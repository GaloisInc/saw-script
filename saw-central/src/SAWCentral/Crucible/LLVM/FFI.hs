{-# LANGUAGE BlockArguments    #-}
{-# LANGUAGE ConstraintKinds   #-}
{-# LANGUAGE ImplicitParams    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE ViewPatterns      #-}

-- | Commands for verifying Cryptol foreign functions against their Cryptol
-- implementations.
--
-- Since the Cryptol FFI specifies the exact way that foreign function
-- implementations are called
-- (https://galoisinc.github.io/cryptol/master/FFI.html), we can automatically
-- generate the necessary LLVM setup script for verifying Cryptol foreign
-- functions which also have Cryptol reference implementations. However, often
-- the foreign (LLVM) representation of Cryptol data types as specified by the
-- FFI is different from the representation that SAW directly maps the Cryptol
-- type to (e.g. bitvectors are widened to machine-size integers, and
-- multidimensional arrays are flattened). Therefore, if we were writing the
-- setup spec by hand, we would use some Cryptol built in functions to do the
-- appropriate conversions. Here, we use the SAW Core built in functions (which
-- the Cryptol builtins are converted to) directly for these operations.
--
-- In order for SAW to match overrides with the resulting LLVM spec, we always
-- create symbolic variables in the LLVM representation and pass them directly
-- as arguments to the LLVM function, while asserting the necessary
-- preconditions and doing the appropriate conversions to pass the Cryptol
-- version of the variables to Cryptol. If the mapping from Cryptol to LLVM
-- representation is not surjective, then preconditions are necessary to assert
-- that the LLVM input variables start in a state that is in the image of such
-- mapping (a fact which the LLVM implementation of the function may depend on).
-- Similarly, for function outputs where the mapping from Cryptol to LLVM
-- representation is not unique, we cannot directly verify functional
-- correctness by using @llvm_return@ (for LLVM return values) or
-- @llvm_points_to@ (for LLVM output arguments) on the Cryptol function output
-- converted to LLVM representation. Instead, we must create a fresh symbolic
-- variable representing the LLVM output, then convert that to Cryptol
-- representation and compare it with the Cryptol result.
module SAWCentral.Crucible.LLVM.FFI
  ( llvm_ffi_setup
  ) where

import           Control.Monad
import           Control.Monad.Trans
import           Data.Bits                            (finiteBitSize)
import           Data.Foldable
import           Data.Functor                         ((<&>))
import           Data.List                            (elemIndex, intercalate)
import           Data.List.NonEmpty                   (NonEmpty (..))
import qualified Data.List.NonEmpty                   as NE
import qualified Data.Map                             as Map
import           Data.Maybe
import           Data.Text                            (Text)
import qualified Data.Text                            as Text
import           Foreign.C.Types                      (CSize)
import           Numeric.Natural

import qualified Text.LLVM.AST                        as LLVM

import           Cryptol.Eval.Type
import           Cryptol.TypeCheck.AST                (FFI(..))
import           Cryptol.TypeCheck.FFI.FFIType
import           Cryptol.TypeCheck.Solver.InfNat
import qualified Cryptol.TypeCheck.Type               as Cry
import           Cryptol.Utils.Ident                  as Cry
import           Cryptol.Utils.PP                     (pretty)
import           Cryptol.Utils.RecordMap

import           SAWCentral.Crucible.Common.MethodSpec
import           SAWCentral.Crucible.LLVM.Builtins
import           SAWCentral.Crucible.LLVM.MethodSpecIR
import           SAWCentral.LLVMBuiltins
import           SAWCentral.Panic
import           SAWCentral.Value
import           CryptolSAWCore.CryptolEnv
import           SAWCore.Module (Def(..), ResolvedName(..), lookupVarIndexInMap)
import           SAWCore.Name (Name(..))
import           SAWCore.OpenTerm
import           SAWCore.Prelude
import           SAWCore.Recognizer
import           SAWCore.SharedTerm as Term
import           SAWCore.Term.Pretty (showTerm)
import           CryptolSAWCore.TypedTerm

-- | Commonly used things that need to be passed around.
data FFISetupCtx = FFISetupCtx
  { sc      :: SharedContext
  , funTerm :: Term
  }

type Ctx = (?ctx :: FFISetupCtx)

-- | Information about a Cryptol 'FFIType' that tells us how to generate a setup
-- spec for values of that type.
data FFITypeInfo = FFITypeInfo
  { -- | The representation of the type when passed to the foreign (LLVM)
    -- function.
    ffiLLVMType     :: LLVM.Type
    -- | The same as 'ffiLLVMType' but as a SAWCore term.
  , ffiLLVMCoreType :: OpenTerm
    -- | If 'Nothing' then the Cryptol and foreign representations are the same
    -- and there is no need to convert.
  , ffiConv         :: Maybe FFIConv
  }

-- | How to convert between the Cryptol and foreign representations of an
-- 'FFIType'.
data FFIConv = FFIConv
  { -- | The representation of the type when passed to the Cryptol function.
    ffiCryType :: OpenTerm
    -- | Assert any preconditions guaranteed by the Cryptol FFI on the LLVM
    -- representation.
  , ffiPrecond :: OpenTerm {- : ffiLLVMType -} -> LLVMCrucibleSetupM ()
    -- | Convert from the foreign representation to the Cryptol representation.
  , ffiToCry :: OpenTerm {- : ffiLLVMType -} -> OpenTerm {- : ffiCryType -}
    -- | Convert from the Cryptol representation to the foreign representation.
    -- This is only defined when this conversion is unique, that is, when the
    -- Cryptol and LLVM representations are isomorphic and this function is the
    -- inverse of 'ffiToCry'.
  , ffiToLLVM :: Maybe
      (OpenTerm {- : ffiCryType -} -> OpenTerm {- : FFILLVMType -})
  }

-- | How to check functional correctness of an 'FFIType' result.
data FFIPostcond
  -- | Convert the Cryptol result to the LLVM representation using the given
  -- function, for use with @llvm_return@ or @llvm_points_to@.
  = FFIPostcondConvToLLVM
      (OpenTerm {- : ffiCryType -} -> LLVMCrucibleSetupM (AllLLVM SetupValue))
  -- | Given the LLVM result and the Cryptol result, convert the LLVM result to
  -- the Cryptol representation then assert as a postcondition that they are
  -- equal.
  | FFIPostcondConvToCryEq
      (TypedTerm {- ffiLLVMType -} -> OpenTerm {- ffiCryType -} ->
        LLVMCrucibleSetupM ())

-- | Generate a @LLVMSetup@ spec that can be used to verify that the given
-- monomorphic Cryptol term, consisting of a Cryptol foreign function fully
-- applied to any type arguments, has a correct foreign (LLVM) implementation
-- with respect to its Cryptol implementation.
llvm_ffi_setup :: TypedTerm -> LLVMCrucibleSetupM ()
llvm_ffi_setup TypedTerm { ttTerm = appTerm } = do
  let (funTerm, tyArgTerms) = asApplyAll appTerm
  sc <- lll getSharedContext
  let ?ctx = FFISetupCtx {..}
  cryEnv <- lll getCryptolEnv
  case asConstant funTerm of
    Just nm -> case Map.lookup (nameInfo nm) (eFFITypes cryEnv) of
      Nothing ->
        throwFFISetup $ "No Cryptol foreign function " ++ show nm ++ " found"
      Just (CallC (FFIFunType {..})) -> do
        mm <- lio $ scGetModuleMap sc
        let funDef =
              case lookupVarIndexInMap (nameIndex nm) mm of
                Just (ResolvedDef d) -> defBody d
                _ -> Nothing
        when (isNothing funDef) do
          throwFFISetup
            "Cannot verify foreign function with no Cryptol implementation"
        tenv <- buildTypeEnv ffiTParams tyArgTerms
        llvmSizeArgs <- lio $ traverse mkSizeArg tyArgTerms
        (cryArgs, concat -> llvmInArgs) <- unzip <$> zipWithM
          (\i -> setupInArg tenv ("in" <> Text.pack (show i)))
          [0 :: Integer ..]
          ffiArgTypes
        (llvmOutArgs, post) <- setupRet tenv ffiRetType
        llvm_execute_func (llvmSizeArgs ++ llvmInArgs ++ llvmOutArgs)
        post $ applyOpenTermMulti (closedOpenTerm appTerm) cryArgs
      Just (CallAbstract (FFIFunType{})) ->
        -- CallAbstract uses ordinary Cryptol types instead of FFIType,
        -- and while the logic above might be generalized to support that
        -- it'll take work. FUTURE
        throwFFISetup $ "Foreign functions using the 'abstract' calling" <>
                        " convention are not supported yet"
    _ ->
      throwFFISetup
        "Not a (monomorphic instantiation of a) Cryptol foreign function"

-- | Report an error in generating setup for a foreign function.
throwFFISetup :: Ctx => String -> LLVMCrucibleSetupM a
throwFFISetup msg =
  throwLLVMFun "llvm_ffi_setup" $
    "Cannot generate FFI setup for " ++ showTerm (funTerm ?ctx) ++ ":\n" ++ msg

-- | Given a list of type parameters and their actual values as terms, create a
-- type environment binding them.
buildTypeEnv :: Ctx => [Cry.TParam] -> [Term] -> LLVMCrucibleSetupM TypeEnv
buildTypeEnv [] [] = pure mempty
buildTypeEnv (param:params) (argTerm:argTerms) =
  case asGlobalApply "Cryptol.TCNum" argTerm of
    Just [asNat -> Just n] ->
      bindTypeVar (Cry.TVBound param) (Left (Nat (toInteger n))) <$>
        buildTypeEnv params argTerms
    _ ->
      throwFFISetup $
        "Not a numeric literal type argument: " ++ showTerm argTerm
buildTypeEnv params [] = throwFFISetup $
  "Foreign function not fully instantiated;\n"
  ++ "Missing type arguments for: " ++ intercalate ", " (map pretty params)
buildTypeEnv [] _ = throwFFISetup "Too many (type) arguments"

-- | Given a Cryptol type argument as a term, return the corresponding size_t
-- LLVM argument.
mkSizeArg :: Ctx => Term -> IO (AllLLVM SetupValue)
mkSizeArg tyArgTerm = do
  {- `tyArgTerm : [sizeBitSize]
  => Cryptol.ecNumber tyArgTerm (Vec sizeBitSize Bool)
                      (Cryptol.PLiteralSeqBool (Cryptol.TCNum sizeBitSize))
  -}
  openToSetupTerm $
    applyGlobalOpenTerm "Cryptol.ecNumber"
      [ closedOpenTerm tyArgTerm
      , vectorTypeOpenTerm sizeBitSize boolTypeOpenTerm
      , applyGlobalOpenTerm "Cryptol.PLiteralSeqBool"
          [ctorOpenTerm "Cryptol.TCNum" [sizeBitSize]]
      ]
  where
  sizeBitSize = natOpenTerm $
    fromIntegral $ finiteBitSize (undefined :: CSize)

-- | Do setup for an input argument, returning the term to pass to the Cryptol
-- function and a list of arguments to pass to the LLVM function.
setupInArg :: Ctx => TypeEnv -> Text -> FFIType ->
  LLVMCrucibleSetupM (OpenTerm, [AllLLVM SetupValue])
setupInArg tenv = go
  where
  go name ffiType =
    case ffiType of
      FFIBool ->
        valueInArg boolTypeInfo
      FFIBasic ffiBasicType ->
        valueInArg =<< basicTypeInfo ffiBasicType
      FFIArray lengths ffiBasicType -> do
        FFITypeInfo {..} <- arrayTypeInfo tenv lengths ffiBasicType
        (arr, cryTerm) <- singleInArg FFITypeInfo {..}
        ptr <- llvm_alloc_readonly ffiLLVMType
        llvm_points_to True ptr (anySetupTerm arr)
        pure (cryTerm, [ptr])
      FFITuple ffiTypes ->
        tupleInArgs <$> setupTupleArgs go name ffiTypes
      FFIRecord ffiTypeMap ->
        tupleInArgs <$> setupRecordArgs go name ffiTypeMap
    where
    valueInArg ffiTypeInfo = do
      (x, cryTerm) <- singleInArg ffiTypeInfo
      pure (cryTerm, [anySetupTerm x])
    singleInArg FFITypeInfo {..} = do
      x <- llvm_fresh_var name ffiLLVMType
      let ox = typedToOpenTerm x
      cryTerm <-
        case ffiConv of
          Just FFIConv {..} -> do
            ffiPrecond ox
            pure $ ffiToCry ox
          Nothing -> pure ox
      pure (x, cryTerm)
    tupleInArgs (unzip -> (terms, inArgss)) =
      (tupleOpenTerm' terms, concat inArgss)

-- | Do setup for the return value, returning a list of output arguments to pass
-- to the LLVM function and a function that asserts functional correctness given
-- the Cryptol result.
setupRet :: Ctx => TypeEnv -> FFIType ->
  LLVMCrucibleSetupM ([AllLLVM SetupValue], OpenTerm -> LLVMCrucibleSetupM ())
setupRet tenv ffiType =
  case ffiType of
    FFIBool               -> pure $ retValue boolTypeInfo
    FFIBasic ffiBasicType -> retValue <$> basicTypeInfo ffiBasicType
    _                     -> setupOutArg tenv ffiType
  where
  retValue FFITypeInfo {..} =
    let post cryRet =
          case getFFIPostcond ffiConv of
            FFIPostcondConvToLLVM toLLVM ->
              llvm_return =<< toLLVM cryRet
            FFIPostcondConvToCryEq cryEq -> do
              llvmRet <- llvm_fresh_var "ret" ffiLLVMType
              llvm_return (anySetupTerm llvmRet)
              cryEq llvmRet cryRet
    in  ([], post)

-- | Do setup for a return value passed as output arguments to the LLVM
-- function, returning a list of output arguments to pass to the LLVM function
-- and a function that asserts functional correctness given the Cryptol
-- result.
setupOutArg :: Ctx => TypeEnv -> FFIType ->
  LLVMCrucibleSetupM ([AllLLVM SetupValue], OpenTerm -> LLVMCrucibleSetupM ())
setupOutArg tenv = go "out"
  where
  go name ffiType =
    case ffiType of
      FFIBool ->
        singleOutArg boolTypeInfo
      FFIBasic ffiBasicType ->
        singleOutArg =<< basicTypeInfo ffiBasicType
      FFIArray lengths ffiBasicType ->
        singleOutArg =<< arrayTypeInfo tenv lengths ffiBasicType
      FFITuple ffiTypes -> do
        (outArgss, posts) <- unzip <$> setupTupleArgs go name ffiTypes
        let len = fromIntegral $ length ffiTypes
            post ret = zipWithM_
              (\i p -> p (projTupleOpenTerm' len i ret))
              [0..]
              posts
        pure (concat outArgss, post)
      FFIRecord ffiTypeMap -> do
        -- The FFI passes record elements by display order, while SAW
        -- represents records by tuples in canonical order
        (outArgss, posts) <- unzip <$> setupRecordArgs go name ffiTypeMap
        let canonFields = map fst $ canonicalFields ffiTypeMap
            len = fromIntegral $ length canonFields
            post ret = zipWithM_
              (\field p -> do
                let ix = fromIntegral
                      case elemIndex field canonFields of
                        Just i -> i
                        Nothing -> panic "setupOutArg"
                          ["Bad record field access"]
                p (projTupleOpenTerm' len ix ret))
              (displayOrder ffiTypeMap)
              posts
        pure (concat outArgss, post)
    where
    singleOutArg FFITypeInfo {..} = do
      ptr <- llvm_alloc ffiLLVMType
      let post cryRet =
            case getFFIPostcond ffiConv of
              FFIPostcondConvToLLVM toLLVM ->
                llvm_points_to True ptr =<< toLLVM cryRet
              FFIPostcondConvToCryEq cryEq -> do
                out <- llvm_fresh_var name ffiLLVMType
                llvm_points_to True ptr (anySetupTerm out)
                cryEq out cryRet
      pure ([ptr], post)

-- | Given an 'FFIConv', return a way to assert functional correctness,
-- preferring 'FFIPostcondConvToLLVM' when possible. If no 'FFIConv', then
-- return a trivial conversion to LLVM.
getFFIPostcond :: Ctx => Maybe FFIConv -> FFIPostcond
getFFIPostcond conv =
  case conv of
    Just FFIConv {..} ->
      case ffiToLLVM of
        Just toLLVM -> toLLVMWith toLLVM
        Nothing ->
          FFIPostcondConvToCryEq \llvmTerm cryTerm -> do
            -- ffiToCry llvmTerm == cryTerm
            lhs <- lio $ completeOpenTerm sc $
              ffiToCry $ typedToOpenTerm llvmTerm
            rhs <- lio $ completeOpenTerm sc cryTerm
            eqTerm <- lio $ mkTypedTerm sc =<< scEq sc lhs rhs
            llvm_postcond eqTerm
    Nothing -> toLLVMWith id
  where
  FFISetupCtx {..} = ?ctx
  toLLVMWith toLLVM = FFIPostcondConvToLLVM (lio . openToSetupTerm . toLLVM)

-- | Call the given setup function on subparts of the tuple, naming them by
-- index.
setupTupleArgs :: (Text -> FFIType -> LLVMCrucibleSetupM a) ->
  Text -> [FFIType] -> LLVMCrucibleSetupM [a]
setupTupleArgs setup name =
  zipWithM (\i -> setup (name <> "." <> Text.pack (show i))) [0 :: Integer ..]

-- | Call the given setup function on subparts of the record, naming them by
-- field name.
setupRecordArgs :: (Text -> FFIType -> LLVMCrucibleSetupM a) ->
  Text -> RecordMap Cry.Ident FFIType -> LLVMCrucibleSetupM [a]
setupRecordArgs setup name ffiTypeMap =
  traverse
    (\(field, ty) -> setup (name <> "." <> identText field) ty)
    (displayFields ffiTypeMap)

-- | Type info for 'FFIBool'.
boolTypeInfo :: Ctx => FFITypeInfo
boolTypeInfo =
  FFITypeInfo
    { ffiLLVMType = llvm_int 8
    , ffiLLVMCoreType = bvTypeOpenTerm (8 :: Natural)
    , ffiConv =
        Just FFIConv
          { ffiCryType = boolTypeOpenTerm
          , ffiPrecond = precondBVZeroPrefix 8 7
          , ffiToCry = \x {- : Vec 8 Bool -} -> -- : Bool
              {- x != zero
              => bvNonzero 8 x -}
              applyGlobalOpenTerm "Prelude.bvNonzero" [natOpenTerm 8, x]
          , ffiToLLVM = Nothing
          }
    }

-- | Type info for a 'FFIBasicType'.
basicTypeInfo :: Ctx => FFIBasicType -> LLVMCrucibleSetupM FFITypeInfo
basicTypeInfo (FFIBasicVal ffiBasicValType) = pure
  case ffiBasicValType of
    FFIWord (fromInteger -> n) ffiWordSize ->
      FFITypeInfo
        { ffiLLVMType = llvm_int llvmSize
        , ffiLLVMCoreType = bvTypeOpenTerm (llvmSize :: Natural)
        , ffiConv = do
            -- No need for conversion if the word size exactly matches a
            -- machine word size.
            guard (n < llvmSize)
            Just FFIConv
              { ffiCryType = bvTypeOpenTerm n
              , ffiPrecond =
                  precondBVZeroPrefix llvmSize (llvmSize - n)
              , ffiToCry = \x {- : Vec llvmSize Bool -} -> -- : Vec n Bool
                  {- drop (llvmSize - n) x
                  => Prelude.bvTrunc (llvmSize - n) n x -}
                  applyGlobalOpenTerm "Prelude.bvTrunc"
                    [natOpenTerm (llvmSize - n), natOpenTerm n, x]
              , ffiToLLVM = Nothing
              }
        }
      where
      llvmSize :: Integral a => a
      llvmSize =
        case ffiWordSize of
          FFIWord8  -> 8
          FFIWord16 -> 16
          FFIWord32 -> 32
          FFIWord64 -> 64
    FFIFloat _ _ ffiFloatSize ->
      let (ffiLLVMType, ffiLLVMCoreType) =
            case ffiFloatSize of
              FFIFloat32 -> (llvm_float, globalOpenTerm "Prelude.Float")
              FFIFloat64 -> (llvm_double, globalOpenTerm "Prelude.Double")
      in  FFITypeInfo
            { ffiConv = Nothing
            , .. }
basicTypeInfo (FFIBasicRef _) =
  throwFFISetup "GMP types (Integer, Rational, Z) not supported"

-- | Assert the precondition that a prefix of the given bitvector is zero.
precondBVZeroPrefix :: Ctx =>
  Natural {- totalLen -} -> Natural ->
  OpenTerm {- Vec totalLen Bool -} -> LLVMCrucibleSetupM ()
precondBVZeroPrefix totalLen zeroLen x = do
  let zeroLenTerm = natOpenTerm zeroLen
      precond =
        {- take zeroLen x == zero
        => Prelude.bvEq zeroLen
                        (take Bool zeroLen (totalLen - zeroLen) x)
                        (bvNat zeroLen 0) -}
        applyGlobalOpenTerm "Prelude.bvEq"
          [ zeroLenTerm
          , applyGlobalOpenTerm "Prelude.take"
              [ boolTypeOpenTerm
              , zeroLenTerm
              , natOpenTerm (totalLen - zeroLen)
              , x
              ]
          , applyGlobalOpenTerm "Prelude.bvNat"
              [zeroLenTerm, natOpenTerm 0]
          ]
  llvm_precond =<< lio (openToTypedTerm precond)

-- | Type info for the 'FFIArray' type.
arrayTypeInfo :: Ctx => TypeEnv -> [Cry.Type] -> FFIBasicType ->
  LLVMCrucibleSetupM FFITypeInfo
arrayTypeInfo tenv lenTypes ffiBasicType = do
  let lens :: Integral a => [a]
      lens = map (fromInteger . finNat' . evalNumType tenv) lenTypes
      lenTerms = map natOpenTerm lens
      totalLen :: Integral a => a
      totalLen = product lens
      totalLenTerm = natOpenTerm $ fromInteger totalLen
  FFITypeInfo {..} <- basicTypeInfo ffiBasicType
  pure FFITypeInfo
    { ffiLLVMType = llvm_array totalLen ffiLLVMType
    , ffiLLVMCoreType = vectorTypeOpenTerm totalLenTerm ffiLLVMCoreType
    , ffiConv =
        case (lenTerms, ffiConv) of
          -- If the array is flat and there is no need to convert individual
          -- elements, then there is no need to convert the array
          ([_], Nothing) -> Nothing
          _ -> do
            let basicCryType = maybe ffiLLVMCoreType ffiCryType ffiConv
                basicToLLVM = maybe (Just id) ffiToLLVM ffiConv
                cumulLenTerms = map natOpenTerm $ scanl1 (*) lens
                arrCryType :| cumulElemTypes =
                  NE.scanr vectorTypeOpenTerm basicCryType lenTerms

                noArrayLengths :: a
                noArrayLengths =
                  panic "arrayTypeInfo"
                        ["FFIArray with empty list of length types"]

                lenTermsTail =
                  case lenTerms of
                    _:lenTermsTail' -> lenTermsTail'
                    [] -> noArrayLengths
                cumulElemTypesTail =
                  case cumulElemTypes of
                    _:cumulElemTypesTail' -> cumulElemTypesTail'
                    [] -> noArrayLengths

                -- Note that the length of cumulLenTerms will always be one
                -- greater than the lengths of the other two lists, which means
                -- that zip3 will drop the last element of cumulLenTerms. This
                -- is fine, as `cumul` is used in such a way where the last
                -- element is never required. (See the comments next to the uses
                -- of `cumul` below.)
                cumul = zip3 cumulLenTerms lenTermsTail cumulElemTypesTail
            Just FFIConv
              { ffiCryType = arrCryType
              , ffiPrecond = \arr {- : Vec totalLen ffiLLVMCoreType -} ->
                  for_ ffiConv \FFIConv {..} ->
                    for_ [0 .. totalLen - 1] \i -> do
                      {- arr @ i
                      => Prelude.at len ffiLLVMCoreType arr i -}
                      ffiPrecond $
                        applyGlobalOpenTerm "Prelude.at"
                          [totalLenTerm, ffiLLVMCoreType, arr, natOpenTerm i]
              , ffiToCry = \llvmArr {- : Vec totalLen ffiLLVMCoreType -} ->
                  let flatCryArr =
                        case ffiConv of
                          Just FFIConv {..} ->
                            {- map ffiToCry llvmArr
                            => Prelude.map ffiLLVMCoreType
                                           ffiCryType
                                           (\x -> ffiToCry x)
                                           totalLen
                                           llvmArr -}
                            applyGlobalOpenTerm "Prelude.map"
                              [ ffiLLVMCoreType
                              , ffiCryType
                              , lambdaOpenTerm "x" ffiLLVMCoreType ffiToCry
                              , totalLenTerm
                              , llvmArr
                              ]
                          Nothing ->
                            llvmArr
                  in  {- if lens = [x, y, z]
                          split x y (Vec z ffiCryType)
                                (split (x * y) z ffiCryType flatCryArr) -}
                      foldr
                        (\(cumulLen, dimLen, arrElemType) arr ->
                          applyGlobalOpenTerm "Prelude.split"
                            [cumulLen, dimLen, arrElemType, arr])
                        flatCryArr
                        cumul
              , ffiToLLVM = basicToLLVM <&> \toLLVM cryArr ->
                  -- If the element representations are isomorphic, then the
                  -- array representations are isomorphic as well
                  let flatCryArr =
                        {- if lens = [x, y, z]
                            join (x * y) z ffiCryType
                                 (join x y (Vec z ffiCryType) cryArr) -}
                        foldr
                          (\(cumulLen, dimLen, arrElemType) arr ->
                            applyGlobalOpenTerm "Prelude.join"
                              [cumulLen, dimLen, arrElemType, arr])
                          cryArr
                          (reverse cumul)
                  in  {- map toLLVM flatCryArr
                      => Prelude.map basicCryType
                                     ffiLLVMCoreType
                                     (\x -> toLLVM x)
                                     totalLen
                                     flatCryArr -}
                      applyGlobalOpenTerm "Prelude.map"
                        [ basicCryType
                        , ffiLLVMCoreType
                        , lambdaOpenTerm "x" basicCryType toLLVM
                        , totalLenTerm
                        , flatCryArr
                        ]
              }
    }

-- Utility functions

openToTypedTerm :: Ctx => OpenTerm -> IO TypedTerm
openToTypedTerm openTerm = mkTypedTerm sc =<< completeOpenTerm sc openTerm
  where FFISetupCtx {..} = ?ctx

openToSetupTerm :: Ctx => OpenTerm -> IO (AllLLVM SetupValue)
openToSetupTerm openTerm = anySetupTerm <$> openToTypedTerm openTerm

typedToOpenTerm :: TypedTerm -> OpenTerm
typedToOpenTerm = closedOpenTerm . ttTerm

lll :: TopLevel a -> LLVMCrucibleSetupM a
lll x = LLVMCrucibleSetupM $ lift $ lift x

lio :: IO a -> LLVMCrucibleSetupM a
lio x = LLVMCrucibleSetupM $ liftIO x
