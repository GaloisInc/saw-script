{-# LANGUAGE BlockArguments    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE ViewPatterns      #-}

module SAWScript.Crucible.LLVM.FFI
  ( llvm_ffi_setup
  ) where

import           Control.Monad
import           Control.Monad.Trans
import           Data.Bits                            (finiteBitSize)
import           Data.Foldable
import           Data.List
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
import           Cryptol.TypeCheck.FFI.FFIType
import           Cryptol.TypeCheck.Solver.InfNat
import           Cryptol.TypeCheck.Type
import           Cryptol.Utils.Ident                  as Cry
import           Cryptol.Utils.PP                     (pretty)
import           Cryptol.Utils.RecordMap

import           SAWScript.Builtins
import           SAWScript.Crucible.Common.MethodSpec
import           SAWScript.Crucible.LLVM.Builtins
import           SAWScript.Crucible.LLVM.MethodSpecIR
import           SAWScript.LLVMBuiltins
import           SAWScript.Panic
import           SAWScript.Value
import           Verifier.SAW.CryptolEnv
import           Verifier.SAW.OpenTerm
import           Verifier.SAW.Recognizer
import           Verifier.SAW.SharedTerm
import           Verifier.SAW.TypedTerm

data FFITypeInfo = FFITypeInfo
  { ffiLLVMType     :: LLVM.Type
  , ffiLLVMCoreType :: OpenTerm
  , ffiConv         :: Maybe FFIConv
  }

data FFIConv = FFIConv
  { ffiCryType  :: OpenTerm
  , ffiPrecond  :: OpenTerm {- : ffiLLVMType -} -> LLVMCrucibleSetupM ()
  , ffiToCry    :: OpenTerm {- : ffiLLVMType -} -> OpenTerm {- : ffiCryType -}
  , ffiPostcond :: FFIPostcond
  }

data FFIPostcond
  = FFIPostcondConvToLLVM
      (OpenTerm {- : ffiCryType -} -> OpenTerm {- : FFILLVMType -})
  | FFIPostcondConvToCryEq
      OpenTerm -- : ffiCryType -> ffiCryType -> Bool

-- | Generate a @LLVMSetup@ spec that can be used to verify the given term
-- containing a Cryptol foreign function fully applied to any type arguments.
llvm_ffi_setup :: TypedTerm -> LLVMCrucibleSetupM ()
llvm_ffi_setup TypedTerm { ttTerm = appTerm } = do
  cryEnv <- lll $ rwCryptol <$> getMergedEnv
  sc <- lll getSharedContext
  case asConstant funTerm of
    Just (ec, funDef)
      | Just FFIFunType {..} <- Map.lookup (ecName ec) (eFFITypes cryEnv) -> do
        when (isNothing funDef) do
          throw "Cannot verify foreign function with no Cryptol implementation"
        tenv <- buildTypeEnv ffiTParams tyArgTerms
        sizeArgs <- lio $ traverse (mkSizeArg sc) tyArgTerms
        (argTerms, inArgss) <- unzip <$> zipWithM
          (\i -> setupInArg sc tenv ("in" <> Text.pack (show i)))
          [0 :: Integer ..]
          ffiArgTypes
        let inArgs = concat inArgss
        (outArgs, post) <- setupRet sc tenv ffiRetType
        llvm_execute_func (sizeArgs ++ inArgs ++ outArgs)
        post $ applyOpenTermMulti (closedOpenTerm appTerm) argTerms
    _ ->
      throw "Not a (monomorphic instantiation of a) Cryptol foreign function"

  where

  (funTerm, tyArgTerms) = asApplyAll appTerm

  throw :: String -> LLVMCrucibleSetupM a
  throw msg = do
    funTermStr <- lll $ show_term funTerm
    throwLLVM' "llvm_ffi_setup" $
      "Cannot generate FFI setup for " ++ funTermStr ++ ":\n" ++ msg

  buildTypeEnv :: [TParam] -> [Term] -> LLVMCrucibleSetupM TypeEnv
  buildTypeEnv [] [] = pure mempty
  buildTypeEnv (param:params) (argTerm:argTerms) =
    case asCtorParams argTerm of
      Just (primName -> "Cryptol.TCNum", [], [asNat -> Just n]) ->
        bindTypeVar (TVBound param) (Left (Nat (toInteger n))) <$>
          buildTypeEnv params argTerms
      _ -> do
        argTermStr <- lll $ show_term argTerm
        throw $ "Not a numeric literal type argument: " ++ argTermStr
  buildTypeEnv params [] = throw $
    "Foreign function not fully instantiated;\n"
    ++ "Missing type arguments for: " ++ intercalate ", " (map pretty params)
  buildTypeEnv [] _ = throw "Too many type arguments"

  mkSizeArg :: SharedContext -> Term -> IO (AllLLVM SetupValue)
  mkSizeArg sc tyArgTerm = do
    {- `tyArgTerm : [sizeBitSize]
    => Cryptol.ecNumber tyArgTerm (Vec sizeBitSize Bool)
                        (Cryptol.PLiteralSeqBool (Cryptol.TCNum sizeBitSize))
    -}
    openToSetupTerm sc $
      applyGlobalOpenTerm "Cryptol.ecNumber"
        [ closedOpenTerm tyArgTerm
        , vectorTypeOpenTerm sizeBitSize boolTypeOpenTerm
        , applyGlobalOpenTerm "Cryptol.PLiteralSeqBool"
            [ctorOpenTerm "Cryptol.TCNum" [sizeBitSize]]
        ]
    where
    sizeBitSize = natOpenTerm $
      fromIntegral $ finiteBitSize (undefined :: CSize)

  setupInArg :: SharedContext -> TypeEnv -> Text -> FFIType ->
    LLVMCrucibleSetupM (OpenTerm, [AllLLVM SetupValue])
  setupInArg sc tenv = go
    where
    go name ffiType =
      case ffiType of
        FFIBool ->
          valueInArg (boolTypeInfo sc)
        FFIBasic ffiBasicType ->
          valueInArg =<< basicTypeInfo sc ffiBasicType
        FFIArray lengths ffiBasicType -> do
          FFITypeInfo {..} <- arrayTypeInfo sc tenv lengths ffiBasicType
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

  setupRet :: SharedContext -> TypeEnv -> FFIType ->
    LLVMCrucibleSetupM ([AllLLVM SetupValue], OpenTerm -> LLVMCrucibleSetupM ())
  setupRet sc tenv ffiType =
    case ffiType of
      FFIBool               -> pure $ retValue (boolTypeInfo sc)
      FFIBasic ffiBasicType -> retValue <$> basicTypeInfo sc ffiBasicType
      _                     -> setupOutArg sc tenv ffiType
    where
    retValue FFITypeInfo {..} =
      let post cryRet =
            case doFFIPostcond sc ffiConv of
              Left toLLVM ->
                llvm_return =<< toLLVM cryRet
              Right cryEq -> do
                llvmRet <- llvm_fresh_var "ret" ffiLLVMType
                llvm_return (anySetupTerm llvmRet)
                cryEq llvmRet cryRet
      in  ([], post)

  setupOutArg :: SharedContext -> TypeEnv -> FFIType ->
    LLVMCrucibleSetupM ([AllLLVM SetupValue], OpenTerm -> LLVMCrucibleSetupM ())
  setupOutArg sc tenv = go "out"
    where
    go name ffiType =
      case ffiType of
        FFIBool ->
          singleOutArg $ boolTypeInfo sc
        FFIBasic ffiBasicType ->
          singleOutArg =<< basicTypeInfo sc ffiBasicType
        FFIArray lengths ffiBasicType ->
          singleOutArg =<< arrayTypeInfo sc tenv lengths ffiBasicType
        FFITuple ffiTypes -> do
          (outArgss, posts) <- unzip <$> setupTupleArgs go name ffiTypes
          let len = fromIntegral $ length ffiTypes
              post ret = zipWithM_
                (\i p -> p (projTupleOpenTerm' i len ret))
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
                  p (projTupleOpenTerm' ix len ret))
                (displayOrder ffiTypeMap)
                posts
          pure (concat outArgss, post)
      where
      singleOutArg FFITypeInfo {..} = do
        ptr <- llvm_alloc ffiLLVMType
        let post cryRet =
              case doFFIPostcond sc ffiConv of
                Left toLLVM ->
                  llvm_points_to True ptr =<< toLLVM cryRet
                Right cryEq -> do
                  out <- llvm_fresh_var name ffiLLVMType
                  llvm_points_to True ptr (anySetupTerm out)
                  cryEq out cryRet
        pure ([ptr], post)

  setupTupleArgs :: (Text -> FFIType -> LLVMCrucibleSetupM a) ->
    Text -> [FFIType] -> LLVMCrucibleSetupM [a]
  setupTupleArgs setup name =
    zipWithM (\i -> setup (name <> "." <> Text.pack (show i))) [0 :: Integer ..]

  setupRecordArgs :: (Text -> FFIType -> LLVMCrucibleSetupM a) ->
    Text -> RecordMap Cry.Ident FFIType -> LLVMCrucibleSetupM [a]
  setupRecordArgs setup name ffiTypeMap =
    traverse
      (\(field, ty) -> setup (name <> "." <> identText field) ty)
      (displayFields ffiTypeMap)

  arrayTypeInfo :: SharedContext -> TypeEnv -> [Type] -> FFIBasicType ->
    LLVMCrucibleSetupM FFITypeInfo
  arrayTypeInfo sc tenv lenTypes ffiBasicType = do
    let lens :: Integral a => [a]
        lens = map (fromInteger . finNat' . evalNumType tenv) lenTypes
        lenTerms = map natOpenTerm lens
        totalLen :: Integral a => a
        totalLen = product lens
        totalLenTerm = natOpenTerm $ fromInteger totalLen
    FFITypeInfo {..} <- basicTypeInfo sc ffiBasicType
    pure FFITypeInfo
      { ffiLLVMType = llvm_array totalLen ffiLLVMType
      , ffiLLVMCoreType = vectorTypeOpenTerm totalLenTerm ffiLLVMCoreType
      , ffiConv =
          case (lenTerms, ffiConv) of
            ([_], Nothing) -> Nothing
            _ -> do
              let basicCryType = maybe ffiLLVMCoreType ffiCryType ffiConv
                  basicPostcond =
                    maybe (FFIPostcondConvToLLVM id) ffiPostcond ffiConv
                  cumulLenTerms = map natOpenTerm $ scanl1 (*) lens
                  arrCryType :| cumulElemTypes =
                    NE.scanr vectorTypeOpenTerm basicCryType lenTerms
                  cumul = zip3
                    cumulLenTerms (tail lenTerms) (tail cumulElemTypes)
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
                , ffiPostcond =
                    case basicPostcond of
                      FFIPostcondConvToLLVM toLLVM ->
                        FFIPostcondConvToLLVM \cryArr ->
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
                      FFIPostcondConvToCryEq cryEq ->
                        FFIPostcondConvToCryEq $
                          {- if lens = [x, y, z]
                             vecEq x (Vec y (Vec z ffiCryType))
                                   (vecEq y (Vec z ffiCryType)
                                          (vecEq z ffiCryType cryEq)) -}
                          foldr
                            (\(len, elemType) eq ->
                              applyGlobalOpenTerm "Prelude.vecEq"
                                [len, elemType, eq])
                            cryEq
                            (zip lenTerms cumulElemTypes)
                }
      }

  basicTypeInfo :: SharedContext -> FFIBasicType ->
    LLVMCrucibleSetupM FFITypeInfo
  basicTypeInfo sc (FFIBasicVal ffiBasicValType) = pure
    case ffiBasicValType of
      FFIWord (fromInteger -> n) ffiWordSize ->
        FFITypeInfo
          { ffiLLVMType = llvm_int llvmSize
          , ffiLLVMCoreType = bvTypeOpenTerm (llvmSize :: Natural)
          , ffiConv = do
              guard (n < llvmSize)
              Just FFIConv
                { ffiCryType = bvTypeOpenTerm n
                , ffiPrecond = precondBVZeroPrefix sc llvmSize (llvmSize - n)
                , ffiToCry = \x {- : Vec llvmSize Bool -} -> -- : Vec n Bool
                    {- drop (llvmSize - n) x
                    => Prelude.bvTrunc (llvmSize - n) n x -}
                    applyGlobalOpenTerm "Prelude.bvTrunc"
                      [natOpenTerm (llvmSize - n), natOpenTerm n, x]
                , ffiPostcond = FFIPostcondConvToCryEq $
                    -- Prelude.bvEq n
                    applyGlobalOpenTerm "Prelude.bvEq" [natOpenTerm n]
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
  basicTypeInfo _ (FFIBasicRef _) =
    throw "GMP types (Integer, Z) not supported"

boolTypeInfo :: SharedContext -> FFITypeInfo
boolTypeInfo sc =
  FFITypeInfo
    { ffiLLVMType = llvm_int 8
    , ffiLLVMCoreType = bvTypeOpenTerm (8 :: Natural)
    , ffiConv =
        Just FFIConv
          { ffiCryType = boolTypeOpenTerm
          , ffiPrecond = precondBVZeroPrefix sc 8 7
          , ffiToCry = \x {- : Vec 8 Bool -} -> -- : Bool
              {- x != zero
              => bvNonzero 8 x -}
              applyGlobalOpenTerm "Prelude.bvNonzero" [natOpenTerm 8, x]
          , ffiPostcond = FFIPostcondConvToCryEq $
              -- Prelude.boolEq
              globalOpenTerm "Prelude.boolEq"
          }
    }

precondBVZeroPrefix :: SharedContext ->
  Natural {- totalLen -} -> Natural ->
  OpenTerm {- Vec totalLen Bool -} -> LLVMCrucibleSetupM ()
precondBVZeroPrefix sc totalLen zeroLen x = do
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
  llvm_precond =<< lio (openToTypedTerm sc precond)

doFFIPostcond :: SharedContext -> Maybe FFIConv ->
  Either
    (OpenTerm {- ffiCryType -} -> LLVMCrucibleSetupM (AllLLVM SetupValue))
    (TypedTerm {- ffiLLVMType -} ->
     OpenTerm {- ffiCryType -} ->
     LLVMCrucibleSetupM ())
doFFIPostcond sc conv =
  case conv of
    Just FFIConv {..} ->
      case ffiPostcond of
        FFIPostcondConvToCryEq cryEq ->
          Right \llvmTerm cryTerm -> do
            -- ffiToCry llvmTerm == cryTerm
            eqTerm <- lio $ openToTypedTerm sc $
              applyOpenTermMulti cryEq
                [ffiToCry (typedToOpenTerm llvmTerm), cryTerm]
            llvm_postcond eqTerm
        FFIPostcondConvToLLVM toLLVM -> toLLVMWith toLLVM
    Nothing -> toLLVMWith id
  where
  toLLVMWith toLLVM = Left (lio . openToSetupTerm sc . toLLVM)

openToTypedTerm :: SharedContext -> OpenTerm -> IO TypedTerm
openToTypedTerm sc openTerm = mkTypedTerm sc =<< completeOpenTerm sc openTerm

openToSetupTerm :: SharedContext -> OpenTerm -> IO (AllLLVM SetupValue)
openToSetupTerm sc openTerm = anySetupTerm <$> openToTypedTerm sc openTerm

typedToOpenTerm :: TypedTerm -> OpenTerm
typedToOpenTerm = closedOpenTerm . ttTerm

lll :: TopLevel a -> LLVMCrucibleSetupM a
lll x = LLVMCrucibleSetupM $ lift $ lift x

lio :: IO a -> LLVMCrucibleSetupM a
lio x = LLVMCrucibleSetupM $ liftIO x
