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
import           Data.Functor
import           Data.List
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
  { ffiCryType :: OpenTerm
  , ffiPrecond :: OpenTerm {- : ffiLLVMType -} -> LLVMCrucibleSetupM ()
  , ffiToCry   :: OpenTerm -- : ffiLLVMType -> ffiCryType
  , ffiCryEq   :: OpenTerm -- : ffiCryType -> ffiCryType -> Bool
  }

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
          len <- getArrayLen tenv lengths
          FFITypeInfo {..} <- arrayTypeInfo sc len ffiBasicType
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
              pure $ applyOpenTerm ffiToCry ox
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
    retValue FFITypeInfo {..} = ([], post)
      where
      post cryRet =
        case ffiConv of
          Just FFIConv {..} -> do
            llvmRet <- llvm_fresh_var "ret" ffiLLVMType
            llvm_return (anySetupTerm llvmRet)
            -- ffiToCry llvmRet == cryRet
            eqTerm <- lio $ openToTypedTerm sc $
              applyOpenTermMulti ffiCryEq
                [ applyOpenTerm ffiToCry (typedToOpenTerm llvmRet)
                , cryRet
                ]
            llvm_postcond eqTerm
          Nothing ->
            llvm_return =<< lio (openToSetupTerm sc cryRet)

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
        FFIArray lengths ffiBasicType -> do
          len <- getArrayLen tenv lengths
          singleOutArg =<< arrayTypeInfo sc len ffiBasicType
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
        let post ret = do
              case ffiConv of
                Just FFIConv {..} -> do
                  out <- llvm_fresh_var name ffiLLVMType
                  llvm_points_to True ptr (anySetupTerm out)
                  -- ffiToCry out == ret
                  eqTerm <- lio $ openToTypedTerm sc $
                    applyOpenTermMulti ffiCryEq
                      [ applyOpenTerm ffiToCry (typedToOpenTerm out)
                      , ret
                      ]
                  llvm_postcond eqTerm
                Nothing -> do
                  llvm_points_to True ptr =<< lio (openToSetupTerm sc ret)
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

  getArrayLen :: TypeEnv -> [Type] -> LLVMCrucibleSetupM Int
  getArrayLen tenv lengths =
    case lengths of
      [len] -> pure $ fromInteger $ finNat' $ evalNumType tenv len
      _     -> throw "Multidimensional arrays not supported"

  arrayTypeInfo :: SharedContext -> Int -> FFIBasicType ->
    LLVMCrucibleSetupM FFITypeInfo
  arrayTypeInfo sc len ffiBasicType = do
    let lenTerm = natOpenTerm $ fromIntegral len
    FFITypeInfo {..} <- basicTypeInfo sc ffiBasicType
    pure FFITypeInfo
      { ffiLLVMType = llvm_array len ffiLLVMType
      , ffiLLVMCoreType = vectorTypeOpenTerm lenTerm ffiLLVMCoreType
      , ffiConv = ffiConv <&> \FFIConv {..} ->
          FFIConv
            { ffiCryType = vectorTypeOpenTerm lenTerm ffiCryType
            , ffiPrecond = \arr {- : Vec len ffiLLVMCoreType -} -> do
                for_ [0 .. fromIntegral len - 1] \i -> do
                  {- arr @ i
                  => Prelude.at len ffiLLVMCoreType arr i -}
                  ffiPrecond $
                    applyGlobalOpenTerm "Prelude.at"
                      [lenTerm, ffiLLVMCoreType, arr, natOpenTerm i]
            , ffiToCry =
                {- map ffiToCry
                => Prelude.map ffiLLVMCoreType ffiCryType ffiToCry len -}
                applyGlobalOpenTerm "Prelude.map"
                  [ffiLLVMCoreType, ffiCryType, ffiToCry, lenTerm]
            , ffiCryEq =
                -- Prelude.vecEq len ffiCryType ffiCryEq
                applyGlobalOpenTerm "Prelude.vecEq"
                  [lenTerm, ffiCryType, ffiCryEq]
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
                , ffiToCry =
                    {- drop (llvmSize - n)
                    => Prelude.bvTrunc (llvmSize - n) n -}
                    applyGlobalOpenTerm "Prelude.bvTrunc"
                      [natOpenTerm (llvmSize - n), natOpenTerm n]
                , ffiCryEq =
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
          , ffiToCry =
              {- (!= zero)
              => bvNonzero 8 -}
              applyGlobalOpenTerm "Prelude.bvNonzero" [natOpenTerm 8]
          , ffiCryEq =
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
