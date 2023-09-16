{-# LANGUAGE BlockArguments      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RecordWildCards     #-}

module SAWScript.Crucible.LLVM.FFI
  ( llvm_ffi_setup
  ) where

import           Control.Monad
import           Control.Monad.Trans
import qualified Data.Map                             as Map
import           Data.Maybe
import           Data.Text                            (Text)
import qualified Data.Text                            as Text

import qualified Text.LLVM.AST                        as LLVM

import           Cryptol.Eval.Type
import           Cryptol.TypeCheck.FFI.FFIType
import           Cryptol.TypeCheck.Type

import           SAWScript.Builtins
import           SAWScript.Crucible.Common.MethodSpec
import           SAWScript.Crucible.LLVM.Builtins
import           SAWScript.Crucible.LLVM.MethodSpecIR
import           SAWScript.LLVMBuiltins
import           SAWScript.Value
import           Verifier.SAW.CryptolEnv
import           Verifier.SAW.OpenTerm
import           Verifier.SAW.Recognizer
import           Verifier.SAW.SharedTerm
import           Verifier.SAW.TypedTerm

-- | Generate a @LLVMSetup@ spec that can be used to verify the given term
-- containing a Cryptol foreign function.
llvm_ffi_setup :: TypedTerm -> LLVMCrucibleSetupM ()
llvm_ffi_setup appTerm = do
  let appTerm' = ttTerm appTerm
      (funTerm, _) = asApplyAll appTerm'
  cryEnv <- lll $ rwCryptol <$> getMergedEnv
  sc <- lll getSharedContext
  case asConstant funTerm of
    Just (ec, funDef)
      | Just FFIFunType {..} <- Map.lookup (ecName ec) (eFFITypes cryEnv) -> do
        when (isNothing funDef) do
          throw "Cannot verify foreign function with no Cryptol implementation"
        case ffiTParams of
          [] -> do
            (argTerms, inArgs) <- unzip <$> zipWithM
              (\i -> setupInArg ("in" <> Text.pack (show i)))
              [0 :: Integer ..]
              ffiArgTypes
            retTerm <- sio $ completeOpenTerm sc $
              applyOpenTermMulti (closedOpenTerm appTerm')
                (map closedOpenTerm argTerms)
            retSetupValue <- sio $ anySetupTerm <$> mkTypedTerm sc retTerm
            setupRet ffiRetType >>= \case
              Nothing -> do
                llvm_execute_func inArgs
                llvm_return retSetupValue
              Just outArg -> do
                llvm_execute_func (inArgs ++ [outArg])
                llvm_points_to True outArg retSetupValue
          _ -> throw "Polymorphic FFI not supported"
    _ -> do
      funTermStr <- lll $ show_term funTerm
      throw $ "Not a Cryptol foreign function: " ++ funTermStr

throw :: String -> LLVMCrucibleSetupM a
throw = throwLLVM' "llvm_ffi_setup"

lll :: TopLevel a -> LLVMCrucibleSetupM a
lll x = LLVMCrucibleSetupM $ lift $ lift x

sio :: IO a -> LLVMCrucibleSetupM a
sio x = LLVMCrucibleSetupM $ liftIO x

setupInArg :: Text -> FFIType -> LLVMCrucibleSetupM (Term, AllLLVM SetupValue)
setupInArg name ffiType =
  case ffiType of
    FFIBool -> throw "Bit not supported"
    FFIBasic ffiBasicType -> do
      llvmType <- convertBasicType ffiBasicType
      x <- llvm_fresh_var name llvmType
      pure (ttTerm x, anySetupTerm x)
    FFIArray lengths ffiBasicType -> do
      len <- getArrayLen lengths
      llvmType <- convertBasicType ffiBasicType
      let arrType = llvm_array len llvmType
      arr <- llvm_fresh_var name arrType
      ptr <- llvm_alloc_readonly arrType
      llvm_points_to True ptr (anySetupTerm arr)
      pure (ttTerm arr, ptr)
    FFITuple _ -> throw "Tuples not supported"
    FFIRecord _ -> throw "Records not supported"

setupRet :: FFIType -> LLVMCrucibleSetupM (Maybe (AllLLVM SetupValue))
setupRet ffiType =
  case ffiType of
    FFIBool -> throw "Bit not supported"
    FFIBasic _ -> pure Nothing
    FFIArray lengths ffiBasicType -> do
      len <- getArrayLen lengths
      llvmType <- convertBasicType ffiBasicType
      Just <$> llvm_alloc (llvm_array len llvmType)
    FFITuple _ -> throw "Tuples not supported"
    FFIRecord _ -> throw "Records not supported"

getArrayLen :: [Type] -> LLVMCrucibleSetupM Int
getArrayLen [l] = pure $ fromInteger $ finNat' $ evalNumType mempty l
getArrayLen _   = throw "Multidimensional arrays not supported"

convertBasicType :: FFIBasicType -> LLVMCrucibleSetupM LLVM.Type
convertBasicType (FFIBasicVal ffiBasicValType) =
  case ffiBasicValType of
    FFIWord n ffiWordSize
      | n == size -> pure $ llvm_int size
      | otherwise -> throw
        "Only exact machine-sized bitvectors (8, 16, 32, 64 bits) supported"
      where
      size :: Integral a => a
      size =
        case ffiWordSize of
          FFIWord8  -> 8
          FFIWord16 -> 16
          FFIWord32 -> 32
          FFIWord64 -> 64
    FFIFloat _ _ ffiFloatSize -> pure
      case ffiFloatSize of
        FFIFloat32 -> llvm_float
        FFIFloat64 -> llvm_double
convertBasicType (FFIBasicRef _) = throw "GMP types not supported"
