{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PartialTypeSignatures #-}
module SAWServer.LLVMCrucibleSetup
  ( startLLVMCrucibleSetup
  , llvmLoadModule
  , llvmLoadModuleDescr
  , Contract(..)
  , ContractVar(..)
  , Allocated(..)
  , PointsTo(..)
  , compileLLVMContract
  ) where

import Control.Lens
import Control.Monad.IO.Class
import Control.Monad.State
import Data.Aeson (FromJSON(..), withObject, (.:))
import Data.ByteString (ByteString)
import Data.Foldable
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Text as T

import qualified Cryptol.Parser.AST as P
import Cryptol.Utils.Ident (mkIdent)
import qualified Text.LLVM.AST as LLVM
import qualified Data.LLVM.BitCode as LLVM
import SAWScript.Crucible.Common.MethodSpec as MS (SetupValue(..))
import SAWScript.Crucible.LLVM.Builtins
    ( llvm_alloc
    , llvm_alloc_aligned
    , llvm_alloc_readonly
    , llvm_alloc_readonly_aligned
    , llvm_execute_func
    , llvm_fresh_var
    , llvm_points_to
    , llvm_return
    , llvm_precond
    , llvm_postcond )
import qualified SAWScript.Crucible.LLVM.MethodSpecIR as CMS
import SAWScript.Value (BuiltinContext, LLVMCrucibleSetupM(..), biSharedContext)
import qualified Verifier.SAW.CryptolEnv as CEnv
import Verifier.SAW.CryptolEnv (CryptolEnv)
import Verifier.SAW.TypedTerm (TypedTerm)

import Argo
import qualified Argo.Doc as Doc
import SAWServer
import SAWServer.Data.Contract
import SAWServer.Data.LLVMType (JSONLLVMType, llvmType)
import SAWServer.Data.SetupValue ()
import SAWServer.CryptolExpression (getTypedTermOfCExp)
import SAWServer.Exceptions
import SAWServer.OK
import SAWServer.TrackFile

startLLVMCrucibleSetup :: StartLLVMCrucibleSetupParams -> Method SAWState OK
startLLVMCrucibleSetup (StartLLVMCrucibleSetupParams n) =
  do pushTask (LLVMCrucibleSetup n [])
     ok

data StartLLVMCrucibleSetupParams
  = StartLLVMCrucibleSetupParams ServerName

instance FromJSON StartLLVMCrucibleSetupParams where
  parseJSON =
    withObject "params for \"SAW/Crucible setup\"" $ \o ->
    StartLLVMCrucibleSetupParams <$> o .: "name"

data ServerSetupVal = Val (CMS.AllLLVM SetupValue)

-- TODO: this is an extra layer of indirection that could be collapsed, but is easy to implement for now.
compileLLVMContract ::
  (FilePath -> IO ByteString) ->
  BuiltinContext ->
  CryptolEnv ->
  Contract JSONLLVMType (P.Expr P.PName) ->
  LLVMCrucibleSetupM ()
compileLLVMContract fileReader bic cenv c =
  interpretLLVMSetup fileReader bic cenv steps
  where
    setupFresh (ContractVar n dn ty) = SetupFresh n dn (llvmType ty)
    setupAlloc (Allocated n ty mut align) = SetupAlloc n (llvmType ty) mut align
    steps =
      map setupFresh (preVars c) ++
      map SetupPrecond (preConds c) ++
      map setupAlloc (preAllocated c) ++
      map (\(PointsTo p v) -> SetupPointsTo p v) (prePointsTos c) ++
      [ SetupExecuteFunction (argumentVals c) ] ++
      map setupFresh (postVars c) ++
      map SetupPostcond (postConds c) ++
      map setupAlloc (postAllocated c) ++
      map (\(PointsTo p v) -> SetupPointsTo p v) (postPointsTos c) ++
      [ SetupReturn v | v <- maybeToList (returnVal c) ]

interpretLLVMSetup ::
  (FilePath -> IO ByteString) ->
  BuiltinContext ->
  CryptolEnv ->
  [SetupStep LLVM.Type] ->
  LLVMCrucibleSetupM ()
interpretLLVMSetup fileReader bic cenv0 ss =
  runStateT (traverse_ go ss) (mempty, cenv0) *> pure ()
  where
    go (SetupReturn v) = get >>= \env -> lift $ getSetupVal env v >>= llvm_return
    -- TODO: do we really want two names here?
    go (SetupFresh name@(ServerName n) debugName ty) =
      do t <- lift $ llvm_fresh_var (T.unpack debugName) ty
         (env, cenv) <- get
         put (env, CEnv.bindTypedTerm (mkIdent n, t) cenv)
         save name (Val (CMS.anySetupTerm t))
    go (SetupAlloc name ty True Nothing) =
      lift (llvm_alloc ty) >>= save name . Val
    go (SetupAlloc name ty False Nothing) =
      lift (llvm_alloc_readonly ty) >>= save name . Val
    go (SetupAlloc name ty True (Just align)) =
      lift (llvm_alloc_aligned align ty) >>= save name . Val
    go (SetupAlloc name ty False (Just align)) =
      lift (llvm_alloc_readonly_aligned align ty) >>= save name . Val
    go (SetupPointsTo src tgt) = get >>= \env -> lift $
      do ptr <- getSetupVal env src
         tgt' <- getSetupVal env tgt
         llvm_points_to True ptr tgt'
    go (SetupExecuteFunction args) =
      get >>= \env ->
      lift $ traverse (getSetupVal env) args >>= llvm_execute_func
    go (SetupPrecond p) = get >>= \env -> lift $
      getTypedTerm env p >>= llvm_precond
    go (SetupPostcond p) = get >>= \env -> lift $
      getTypedTerm env p >>= llvm_postcond

    save name val = modify' (\(env, cenv) -> (Map.insert name val env, cenv))

    getSetupVal ::
      (Map ServerName ServerSetupVal, CryptolEnv) ->
      CrucibleSetupVal (P.Expr P.PName) ->
      LLVMCrucibleSetupM (CMS.AllLLVM MS.SetupValue)
    getSetupVal _ NullValue = LLVMCrucibleSetupM $ return CMS.anySetupNull
    getSetupVal env (ArrayValue elts) =
      do elts' <- mapM (getSetupVal env) elts
         LLVMCrucibleSetupM $ return $ CMS.anySetupArray elts'
    getSetupVal env (FieldLValue base fld) =
      do base' <- getSetupVal env base
         LLVMCrucibleSetupM $ return $ CMS.anySetupField base' fld
    getSetupVal env (ElementLValue base idx) =
      do base' <- getSetupVal env base
         LLVMCrucibleSetupM $ return $ CMS.anySetupElem base' idx
    getSetupVal _ (GlobalInitializer name) =
      LLVMCrucibleSetupM $ return $ CMS.anySetupGlobalInitializer name
    getSetupVal _ (GlobalLValue name) =
      LLVMCrucibleSetupM $ return $ CMS.anySetupGlobal name
    getSetupVal (env, _) (ServerValue n) = LLVMCrucibleSetupM $
      resolve env n >>=
      \case
        Val x -> return x -- TODO add cases for the server values that
                          -- are not coming from the setup monad
                          -- (e.g. surrounding context)
    getSetupVal (_, cenv) (CryptolExpr expr) = LLVMCrucibleSetupM $
      do res <- liftIO $ getTypedTermOfCExp fileReader (biSharedContext bic) cenv expr
         -- TODO: add warnings (snd res)
         case fst res of
           Right (t, _) -> return (CMS.anySetupTerm t)
           Left err -> error $ "Cryptol error: " ++ show err -- TODO: report properly

    getTypedTerm ::
      (Map ServerName ServerSetupVal, CryptolEnv) ->
      P.Expr P.PName ->
      LLVMCrucibleSetupM TypedTerm
    getTypedTerm (_, cenv) expr = LLVMCrucibleSetupM $
      do res <- liftIO $ getTypedTermOfCExp fileReader (biSharedContext bic) cenv expr
         -- TODO: add warnings (snd res)
         case fst res of
           Right (t, _) -> return t
           Left err -> error $ "Cryptol error: " ++ show err -- TODO: report properly

    resolve env name =
       case Map.lookup name env of
         Just v -> return v
         Nothing -> error "Server value not found - impossible!" -- rule out elsewhere

data LLVMLoadModuleParams
  = LLVMLoadModuleParams ServerName FilePath

instance FromJSON LLVMLoadModuleParams where
  parseJSON =
    withObject "params for \"SAW/LLVM/load module\"" $ \o ->
    LLVMLoadModuleParams <$> o .: "name" <*> o .: "bitcode file"


instance Doc.DescribedParams LLVMLoadModuleParams where
  parameterFieldDescription =
    [ ("name",
        Doc.Paragraph [Doc.Text "The name to refer to the loaded module by later."])
    , ("bitcode file",
       Doc.Paragraph [Doc.Text "The file containing the bitcode LLVM module to load."])
    ]

llvmLoadModuleDescr :: Doc.Block
llvmLoadModuleDescr =
  Doc.Paragraph [Doc.Text "Load the specified LLVM module."]

llvmLoadModule :: LLVMLoadModuleParams -> Method SAWState OK
llvmLoadModule (LLVMLoadModuleParams serverName fileName) =
  do tasks <- view sawTask <$> getState
     case tasks of
       (_:_) -> raise $ notAtTopLevel $ map fst tasks
       [] ->
         do let ?laxArith = False -- TODO read from config
            halloc <- getHandleAlloc
            loaded <- liftIO (CMS.loadLLVMModule fileName halloc)
            case loaded of
              Left err -> raise (cantLoadLLVMModule (LLVM.formatError err))
              Right llvmMod ->
                do setServerVal serverName llvmMod
                   trackFile fileName
                   ok
