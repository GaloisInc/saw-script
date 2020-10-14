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
    ( crucible_alloc
    , crucible_alloc_aligned
    , crucible_alloc_readonly
    , crucible_alloc_readonly_aligned
    , crucible_execute_func
    , crucible_fresh_var
    , crucible_points_to
    , crucible_return
    , crucible_precond
    , crucible_postcond )
import qualified SAWScript.Crucible.LLVM.MethodSpecIR as CMS
import SAWScript.Options (defaultOptions)
import SAWScript.Value (BuiltinContext, LLVMCrucibleSetupM(..), biSharedContext)
import qualified Verifier.SAW.CryptolEnv as CEnv
import Verifier.SAW.CryptolEnv (CryptolEnv)
import Verifier.SAW.TypedTerm (TypedTerm)

import Argo
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
    go (SetupReturn v) = get >>= \env -> lift $ getSetupVal env v >>= crucible_return bic defaultOptions
    -- TODO: do we really want two names here?
    go (SetupFresh name@(ServerName n) debugName ty) =
      do t <- lift $ crucible_fresh_var bic defaultOptions (T.unpack debugName) ty
         (env, cenv) <- get
         put (env, CEnv.bindTypedTerm (mkIdent n, t) cenv)
         save name (Val (CMS.anySetupTerm t))
    go (SetupAlloc name ty True Nothing) =
      lift (crucible_alloc bic defaultOptions ty) >>= save name . Val
    go (SetupAlloc name ty False Nothing) =
      lift (crucible_alloc_readonly bic defaultOptions ty) >>= save name . Val
    go (SetupAlloc name ty True (Just align)) =
      lift (crucible_alloc_aligned bic defaultOptions align ty) >>= save name . Val
    go (SetupAlloc name ty False (Just align)) =
      lift (crucible_alloc_readonly_aligned bic defaultOptions align ty) >>= save name . Val
    go (SetupPointsTo src tgt) = get >>= \env -> lift $
      do ptr <- getSetupVal env src
         tgt' <- getSetupVal env tgt
         crucible_points_to True bic defaultOptions ptr tgt'
    go (SetupExecuteFunction args) =
      get >>= \env ->
      lift $ traverse (getSetupVal env) args >>= crucible_execute_func bic defaultOptions
    go (SetupPrecond p) = get >>= \env -> lift $
      getTypedTerm env p >>= crucible_precond
    go (SetupPostcond p) = get >>= \env -> lift $
      getTypedTerm env p >>= crucible_postcond

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
