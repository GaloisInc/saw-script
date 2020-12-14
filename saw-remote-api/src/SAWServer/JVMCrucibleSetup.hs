{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PartialTypeSignatures #-}
module SAWServer.JVMCrucibleSetup
  ( startJVMSetup
  , jvmLoadClass
  , compileJVMContract
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
import qualified Lang.Crucible.JVM as CJ
import SAWScript.Crucible.Common.MethodSpec as MS (SetupValue(..))
import SAWScript.Crucible.JVM.Builtins
import SAWScript.Crucible.JVM.BuiltinsJVM
import SAWScript.JavaExpr (JavaType(..))
import SAWScript.Value (BuiltinContext, JVMSetupM(..), biSharedContext)
import qualified Verifier.SAW.CryptolEnv as CEnv
import Verifier.SAW.CryptolEnv (CryptolEnv)
import Verifier.SAW.TypedTerm (TypedTerm)

import Argo
import SAWServer
import SAWServer.Data.Contract
import SAWServer.Data.SetupValue ()
import SAWServer.CryptolExpression (getTypedTermOfCExp)
import SAWServer.Exceptions
import SAWServer.OK
import SAWServer.TopLevel

startJVMSetup :: StartJVMSetupParams -> Method SAWState OK
startJVMSetup (StartJVMSetupParams n) =
  do pushTask (JVMSetup n [])
     ok

data StartJVMSetupParams
  = StartJVMSetupParams ServerName

instance FromJSON StartJVMSetupParams where
  parseJSON =
    withObject "params for \"SAW/Crucible setup\"" $ \o ->
    StartJVMSetupParams <$> o .: "name"

data ServerSetupVal = Val (SetupValue CJ.JVM)

-- TODO: this is an extra layer of indirection that could be collapsed, but is easy to implement for now.
compileJVMContract ::
  (FilePath -> IO ByteString) ->
  BuiltinContext ->
  CryptolEnv ->
  Contract JavaType (P.Expr P.PName) ->
  JVMSetupM ()
compileJVMContract fileReader bic cenv c = interpretJVMSetup fileReader bic cenv steps
  where
    setupFresh (ContractVar n dn ty) = SetupFresh n dn ty
    setupAlloc (Allocated n ty mut align) = SetupAlloc n ty mut align
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

interpretJVMSetup ::
  (FilePath -> IO ByteString) ->
  BuiltinContext ->
  CryptolEnv ->
  [SetupStep JavaType] ->
  JVMSetupM ()
interpretJVMSetup fileReader bic cenv0 ss = runStateT (traverse_ go ss) (mempty, cenv0) *> pure ()
  where
    go (SetupReturn v) = get >>= \env -> lift $ getSetupVal env v >>= jvm_return
    -- TODO: do we really want two names here?
    go (SetupFresh name@(ServerName n) debugName ty) =
      do t <- lift $ jvm_fresh_var (T.unpack debugName) ty
         (env, cenv) <- get
         put (env, CEnv.bindTypedTerm (mkIdent n, t) cenv)
         save name (Val (MS.SetupTerm t))
    go (SetupAlloc name _ _ (Just _)) =
      error $ "attempted to allocate a Java object with alignment information: " ++ show name
    go (SetupAlloc name (JavaArray n ty) True Nothing) =
      lift (jvm_alloc_array n ty) >>= save name . Val
    go (SetupAlloc name (JavaClass c) True Nothing) =
      lift (jvm_alloc_object c) >>= save name . Val
    go (SetupAlloc _ ty _ Nothing) =
      error $ "cannot allocate type: " ++ show ty
    go (SetupPointsTo src tgt) = get >>= \env -> lift $
      do _ptr <- getSetupVal env src
         _tgt' <- getSetupVal env tgt
         error "nyi: points-to"
    go (SetupExecuteFunction args) =
      get >>= \env ->
      lift $ traverse (getSetupVal env) args >>= jvm_execute_func
    go (SetupPrecond p) = get >>= \env -> lift $
      getTypedTerm env p >>= jvm_precond
    go (SetupPostcond p) = get >>= \env -> lift $
      getTypedTerm env p >>= jvm_postcond

    save name val = modify' (\(env, cenv) -> (Map.insert name val env, cenv))

    getSetupVal ::
      (Map ServerName ServerSetupVal, CryptolEnv) ->
      CrucibleSetupVal (P.Expr P.PName) ->
      JVMSetupM (MS.SetupValue CJ.JVM)
    getSetupVal _ NullValue = JVMSetupM $ return $ MS.SetupNull ()
                              {-
    getSetupVal env (ArrayValue elts) =
      do elts' <- mapM (getSetupVal env) elts
         JVMSetupM $ return $ MS.SetupArray () elts'
    getSetupVal env (FieldLValue base fld) =
      do base' <- getSetupVal env base
         JVMSetupM $ return $ MS.SetupField () base' fld
    getSetupVal env (ElementLValue base idx) =
      do base' <- getSetupVal env base
         JVMSetupM $ return $ MS.SetupElem () base' idx
    getSetupVal _ (GlobalInitializer name) =
      JVMSetupM $ return $ MS.SetupGlobalInitializer () name
    getSetupVal _ (GlobalLValue name) =
      JVMSetupM $ return $ MS.SetupGlobal () name
         -}
    getSetupVal (env, _) (ServerValue n) = JVMSetupM $
      resolve env n >>=
      \case
        Val x -> return x -- TODO add cases for the server values that
                          -- are not coming from the setup monad
                          -- (e.g. surrounding context)
    getSetupVal (_, cenv) (CryptolExpr expr) = JVMSetupM $
      do res <- liftIO $ getTypedTermOfCExp fileReader (biSharedContext bic) cenv expr
         -- TODO: add warnings (snd res)
         case fst res of
           Right (t, _) -> return (MS.SetupTerm t)
           Left err -> error $ "Cryptol error: " ++ show err -- TODO: report properly
    getSetupVal _ _sv = error $ "unrecognized setup value" -- ++ show sv

    getTypedTerm ::
      (Map ServerName ServerSetupVal, CryptolEnv) ->
      P.Expr P.PName ->
      JVMSetupM TypedTerm
    getTypedTerm (_, cenv) expr = JVMSetupM $
      do res <- liftIO $ getTypedTermOfCExp fileReader (biSharedContext bic) cenv expr
         -- TODO: add warnings (snd res)
         case fst res of
           Right (t, _) -> return t
           Left err -> error $ "Cryptol error: " ++ show err -- TODO: report properly

    resolve env name =
       case Map.lookup name env of
         Just v -> return v
         Nothing -> error "Server value not found - impossible!" -- rule out elsewhere

data JVMLoadClassParams
  = JVMLoadClassParams ServerName String

instance FromJSON JVMLoadClassParams where
  parseJSON =
    withObject "params for \"SAW/JVM/load class\"" $ \o ->
    JVMLoadClassParams <$> o .: "name" <*> o .: "class"

jvmLoadClass :: JVMLoadClassParams -> Method SAWState OK
jvmLoadClass (JVMLoadClassParams serverName cname) =
  do tasks <- view sawTask <$> getState
     case tasks of
       (_:_) -> raise $ notAtTopLevel $ map fst tasks
       [] ->
         do c <- tl $ loadJavaClass cname
            setServerVal serverName c
            ok
