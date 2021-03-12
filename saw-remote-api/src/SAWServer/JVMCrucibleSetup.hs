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

import Control.Lens ( view )
import Control.Monad.IO.Class ( MonadIO(liftIO) )
import Control.Monad.State
    ( evalStateT,
      MonadState(get, put),
      MonadTrans(lift),
      modify' )
import Data.Aeson (FromJSON(..), withObject, (.:))
import Data.ByteString (ByteString)
import Data.Foldable ( traverse_ )
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe ( maybeToList )
import qualified Data.Text as T

import qualified Cryptol.Parser.AST as P
import Cryptol.Utils.Ident (mkIdent)
import qualified Lang.Crucible.JVM as CJ
import SAWScript.Crucible.Common.MethodSpec as MS (SetupValue(..))
import SAWScript.Crucible.JVM.Builtins
    ( jvm_alloc_array,
      jvm_alloc_object,
      jvm_execute_func,
      jvm_fresh_var,
      jvm_postcond,
      jvm_precond,
      jvm_return )
import SAWScript.Crucible.JVM.BuiltinsJVM ( loadJavaClass )
import SAWScript.JavaExpr (JavaType(..))
import SAWScript.Value (BuiltinContext, JVMSetupM(..), biSharedContext)
import qualified Verifier.SAW.CryptolEnv as CEnv
import Verifier.SAW.CryptolEnv (CryptolEnv)
import Verifier.SAW.TypedTerm (TypedTerm)

import qualified Argo
import qualified Argo.Doc as Doc
import SAWServer
    ( ServerName(..),
      SAWState,
      SetupStep(..),
      CrucibleSetupVal(CryptolExpr, NullValue, NamedValue),
      SAWTask(JVMSetup),
      sawTask,
      pushTask,
      setServerVal )
import SAWServer.Data.Contract
    ( PointsTo(PointsTo),
      Allocated(Allocated),
      ContractVar(ContractVar),
      Contract(preVars, preConds, preAllocated, prePointsTos,
               argumentVals, postVars, postConds, postAllocated, postPointsTos,
               returnVal) )
import SAWServer.Data.SetupValue ()
import SAWServer.CryptolExpression (getTypedTermOfCExp)
import SAWServer.Exceptions ( notAtTopLevel )
import SAWServer.OK ( OK, ok )
import SAWServer.TopLevel ( tl )

startJVMSetup :: StartJVMSetupParams -> Argo.Command SAWState OK
startJVMSetup (StartJVMSetupParams n) =
  do pushTask (JVMSetup n [])
     ok

newtype StartJVMSetupParams
  = StartJVMSetupParams ServerName

instance FromJSON StartJVMSetupParams where
  parseJSON =
    withObject "params for \"SAW/Crucible setup\"" $ \o ->
    StartJVMSetupParams <$> o .: "name"

instance Doc.DescribedParams StartJVMSetupParams where
  parameterFieldDescription =
    [ ("name",
       Doc.Paragraph [Doc.Text "The name of the item to setup on the server."])
    ]

newtype ServerSetupVal = Val (SetupValue CJ.JVM)

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
      map (\(PointsTo p v chkV cond) -> SetupPointsTo p v chkV cond) (prePointsTos c) ++
      [ SetupExecuteFunction (argumentVals c) ] ++
      map setupFresh (postVars c) ++
      map SetupPostcond (postConds c) ++
      map setupAlloc (postAllocated c) ++
      map (\(PointsTo p v chkV cond) -> SetupPointsTo p v chkV cond) (postPointsTos c) ++
      [ SetupReturn v | v <- maybeToList (returnVal c) ]

interpretJVMSetup ::
  (FilePath -> IO ByteString) ->
  BuiltinContext ->
  CryptolEnv ->
  [SetupStep JavaType] ->
  JVMSetupM ()
interpretJVMSetup fileReader bic cenv0 ss = evalStateT (traverse_ go ss) (mempty, cenv0)
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
    go (SetupPointsTo src tgt _chkTgt _cond) = get >>= \env -> lift $
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
    getSetupVal (env, _) (NamedValue n) = JVMSetupM $
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

jvmLoadClass :: JVMLoadClassParams -> Argo.Command SAWState OK
jvmLoadClass (JVMLoadClassParams serverName cname) =
  do tasks <- view sawTask <$> Argo.getState
     case tasks of
       (_:_) -> Argo.raise $ notAtTopLevel $ map fst tasks
       [] ->
         do c <- tl $ loadJavaClass cname
            setServerVal serverName c
            ok

instance Doc.DescribedParams JVMLoadClassParams where
  parameterFieldDescription =
    [ ("name",
        Doc.Paragraph [Doc.Text "The name of the class on the server."])
    , ("class",
      Doc.Paragraph [Doc.Text "The java class to load."])
    ]
