{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TupleSections #-}
module SAWServer.JVMCrucibleSetup
  ( jvmLoadClass
  , compileJVMContract
  ) where

import Control.Exception (throw)
import Control.Lens ( view )
import Control.Monad.IO.Class ( MonadIO(liftIO) )
import Data.Aeson (FromJSON(..), withObject, (.:))
import Data.ByteString (ByteString)
import Data.Map (Map)
import qualified Data.Map as Map

import qualified Cryptol.Parser.AST as P
import Cryptol.Utils.Ident (mkIdent)
import qualified Lang.Crucible.JVM as CJ
import SAWScript.Crucible.Common.MethodSpec as MS (SetupValue(..))
import SAWScript.Crucible.JVM.Builtins
    ( jvm_alloc_array,
      jvm_alloc_object,
      jvm_elem_is,
      jvm_field_is,
      jvm_static_field_is,
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
      CrucibleSetupVal(..),
      sawTask,
      setServerVal )
import SAWServer.Data.Contract
    ( PointsTo(PointsTo),
      Allocated(Allocated),
      ContractVar(ContractVar),
      Contract(preVars, preConds, preAllocated, prePointsTos,
               argumentVals, postVars, postConds, postAllocated, postPointsTos,
               returnVal) )
import SAWServer.Data.SetupValue ()
import SAWServer.CryptolExpression (CryptolModuleException(..), getTypedTermOfCExp)
import SAWServer.Exceptions ( notAtTopLevel )
import SAWServer.OK ( OK, ok )
import SAWServer.TopLevel ( tl )

newtype StartJVMSetupParams
  = StartJVMSetupParams ServerName

instance FromJSON StartJVMSetupParams where
  parseJSON =
    withObject "params for \"SAW/Crucible setup\"" $ \o ->
    StartJVMSetupParams <$> o .: "name"

instance Doc.DescribedMethod StartJVMSetupParams OK where
  parameterFieldDescription =
    [ ("name",
       Doc.Paragraph [Doc.Text "The name of the item to setup on the server."])
    ]
  resultFieldDescription = []

newtype ServerSetupVal = Val (SetupValue CJ.JVM)

compileJVMContract ::
  (FilePath -> IO ByteString) ->
  BuiltinContext ->
  CryptolEnv ->
  Contract JavaType (P.Expr P.PName) ->
  JVMSetupM ()
compileJVMContract fileReader bic cenv0 c =
  do allocsPre <- mapM setupAlloc (preAllocated c)
     (envPre, cenvPre) <- setupState allocsPre (Map.empty, cenv0) (preVars c)
     mapM_ (\p -> getTypedTerm cenvPre p >>= jvm_precond) (preConds c)
     mapM_ (setupPointsTo (envPre, cenvPre)) (prePointsTos c)
     --mapM_ (setupGhostValue ghostEnv cenvPre) (preGhostValues c)
     traverse (getSetupVal (envPre, cenvPre)) (argumentVals c) >>= jvm_execute_func
     allocsPost <- mapM setupAlloc (postAllocated c)
     (envPost, cenvPost) <- setupState (allocsPre ++ allocsPost) (envPre, cenvPre) (postVars c)
     mapM_ (\p -> getTypedTerm cenvPost p >>= jvm_postcond) (postConds c)
     mapM_ (setupPointsTo (envPost, cenvPost)) (postPointsTos c)
     --mapM_ (setupGhostValue ghostEnv cenvPost) (postGhostValues c)
     case returnVal c of
       Just v -> getSetupVal (envPost, cenvPost) v >>= jvm_return
       Nothing -> return ()
  where
    setupFresh :: ContractVar JavaType -> JVMSetupM (ServerName, TypedTerm)
    setupFresh (ContractVar n dn ty) =
      do t <- jvm_fresh_var dn ty
         return (n, t)
    setupState allocs (env, cenv) vars =
      do freshTerms <- mapM setupFresh vars
         let cenv' = foldr (\(ServerName n, t) -> CEnv.bindTypedTerm (mkIdent n, t)) cenv freshTerms
         let env' = Map.union env $ Map.fromList $
                   [ (n, Val (MS.SetupTerm t)) | (n, t) <- freshTerms ] ++
                   [ (n, Val v) | (n, v) <- allocs ]
         return (env', cenv')

    setupAlloc :: Allocated JavaType -> JVMSetupM (ServerName, MS.SetupValue CJ.JVM)
    setupAlloc (Allocated _ _ False _) =
      JVMSetupM $ fail "Immutable allocations not supported in JVM API."
    setupAlloc (Allocated _ _ _ (Just _)) =
      JVMSetupM $ fail "Alignment not supported in JVM API."
    setupAlloc (Allocated n ty True Nothing) =
      case ty of
        JavaArray sz ety -> (n,) <$> jvm_alloc_array sz ety
        JavaClass cname -> (n,) <$> jvm_alloc_object cname
        _ -> JVMSetupM $ fail $ "Cannot allocate Java object of type " ++ show ty

    setupPointsTo _ (PointsTo _ _ (Just _) _) =
      JVMSetupM $ fail "Points-to without type checking not supported in JVM API."
    setupPointsTo _ (PointsTo _ _ _ (Just _)) =
      JVMSetupM $ fail "Conditional points-to not supported in JVM API."
    setupPointsTo env (PointsTo p v Nothing Nothing) =
      do sv <- getSetupVal env v
         case p of
           FieldLValue base fld ->
             getSetupVal env base >>= \o -> jvm_field_is o fld sv
           ElementLValue base eidx ->
             getSetupVal env base >>= \o -> jvm_elem_is o eidx sv
           GlobalLValue name -> jvm_static_field_is name sv
           _ -> JVMSetupM $ fail "Invalid points-to statement."

    --setupGhostValue _ _ _ = fail "Ghost values not supported yet in JVM API."

    resolve :: Map ServerName a -> ServerName -> JVMSetupM a
    resolve env name =
      JVMSetupM $
      case Map.lookup name env of
        Just v -> return v
        Nothing -> fail $ unlines
                   [ "Server value " ++ show name ++ " not found - impossible!" -- rule out elsewhere
                   , show (Map.keys env)
                   ]

    getTypedTerm ::
      CryptolEnv ->
      P.Expr P.PName ->
      JVMSetupM TypedTerm
    getTypedTerm cenv expr = JVMSetupM $
      do (res, warnings) <- liftIO $ getTypedTermOfCExp fileReader (biSharedContext bic) cenv expr
         case res of
           Right (t, _) -> return t
           Left err -> throw $ CryptolModuleException err warnings

    getSetupVal ::
      (Map ServerName ServerSetupVal, CryptolEnv) ->
      CrucibleSetupVal (P.Expr P.PName) ->
      JVMSetupM (MS.SetupValue CJ.JVM)
    getSetupVal _ NullValue = JVMSetupM $ return (MS.SetupNull ())
    getSetupVal (env, _) (NamedValue n) =
      resolve env n >>= \case Val x -> return x
    getSetupVal (_, cenv) (CryptolExpr expr) =
      MS.SetupTerm <$> getTypedTerm cenv expr
    getSetupVal _ (ArrayValue _) =
      JVMSetupM $ fail "Array setup values unsupported in JVM API."
    getSetupVal _ (TupleValue _) =
      JVMSetupM $ fail "Tuple setup values unsupported in JVM API."
    getSetupVal _ (FieldLValue _ _) =
      JVMSetupM $ fail "Field l-values unsupported in JVM API."
    getSetupVal _ (ElementLValue _ _) =
      JVMSetupM $ fail "Element l-values unsupported in JVM API."
    getSetupVal _ (GlobalInitializer _) =
      JVMSetupM $ fail "Global initializers unsupported in JVM API."
    getSetupVal _ (GlobalLValue _) =
      JVMSetupM $ fail "Global l-values unsupported in JVM API."

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

instance Doc.DescribedMethod JVMLoadClassParams OK where
  parameterFieldDescription =
    [ ("name",
        Doc.Paragraph [Doc.Text "The name of the class on the server."])
    , ("class",
      Doc.Paragraph [Doc.Text "The java class to load."])
    ]
  resultFieldDescription = []
