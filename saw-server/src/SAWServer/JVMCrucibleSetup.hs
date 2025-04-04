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
  , jvmLoadClassDescr
  , compileJVMContract
  ) where

import Control.Exception (throw)
import Control.Lens ( view )
import Control.Monad (unless)
import Control.Monad.IO.Class ( MonadIO(liftIO) )
import Data.Aeson (FromJSON(..), withObject, (.:))
import Data.ByteString (ByteString)
import Data.Map (Map)
import qualified Data.Map as Map

import qualified Cryptol.Parser.AST as P
import Cryptol.Utils.Ident (mkIdent)
import qualified Lang.Crucible.JVM as CJ
import qualified SAWCentral.Crucible.Common.MethodSpec as MS
import SAWCentral.Crucible.JVM.Builtins
    ( jvm_alloc_array,
      jvm_alloc_object,
      jvm_elem_is,
      jvm_field_is,
      jvm_static_field_is,
      jvm_execute_func,
      jvm_fresh_var,
      jvm_ghost_value,
      jvm_postcond,
      jvm_precond,
      jvm_return )
import SAWCentral.Crucible.JVM.BuiltinsJVM ( loadJavaClass )
import SAWCentral.JavaExpr (JavaType(..))
import SAWCentral.Value (BuiltinContext, JVMSetupM(..), biSharedContext)
import qualified CryptolSAWCore.CryptolEnv as CEnv
import CryptolSAWCore.CryptolEnv (CryptolEnv)
import CryptolSAWCore.TypedTerm (TypedTerm)

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
      PointsToBitfield,
      GhostValue(GhostValue),
      Allocated(Allocated),
      ContractVar(ContractVar),
      Contract(mutableGlobals, preVars, preConds, preAllocated, preGhostValues, prePointsTos, prePointsToBitfields,
               argumentVals, postVars, postConds, postAllocated, postGhostValues, postPointsTos, postPointsToBitfields,
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

newtype ServerSetupVal = Val (MS.SetupValue CJ.JVM)

compileJVMContract ::
  (FilePath -> IO ByteString) ->
  BuiltinContext ->
  Map ServerName MS.GhostGlobal ->
  CryptolEnv ->
  Contract JavaType (P.Expr P.PName) ->
  JVMSetupM ()
compileJVMContract fileReader bic ghostEnv cenv0 c =
  do unless (null (mutableGlobals c)) $
       JVMSetupM $ fail "Allocating mutable global variables not supported in the JVM API."
     allocsPre <- mapM setupAlloc (preAllocated c)
     (envPre, cenvPre) <- setupState allocsPre (Map.empty, cenv0) (preVars c)
     mapM_ (\p -> getTypedTerm cenvPre p >>= jvm_precond) (preConds c)
     mapM_ (setupPointsTo (envPre, cenvPre)) (prePointsTos c)
     mapM_ setupPointsToBitfields (prePointsToBitfields c)
     mapM_ (setupGhostValue ghostEnv cenvPre) (preGhostValues c)
     traverse (getSetupVal (envPre, cenvPre)) (argumentVals c) >>= jvm_execute_func
     allocsPost <- mapM setupAlloc (postAllocated c)
     (envPost, cenvPost) <- setupState (allocsPre ++ allocsPost) (envPre, cenvPre) (postVars c)
     mapM_ (\p -> getTypedTerm cenvPost p >>= jvm_postcond) (postConds c)
     mapM_ (setupPointsTo (envPost, cenvPost)) (postPointsTos c)
     mapM_ setupPointsToBitfields (postPointsToBitfields c)
     mapM_ (setupGhostValue ghostEnv cenvPost) (postGhostValues c)
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

    setupPointsToBitfields :: PointsToBitfield JavaType (P.Expr P.PName) -> JVMSetupM ()
    setupPointsToBitfields _ =
      JVMSetupM $ fail "Points-to-bitfield not supported in JVM API."

    setupGhostValue genv cenv (GhostValue serverName e) =
      do g <- resolve genv serverName
         t <- getTypedTerm cenv e
         jvm_ghost_value g t

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
      CrucibleSetupVal JavaType (P.Expr P.PName) ->
      JVMSetupM (MS.SetupValue CJ.JVM)
    getSetupVal _ NullValue = JVMSetupM $ return (MS.SetupNull ())
    getSetupVal (env, _) (NamedValue n) =
      resolve env n >>= \case Val x -> return x
    getSetupVal (_, cenv) (CryptolExpr expr) =
      MS.SetupTerm <$> getTypedTerm cenv expr
    getSetupVal _ (ArrayValue _ _) =
      JVMSetupM $ fail "Array setup values unsupported in JVM API."
    getSetupVal _ (StructValue _ _) =
      JVMSetupM $ fail "Struct setup values unsupported in JVM API."
    getSetupVal _ (EnumValue _ _ _) =
      JVMSetupM $ fail "Enum setup values unsupported in JVM API."
    getSetupVal _ (TupleValue _) =
      JVMSetupM $ fail "Tuple setup values unsupported in JVM API."
    getSetupVal _ (SliceValue _) =
      JVMSetupM $ fail "Slice setup values unsupported in JVM API."
    getSetupVal _ (SliceRangeValue _ _ _) =
      JVMSetupM $ fail "Slice range setup values unsupported in JVM API."
    getSetupVal _ (StrSliceValue _) =
      JVMSetupM $ fail "String slice setup values unsupported in JVM API."
    getSetupVal _ (StrSliceRangeValue _ _ _) =
      JVMSetupM $ fail "String slice range setup values unsupported in JVM API."
    getSetupVal _ (FieldLValue _ _) =
      JVMSetupM $ fail "Field l-values unsupported in JVM API."
    getSetupVal _ (CastLValue _ _) =
      JVMSetupM $ fail "Cast l-values unsupported in JVM API."
    getSetupVal _ (UnionLValue _ _) =
      JVMSetupM $ fail "Union l-values unsupported in JVM API."
    getSetupVal _ (ElementLValue _ _) =
      JVMSetupM $ fail "Element l-values unsupported in JVM API."
    getSetupVal _ (GlobalInitializer _) =
      JVMSetupM $ fail "Global initializers unsupported in JVM API."
    getSetupVal _ (GlobalLValue _) =
      JVMSetupM $ fail "Global l-values unsupported in JVM API."
    getSetupVal _ (FreshExpandedValue _ _) =
      JVMSetupM $ fail "Fresh expanded values unsupported in JVM API."

data JVMLoadClassParams
  = JVMLoadClassParams ServerName String

instance FromJSON JVMLoadClassParams where
  parseJSON =
    withObject "params for \"SAW/JVM/load class\"" $ \o ->
    JVMLoadClassParams <$> o .: "name" <*> o .: "class name"

jvmLoadClass :: JVMLoadClassParams -> Argo.Command SAWState OK
jvmLoadClass (JVMLoadClassParams serverName cname) =
  do tasks <- view sawTask <$> Argo.getState
     case tasks of
       (_:_) -> Argo.raise $ notAtTopLevel $ map fst tasks
       [] ->
         do c <- tl $ loadJavaClass cname
            setServerVal serverName c
            ok

jvmLoadClassDescr :: Doc.Block
jvmLoadClassDescr =
  Doc.Paragraph [Doc.Text "Load the JVM class with the given name for later verification."]

instance Doc.DescribedMethod JVMLoadClassParams OK where
  parameterFieldDescription =
    [ ("name",
        Doc.Paragraph [Doc.Text "The name of the class on the server."])
    , ("class name",
      Doc.Paragraph [Doc.Text "The java class to load."])
    ]
  resultFieldDescription = []
