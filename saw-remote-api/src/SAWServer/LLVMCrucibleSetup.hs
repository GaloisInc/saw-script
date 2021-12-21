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
module SAWServer.LLVMCrucibleSetup
  ( llvmLoadModule
  , llvmLoadModuleDescr
  , Contract(..)
  , ContractVar(..)
  , Allocated(..)
  , PointsTo(..)
  , compileLLVMContract
  ) where

import Control.Exception (throw)
import Control.Lens ( view )
import Control.Monad.IO.Class
import Data.Aeson (FromJSON(..), withObject, (.:))
import Data.ByteString (ByteString)
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Text as T

import qualified Cryptol.Parser.AST as P
import Cryptol.Utils.Ident (mkIdent)
import qualified Data.LLVM.BitCode as LLVM
import qualified SAWScript.Crucible.Common.MethodSpec as MS (SetupValue(..))
import SAWScript.Crucible.LLVM.Builtins
    ( llvm_alloc
    , llvm_alloc_aligned
    , llvm_alloc_global
    , llvm_alloc_readonly
    , llvm_alloc_readonly_aligned
    , llvm_execute_func
    , llvm_fresh_var
    , llvm_points_to_internal
    , llvm_ghost_value
    , llvm_return
    , llvm_precond
    , llvm_postcond )
import qualified SAWScript.Crucible.LLVM.CrucibleLLVM as CL
import qualified SAWScript.Crucible.LLVM.MethodSpecIR as CMS
import qualified SAWScript.Crucible.Common.MethodSpec as CMS (GhostGlobal)
import SAWScript.Value
    ( BuiltinContext, LLVMCrucibleSetupM(..), TopLevelRW(..), biSharedContext )
import qualified Verifier.SAW.CryptolEnv as CEnv
import Verifier.SAW.CryptolEnv (CryptolEnv)
import Verifier.SAW.TypedTerm (TypedTerm)

import qualified Argo
import qualified Argo.Doc as Doc
import SAWServer as Server
    ( ServerName(..),
      SAWState,
      CrucibleSetupVal(..),
      sawTask,
      sawTopLevelRW,
      getHandleAlloc,
      setServerVal )
import SAWServer.Data.Contract
    ( PointsTo(..), GhostValue(..), Allocated(..), ContractVar(..), Contract(..) )
import SAWServer.Data.LLVMType (JSONLLVMType, llvmType)
import SAWServer.Data.SetupValue ()
import SAWServer.CryptolExpression (CryptolModuleException(..), getTypedTermOfCExp)
import SAWServer.Exceptions ( notAtTopLevel, cantLoadLLVMModule )
import SAWServer.OK ( OK, ok )
import SAWServer.TrackFile ( trackFile )

newtype StartLLVMCrucibleSetupParams
  = StartLLVMCrucibleSetupParams ServerName

instance FromJSON StartLLVMCrucibleSetupParams where
  parseJSON =
    withObject "params for \"SAW/Crucible setup\"" $ \o ->
    StartLLVMCrucibleSetupParams <$> o .: "name"

newtype ServerSetupVal = Val (CMS.AllLLVM MS.SetupValue)

compileLLVMContract ::
  (FilePath -> IO ByteString) ->
  BuiltinContext ->
  Map ServerName CMS.GhostGlobal ->
  CryptolEnv ->
  Contract JSONLLVMType (P.Expr P.PName) ->
  LLVMCrucibleSetupM ()
compileLLVMContract fileReader bic ghostEnv cenv0 c =
  do mapM_ (llvm_alloc_global . T.unpack) (mutableGlobals c)
     allocsPre <- mapM setupAlloc (preAllocated c)
     (envPre, cenvPre) <- setupState allocsPre (Map.empty, cenv0) (preVars c)
     mapM_ (\p -> getTypedTerm cenvPre p >>= llvm_precond) (preConds c)
     mapM_ (setupPointsTo (envPre, cenvPre)) (prePointsTos c)
     mapM_ (setupGhostValue ghostEnv cenvPre) (preGhostValues c)
     traverse (getSetupVal (envPre, cenvPre)) (argumentVals c) >>= llvm_execute_func
     allocsPost <- mapM setupAlloc (postAllocated c)
     (envPost, cenvPost) <- setupState (allocsPre ++ allocsPost) (envPre, cenvPre) (postVars c)
     mapM_ (\p -> getTypedTerm cenvPost p >>= llvm_postcond) (postConds c)
     mapM_ (setupPointsTo (envPost, cenvPost)) (postPointsTos c)
     mapM_ (setupGhostValue ghostEnv cenvPost) (postGhostValues c)
     case returnVal c of
       Just v -> getSetupVal (envPost, cenvPost) v >>= llvm_return
       Nothing -> return ()
  where
    setupFresh (ContractVar n dn ty) =
      do t <- llvm_fresh_var dn (llvmType ty)
         return (n, t)

    setupState allocs (env, cenv) vars =
      do freshTerms <- mapM setupFresh vars
         let cenv' = foldr (\(ServerName n, t) -> CEnv.bindTypedTerm (mkIdent n, t)) cenv freshTerms
         let env' = Map.union env $ Map.fromList $
                   [ (n, Val (CMS.anySetupTerm t)) | (n, t) <- freshTerms ] ++
                   [ (n, Val v) | (n, v) <- allocs ]
         return (env', cenv')

    setupAlloc (Allocated n ty mut malign) =
      case (mut, malign) of
        (True,  Nothing)      -> (n,) <$> llvm_alloc ty'
        (False, Nothing)      -> (n,) <$> llvm_alloc_readonly ty'
        (True,  (Just align)) -> (n,) <$> llvm_alloc_aligned align ty'
        (False, (Just align)) -> (n,) <$> llvm_alloc_readonly_aligned align ty'
      where
        ty' = llvmType ty

    setupPointsTo env (PointsTo p v chkTgt cond) =
      do ptr <- getSetupVal env p
         val <- getSetupVal env v
         cond' <- traverse (getTypedTerm (snd env)) cond
         let chkTgt' = fmap (fmap llvmType) chkTgt
         llvm_points_to_internal chkTgt' cond' ptr val

    setupGhostValue genv cenv (GhostValue serverName e) =
      do g <- resolve genv serverName
         t <- getTypedTerm cenv e
         llvm_ghost_value g t

    resolve :: Map ServerName a -> ServerName -> LLVMCrucibleSetupM a
    resolve env name =
      LLVMCrucibleSetupM $
      case Map.lookup name env of
        Just v -> return v
        Nothing -> fail $ unlines
                   [ "Server value " ++ show name ++ " not found - impossible!" -- rule out elsewhere
                   , show (Map.keys env)
                   ]

    getTypedTerm ::
      CryptolEnv ->
      P.Expr P.PName ->
      LLVMCrucibleSetupM TypedTerm
    getTypedTerm cenv expr = LLVMCrucibleSetupM $
      do (res, warnings) <- liftIO $ getTypedTermOfCExp fileReader (biSharedContext bic) cenv expr
         case res of
           Right (t, _) -> return t
           Left err -> throw $ CryptolModuleException err warnings

    getSetupVal ::
      (Map ServerName ServerSetupVal, CryptolEnv) ->
      CrucibleSetupVal (P.Expr P.PName) ->
      LLVMCrucibleSetupM (CMS.AllLLVM MS.SetupValue)
    getSetupVal _ NullValue = LLVMCrucibleSetupM $ return CMS.anySetupNull
    getSetupVal env (ArrayValue elts) =
      do elts' <- mapM (getSetupVal env) elts
         LLVMCrucibleSetupM $ return $ CMS.anySetupArray elts'
    getSetupVal env (TupleValue elts) =
      do elts' <- mapM (getSetupVal env) elts
         LLVMCrucibleSetupM $ return $ CMS.anySetupStruct False elts'
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
    getSetupVal (env, _) (NamedValue n) =
      resolve env n >>= \case Val x -> return x
    getSetupVal (_, cenv) (CryptolExpr expr) =
      CMS.anySetupTerm <$> getTypedTerm cenv expr

data LLVMLoadModuleParams
  = LLVMLoadModuleParams ServerName FilePath

instance FromJSON LLVMLoadModuleParams where
  parseJSON =
    withObject "params for \"SAW/LLVM/load module\"" $ \o ->
    LLVMLoadModuleParams <$> o .: "name" <*> o .: "bitcode file"


instance Doc.DescribedMethod LLVMLoadModuleParams OK where
  parameterFieldDescription =
    [ ("name",
        Doc.Paragraph [Doc.Text "The name to refer to the loaded module by later."])
    , ("bitcode file",
       Doc.Paragraph [Doc.Text "The file containing the bitcode LLVM module to load."])
    ]
  resultFieldDescription = []


llvmLoadModuleDescr :: Doc.Block
llvmLoadModuleDescr =
  Doc.Paragraph [Doc.Text "Load the specified LLVM module."]

llvmLoadModule :: LLVMLoadModuleParams -> Argo.Command SAWState OK
llvmLoadModule (LLVMLoadModuleParams serverName fileName) =
  do tasks <- view sawTask <$> Argo.getState
     case tasks of
       (_:_) -> Argo.raise $ notAtTopLevel $ map fst tasks
       [] ->
         do rw <- view sawTopLevelRW <$> Argo.getState
            let ?transOpts = CL.defaultTranslationOptions
                               { CL.laxArith        = rwLaxArith rw
                               , CL.debugIntrinsics = rwDebugIntrinsics rw
                               }
            halloc <- getHandleAlloc
            loaded <- liftIO (CMS.loadLLVMModule fileName halloc)
            case loaded of
              Left err -> Argo.raise (cantLoadLLVMModule (LLVM.formatError err))
              Right llvmMod ->
                do setServerVal serverName llvmMod
                   trackFile fileName
                   ok
