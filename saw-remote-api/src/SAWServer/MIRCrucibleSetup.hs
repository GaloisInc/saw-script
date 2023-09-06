{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
-- | Support for interfacing with MIR-related commands in SAW.
module SAWServer.MIRCrucibleSetup
  ( mirLoadModule
  , mirLoadModuleDescr
  , compileMIRContract
  ) where

import Control.Exception (throw)
import Control.Lens ( (^.), view )
import Control.Monad.IO.Class ( MonadIO(liftIO) )
import Control.Monad.State ( MonadState(..) )
import Data.Aeson ( FromJSON(..), withObject, (.:) )
import Data.ByteString (ByteString)
import Data.Map (Map)
import qualified Data.Map as Map

import Mir.Intrinsics (MIR)

import qualified Cryptol.Parser.AST as P
import Cryptol.Utils.Ident (mkIdent)
import qualified SAWScript.Crucible.Common.MethodSpec as MS
import qualified SAWScript.Crucible.Common.Setup.Type as MS
import SAWScript.Crucible.Common.Setup.Builtins (CheckPointsToType(..))
import SAWScript.Crucible.MIR.Builtins
    ( mir_alloc,
      mir_alloc_mut,
      mir_fresh_var,
      mir_execute_func,
      mir_load_module,
      mir_points_to,
      mir_postcond,
      mir_precond,
      mir_return )
import SAWScript.Crucible.MIR.ResolveSetupValue (typeOfSetupValue)
import SAWScript.Value (BuiltinContext, MIRSetupM(..), biSharedContext)
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
import SAWServer.CryptolExpression (CryptolModuleException(..), getTypedTermOfCExp)
import SAWServer.Data.Contract
    ( PointsTo(PointsTo),
      PointsToBitfield,
      Allocated(Allocated),
      ContractVar(ContractVar),
      Contract(preVars, preConds, preAllocated, prePointsTos, prePointsToBitfields,
               argumentVals, postVars, postConds, postAllocated, postPointsTos, postPointsToBitfields,
               returnVal) )
import SAWServer.Data.MIRType (JSONMIRType, mirType)
import SAWServer.Exceptions ( notAtTopLevel )
import SAWServer.OK ( OK, ok )
import SAWServer.TopLevel ( tl )
import SAWServer.TrackFile ( trackFile )

newtype ServerSetupVal = Val (MS.SetupValue MIR)

compileMIRContract ::
  (FilePath -> IO ByteString) ->
  BuiltinContext ->
  CryptolEnv ->
  Contract JSONMIRType (P.Expr P.PName) ->
  MIRSetupM ()
compileMIRContract fileReader bic cenv0 c =
  do allocsPre <- mapM setupAlloc (preAllocated c)
     (envPre, cenvPre) <- setupState allocsPre (Map.empty, cenv0) (preVars c)
     mapM_ (\p -> getTypedTerm cenvPre p >>= mir_precond) (preConds c)
     mapM_ (setupPointsTo (envPre, cenvPre)) (prePointsTos c)
     mapM_ setupPointsToBitfields (prePointsToBitfields c)
     --mapM_ (setupGhostValue ghostEnv cenvPre) (preGhostValues c)
     traverse (getSetupVal (envPre, cenvPre)) (argumentVals c) >>= mir_execute_func
     allocsPost <- mapM setupAlloc (postAllocated c)
     (envPost, cenvPost) <- setupState (allocsPre ++ allocsPost) (envPre, cenvPre) (postVars c)
     mapM_ (\p -> getTypedTerm cenvPost p >>= mir_postcond) (postConds c)
     mapM_ (setupPointsTo (envPost, cenvPost)) (postPointsTos c)
     mapM_ setupPointsToBitfields (postPointsToBitfields c)
     --mapM_ (setupGhostValue ghostEnv cenvPost) (postGhostValues c)
     case returnVal c of
       Just v -> getSetupVal (envPost, cenvPost) v >>= mir_return
       Nothing -> return ()
  where
    setupFresh :: ContractVar JSONMIRType -> MIRSetupM (ServerName, TypedTerm)
    setupFresh (ContractVar n dn ty) =
      do t <- mir_fresh_var dn (mirType ty)
         return (n, t)
    setupState allocs (env, cenv) vars =
      do freshTerms <- mapM setupFresh vars
         let cenv' = foldr (\(ServerName n, t) -> CEnv.bindTypedTerm (mkIdent n, t)) cenv freshTerms
         let env' = Map.union env $ Map.fromList $
                   [ (n, Val (MS.SetupTerm t)) | (n, t) <- freshTerms ] ++
                   [ (n, Val v) | (n, v) <- allocs ]
         return (env', cenv')

    setupAlloc :: Allocated JSONMIRType -> MIRSetupM (ServerName, MS.SetupValue MIR)
    setupAlloc (Allocated _ _ _ (Just _)) =
      MIRSetupM $ fail "Alignment not supported in the MIR API."
    setupAlloc (Allocated n ty mut Nothing)
      | mut       = (n,) <$> mir_alloc_mut ty'
      | otherwise = (n,) <$> mir_alloc     ty'
      where
        ty' = mirType ty

    setupPointsTo ::
      (Map ServerName ServerSetupVal, CryptolEnv) ->
      PointsTo JSONMIRType (P.Expr P.PName) ->
      MIRSetupM ()
    setupPointsTo _ (PointsTo _ _ Nothing _) =
      MIRSetupM $ fail "Points-to without type checking not supported in the MIR API."
    setupPointsTo _ (PointsTo _ _ (Just (CheckAgainstCastedType _)) _) =
      MIRSetupM $ fail "Points-to + type checking against a casted type not supported in the MIR API."
    setupPointsTo _ (PointsTo _ _ _ (Just _)) =
      MIRSetupM $ fail "Conditional points-to not supported in the MIR API."
    setupPointsTo env (PointsTo p v (Just CheckAgainstPointerType) Nothing) =
      do ptr <- getSetupVal env p
         val <- getSetupVal env v
         mir_points_to ptr val

    setupPointsToBitfields :: PointsToBitfield JSONMIRType (P.Expr P.PName) -> MIRSetupM ()
    setupPointsToBitfields _ =
      MIRSetupM $ fail "Points-to-bitfield not supported in the MIR API."

    --setupGhostValue _ _ _ = fail "Ghost values not supported yet in the MIR API."

    resolve :: Map ServerName a -> ServerName -> MIRSetupM a
    resolve env name =
      MIRSetupM $
      case Map.lookup name env of
        Just v -> return v
        Nothing -> fail $ unlines
                   [ "Server value " ++ show name ++ " not found - impossible!" -- rule out elsewhere
                   , show (Map.keys env)
                   ]

    getTypedTerm ::
      CryptolEnv ->
      P.Expr P.PName ->
      MIRSetupM TypedTerm
    getTypedTerm cenv expr = MIRSetupM $
      do (res, warnings) <- liftIO $ getTypedTermOfCExp fileReader (biSharedContext bic) cenv expr
         case res of
           Right (t, _) -> return t
           Left err -> throw $ CryptolModuleException err warnings

    getSetupVal ::
      (Map ServerName ServerSetupVal, CryptolEnv) ->
      CrucibleSetupVal JSONMIRType (P.Expr P.PName) ->
      MIRSetupM (MS.SetupValue MIR)
    getSetupVal (env, _) (NamedValue n) =
      resolve env n >>= \case Val x -> return x
    getSetupVal (_, cenv) (CryptolExpr expr) =
      MS.SetupTerm <$> getTypedTerm cenv expr
    getSetupVal _ NullValue =
      MIRSetupM $ fail "Null setup values unsupported in the MIR API."
    getSetupVal env (ArrayValue mbEltTy elts) =
      case (mbEltTy, elts) of
        (Nothing, []) ->
          MIRSetupM $ fail "Empty MIR array with unknown element type."
        (Just eltTy, []) ->
          return $ MS.SetupArray (mirType eltTy) []
        (_, elt:eltss) ->
          do st <- MIRSetupM get
             let cc = st ^. MS.csCrucibleContext
             let mspec = st ^. MS.csMethodSpec
             let allocEnv = MS.csAllocations mspec
             let nameEnv = MS.csTypeNames mspec
             elt' <- getSetupVal env elt
             eltss' <- mapM (getSetupVal env) eltss
             ty' <- case mbEltTy of
                      Just eltTy -> pure $ mirType eltTy
                      Nothing -> MIRSetupM $ typeOfSetupValue cc allocEnv nameEnv elt'
             return $ MS.SetupArray ty' (elt':eltss')
    getSetupVal _ (TupleValue _) =
      MIRSetupM $ fail "Tuple setup values unsupported in the MIR API."
    getSetupVal _ (FieldLValue _ _) =
      MIRSetupM $ fail "Field l-values unsupported in the MIR API."
    getSetupVal _ (CastLValue _ _) =
      MIRSetupM $ fail "Cast l-values unsupported in the MIR API."
    getSetupVal _ (UnionLValue _ _) =
      MIRSetupM $ fail "Union l-values unsupported in the MIR API."
    getSetupVal _ (ElementLValue _ _) =
      MIRSetupM $ fail "Element l-values unsupported in the MIR API."
    getSetupVal _ (GlobalInitializer _) =
      MIRSetupM $ fail "Global initializers unsupported in the MIR API."
    getSetupVal _ (GlobalLValue _) =
      MIRSetupM $ fail "Global l-values unsupported in the MIR API."

data MIRLoadModuleParams
  = MIRLoadModuleParams ServerName FilePath

instance FromJSON MIRLoadModuleParams where
  parseJSON =
    withObject "params for \"SAW/MIR/load module\"" $ \o ->
    MIRLoadModuleParams <$> o .: "name" <*> o .: "JSON file"

instance Doc.DescribedMethod MIRLoadModuleParams OK where
  parameterFieldDescription =
    [ ("name",
        Doc.Paragraph [Doc.Text "The name to refer to the loaded module by later."])
    , ("JSON file",
       Doc.Paragraph [Doc.Text "The file containing the MIR JSON file to load."])
    ]
  resultFieldDescription = []

mirLoadModuleDescr :: Doc.Block
mirLoadModuleDescr =
  Doc.Paragraph [Doc.Text "Load the specified MIR module."]

-- | The implementation of the @SAW/MIR/load module@ command.
mirLoadModule :: MIRLoadModuleParams -> Argo.Command SAWState OK
mirLoadModule (MIRLoadModuleParams serverName fileName) =
  do tasks <- view sawTask <$> Argo.getState
     case tasks of
       (_:_) -> Argo.raise $ notAtTopLevel $ map fst tasks
       [] ->
         do mirMod <- tl $ mir_load_module fileName
            setServerVal serverName mirMod
            trackFile fileName
            ok
