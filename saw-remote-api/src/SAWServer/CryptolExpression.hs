{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}

module SAWServer.CryptolExpression
 ( getCryptolExpr
 , getTypedTerm
 , getTypedTermOfCExp
 , CryptolModuleException(..)
 ) where

import Control.Exception (Exception)
import Control.Lens ( view, set )
import Control.Monad.IO.Class ( MonadIO(liftIO) )
import qualified Data.ByteString as B
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)

import Cryptol.Eval (EvalOpts(..))
import Cryptol.ModuleSystem
  (ModuleCmd, ModuleError, ModuleInput(..), ModuleRes, ModuleWarning)
import Cryptol.ModuleSystem.Base (genInferInput, getPrimMap)
import Cryptol.ModuleSystem.Env (ModuleEnv)
import Cryptol.ModuleSystem.Interface (noIfaceParams)
import Cryptol.ModuleSystem.Monad
  (ModuleM, interactive, runModuleM, setNameSeeds, setSupply, typeCheckWarnings, typeCheckingFailed)
import Cryptol.ModuleSystem.Name (Name)
import Cryptol.Parser.AST ( Expr )
import Cryptol.Parser.Position (emptyRange, getLoc)
import Cryptol.TypeCheck (tcExpr)
import Cryptol.TypeCheck.Monad (InferOutput(..), inpVars, inpTSyns)
import Cryptol.TypeCheck.Solver.SMT (withSolver)
import Cryptol.Utils.Logger (quietLogger)
import Cryptol.Utils.PP ( defaultPPOpts, pp )
import SAWScript.Value (biSharedContext, TopLevelRW(..))
import Verifier.SAW.CryptolEnv
    ( getAllIfaceDecls,
      meSolverConfig,
      translateExpr,
      CryptolEnv(eExtraTypes, eExtraTSyns, eModuleEnv) )
import Verifier.SAW.SharedTerm (SharedContext)
import Verifier.SAW.TypedTerm(TypedTerm(..))

import qualified Argo
import CryptolServer.Data.FreshName (FreshName)
import qualified CryptolServer.Data.Expression as CS
import CryptolServer.Exceptions (cryptolError)
import SAWServer

getCryptolExpr :: CS.Expression -> Argo.Command SAWState (Expr Name)
getCryptolExpr = CS.getCryptolExpr resolveFreshName getModuleEnv liftModuleCmd Argo.raise
  where
    resolveFreshName :: FreshName -> Argo.Command SAWState (Maybe Name)
    resolveFreshName = const $ pure Nothing
    getModuleEnv :: Argo.Command SAWState ModuleEnv
    getModuleEnv = eModuleEnv . (view sawCryptolEnv) <$> Argo.getState

getTypedTerm :: CS.Expression -> Argo.Command SAWState TypedTerm
getTypedTerm inputExpr =
  do cenv <- rwCryptol . view sawTopLevelRW <$> Argo.getState
     fileReader <- Argo.getFileReader
     expr <- getCryptolExpr inputExpr
     sc <- biSharedContext . view sawBIC <$> Argo.getState
     (t, _) <- moduleCmdResult =<< liftIO (getTypedTermOfCExp fileReader sc cenv expr)
     return t


getTypedTermOfCExp ::
  (FilePath -> IO B.ByteString) ->
  SharedContext -> CryptolEnv -> Expr Name -> IO (ModuleRes TypedTerm)
getTypedTermOfCExp fileReader sc cenv expr =
  do let ?fileReader = fileReader
     let env = eModuleEnv cenv
     let minp = ModuleInput True (pure defaultEvalOpts) B.readFile env
     mres <-
       withSolver (meSolverConfig env) $ \s ->
       runModuleM (minp s) $
       do -- infer types
          let ifDecls = getAllIfaceDecls env
          let range = fromMaybe emptyRange (getLoc expr)
          prims <- getPrimMap
          tcEnv <- genInferInput range prims noIfaceParams ifDecls
          let tcEnv' = tcEnv { inpVars = Map.union (eExtraTypes cenv) (inpVars tcEnv)
                             , inpTSyns = Map.union (eExtraTSyns cenv) (inpTSyns tcEnv)
                             }

          out <- liftIO (tcExpr expr tcEnv')
          interactive (runInferOutput out)
     case mres of
       (Right ((checkedExpr, schema), modEnv'), ws) ->
         do let env' = cenv { eModuleEnv = modEnv' }
            trm <- liftIO $ translateExpr sc env' checkedExpr
            return (Right (TypedTerm schema trm, modEnv'), ws)
       (Left err, ws) -> return (Left err, ws)

liftModuleCmd :: ModuleCmd a -> Argo.Command SAWState a
liftModuleCmd cmd = do
  cenv <- view sawCryptolEnv <$> Argo.getState
  let env = eModuleEnv cenv
      minp = ModuleInput True (pure defaultEvalOpts) B.readFile env

  out <- liftIO $ withSolver (meSolverConfig env) $ \s -> liftIO (cmd (minp s))
  case out of
    (Left x, warns) -> Argo.raise (cryptolError x warns)
    (Right (x, newEnv), _warns) -> do
      -- TODO: What to do about warnings when a command completes
      -- successfully?
      Argo.modifyState (\s -> let cEnv = (view sawCryptolEnv s) {eModuleEnv = newEnv}
                              in set sawCryptolEnv cEnv s)
      return x

moduleCmdResult :: ModuleRes a -> Argo.Command SAWState (a, ModuleEnv)
moduleCmdResult (result, warnings) =
  do mapM_ (liftIO . print . pp) warnings
     case result of
       Right (a, me) -> return (a, me)
       Left err      -> Argo.raise $ cryptolError err warnings

defaultEvalOpts :: EvalOpts
defaultEvalOpts = EvalOpts quietLogger defaultPPOpts

runInferOutput :: InferOutput a -> ModuleM a
runInferOutput out =
  case out of
    InferOK nm warns seeds supply o ->
      do setNameSeeds seeds
         setSupply supply
         typeCheckWarnings nm warns
         return o

    InferFailed nm warns errs ->
      do typeCheckWarnings nm warns
         typeCheckingFailed nm errs

data CryptolModuleException = CryptolModuleException
  { cmeError    :: ModuleError
  , cmeWarnings :: [ModuleWarning]
  } deriving Show

instance Exception CryptolModuleException
