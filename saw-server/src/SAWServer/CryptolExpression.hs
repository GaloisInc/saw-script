{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TupleSections #-}
module SAWServer.CryptolExpression
 ( getCryptolExpr
 , getTypedTerm
 , getTypedTermOfCExp
 , CryptolModuleException(..)
 ) where

import Control.Exception (Exception)
import Control.Lens ( view )
import Control.Monad.IO.Class ( MonadIO(liftIO) )
import qualified Data.ByteString as B
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)

import Cryptol.Eval (EvalOpts(..))
import Cryptol.ModuleSystem (ModuleError, ModuleInput(..), ModuleRes, ModuleWarning)
import Cryptol.ModuleSystem.Base (genInferInput, getPrimMap, noPat, rename)
import Cryptol.ModuleSystem.Env (ModuleEnv, ModContextParams(..))
import Cryptol.ModuleSystem.Monad (ModuleM, interactive, runModuleM, setNameSeeds, setSupply, typeCheckWarnings, typeCheckingFailed)
import qualified Cryptol.ModuleSystem.Renamer as MR
import Cryptol.Parser.AST ( Expr, PName )
import Cryptol.Parser.Position (emptyRange, getLoc)
import Cryptol.TypeCheck (tcExpr)
import Cryptol.TypeCheck.Monad (InferOutput(..), inpVars, inpTSyns)
import Cryptol.TypeCheck.Solver.SMT (withSolver)
import Cryptol.Utils.Ident (interactiveName)
import Cryptol.Utils.Logger (quietLogger)
import Cryptol.Utils.PP ( defaultPPOpts, pp )
import SAWCentral.Value (biSharedContext, TopLevelRW(..))
import CryptolSAWCore.CryptolEnv
    ( getAllIfaceDecls,
      getNamingEnv,
      meSolverConfig,
      translateExpr,
      CryptolEnv(eExtraTypes, eExtraTSyns, eModuleEnv) )
import SAWCore.SharedTerm (SharedContext)
import CryptolSAWCore.TypedTerm(TypedTerm(..),TypedTermType(..))

import qualified Argo
import CryptolServer.Data.Expression (Expression, getCryptolExpr)
import CryptolServer.Exceptions (cryptolError)

-- XXX why are we importing what's theoretically the top-level interface from inside?
import SAWServer.SAWServer

getTypedTerm :: Expression -> Argo.Command SAWState TypedTerm
getTypedTerm inputExpr =
  do cenv <- rwCryptol . view sawTopLevelRW <$> Argo.getState
     fileReader <- Argo.getFileReader
     expr <- getCryptolExpr inputExpr
     sc <- biSharedContext . view sawBIC <$> Argo.getState
     (t, _) <- moduleCmdResult =<< liftIO (getTypedTermOfCExp fileReader sc cenv expr)
     return t

getTypedTermOfCExp ::
  (FilePath -> IO B.ByteString) ->
  SharedContext -> CryptolEnv -> Expr PName -> IO (ModuleRes TypedTerm)
getTypedTermOfCExp fileReader sc cenv expr =
  do let ?fileReader = fileReader
     let env = eModuleEnv cenv
     let minp = ModuleInput True False (pure defaultEvalOpts) B.readFile env
     mres <-
       withSolver (return ()) (meSolverConfig env) $ \s ->
       runModuleM (minp s) $
       do npe <- interactive (noPat expr) -- eliminate patterns

          -- resolve names
          let nameEnv = getNamingEnv cenv
          re <- interactive (rename interactiveName nameEnv (MR.rename npe))

          -- infer types
          let ifDecls = getAllIfaceDecls env
          let range = fromMaybe emptyRange (getLoc re)
          prims <- getPrimMap
          tcEnv <- genInferInput range prims NoParams ifDecls
          let tcEnv' = tcEnv { inpVars = Map.union (eExtraTypes cenv) (inpVars tcEnv)
                             , inpTSyns = Map.union (eExtraTSyns cenv) (inpTSyns tcEnv)
                             }

          out <- liftIO (tcExpr re tcEnv')
          interactive (runInferOutput out)
     case mres of
       (Right ((checkedExpr, schema), modEnv'), ws) ->
         do let env' = cenv { eModuleEnv = modEnv' }
            trm <- liftIO $ translateExpr sc env' checkedExpr
            return (Right (TypedTerm (TypedTermSchema schema) trm, modEnv'), ws)
       (Left err, ws) -> return (Left err, ws)

moduleCmdResult :: ModuleRes a -> Argo.Command SAWState (a, ModuleEnv)
moduleCmdResult (result, warnings) =
  do -- TODO: Printing warnings directly to stdout here is questionable (#2129)
     mapM_ (liftIO . print . pp) warnings
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
