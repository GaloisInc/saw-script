{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE PartialTypeSignatures #-}
module SAWServer.CryptolExpression (getTypedTerm, getTypedTermOfCExp) where

import Control.Lens hiding (re)
import Control.Monad.IO.Class
import qualified Data.ByteString as B
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)

import Cryptol.Eval (EvalOpts(..), defaultPPOpts)
import Cryptol.ModuleSystem (ModuleRes)
import Cryptol.ModuleSystem.Base (genInferInput, getPrimMap, noPat, rename)
import Cryptol.ModuleSystem.Env (ModuleEnv)
import Cryptol.ModuleSystem.Interface (noIfaceParams)
import Cryptol.ModuleSystem.Monad (ModuleM, interactive, runModuleM, setNameSeeds, setSupply, typeCheckWarnings, typeCheckingFailed)
import qualified Cryptol.ModuleSystem.Renamer as MR
import Cryptol.Parser.AST
import Cryptol.Parser.Position (emptyRange, getLoc)
import Cryptol.TypeCheck (tcExpr)
import Cryptol.TypeCheck.Monad (InferOutput(..), inpVars, inpTSyns)
import Cryptol.Utils.Ident (interactiveName)
import Cryptol.Utils.Logger (quietLogger)
import Cryptol.Utils.PP
import SAWScript.Value (biSharedContext, TopLevelRW(..))
import Verifier.SAW.CryptolEnv
import Verifier.SAW.SharedTerm (SharedContext)
import Verifier.SAW.TypedTerm(TypedTerm(..))

import Argo
import CryptolServer.Data.Expression
import SAWServer
import CryptolServer.Exceptions (cryptolError)

getTypedTerm :: Expression -> Method SAWState TypedTerm
getTypedTerm inputExpr =
  do cenv <- rwCryptol . view sawTopLevelRW <$> getState
     fileReader <- getFileReader
     expr <- getExpr inputExpr
     sc <- biSharedContext . view sawBIC <$> getState
     (t, _) <- moduleCmdResult =<< (liftIO $ getTypedTermOfCExp fileReader sc cenv expr)
     return t

getTypedTermOfCExp ::
  (FilePath -> IO B.ByteString) ->
  SharedContext -> CryptolEnv -> Expr PName -> IO (ModuleRes TypedTerm)
getTypedTermOfCExp fileReader sc cenv expr =
  do let ?fileReader = fileReader
     let env = eModuleEnv cenv
     mres <- runModuleM (defaultEvalOpts, B.readFile, env) $
       do npe <- interactive (noPat expr) -- eliminate patterns

          -- resolve names
          let nameEnv = getNamingEnv cenv
          re <- interactive (rename interactiveName nameEnv (MR.rename npe))

          -- infer types
          let ifDecls = getAllIfaceDecls env
          let range = fromMaybe emptyRange (getLoc re)
          prims <- getPrimMap
          tcEnv <- genInferInput range prims noIfaceParams ifDecls
          let tcEnv' = tcEnv { inpVars = Map.union (eExtraTypes cenv) (inpVars tcEnv)
                             , inpTSyns = Map.union (eExtraTSyns cenv) (inpTSyns tcEnv)
                             }

          out <- liftIO (tcExpr re tcEnv')
          interactive (runInferOutput out)
     case mres of
       (Right ((checkedExpr, schema), modEnv'), ws) ->
         do let env' = cenv { eModuleEnv = modEnv' }
            trm <- liftIO $ translateExpr sc env' checkedExpr
            return (Right (TypedTerm schema trm, modEnv'), ws)
       (Left err, ws) -> return (Left err, ws)

moduleCmdResult :: ModuleRes a -> Method SAWState (a, ModuleEnv)
moduleCmdResult (result, warnings) =
  do mapM_ (liftIO . print . pp) warnings
     case result of
       Right (a, me) -> return (a, me)
       Left err      -> raise $ cryptolError err warnings

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
