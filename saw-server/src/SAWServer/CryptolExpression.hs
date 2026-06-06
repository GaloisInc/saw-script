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

import Cryptol.ModuleSystem (ModuleError, ModuleWarning)
import Cryptol.ModuleSystem.Base (genInferInput, getPrimMap, noPat, rename)
import Cryptol.ModuleSystem.Env (ModContextParams(..))
import Cryptol.ModuleSystem.Monad (ModuleM, interactive, setNameSeeds, setSupply, typeCheckWarnings, typeCheckingFailed, getModuleEnv)
import qualified Cryptol.ModuleSystem.Renamer as MR
import Cryptol.Parser.AST ( Expr, PName )
import Cryptol.Parser.Position (emptyRange, getLoc)
import Cryptol.TypeCheck (tcExpr)
import Cryptol.TypeCheck.Monad (InferOutput(..), inpVars, inpTSyns)
import Cryptol.Utils.Ident (interactiveName)

import qualified CryptolSAWCore.Pretty as CryPP
import SAWCentral.Value (biSharedContext, rwGetCryptolEnv)
import CryptolSAWCore.Cryptol
    ( getAllIfaceDecls,
      translateExpr,
      CryptolEnv, eExtraVars, eExtraTySyns, runModuleM )
import CryptolSAWCore.CryptolEnv (getNamingEnv, withFileReader)
import SAWCore.SharedTerm (SharedContext)
import CryptolSAWCore.TypedTerm(TypedTerm(..),TypedTermType(..))

import qualified Argo
import CryptolServer.Data.Expression (Expression, getCryptolExpr)
import CryptolServer.Exceptions (cryptolError)

-- XXX why are we importing what's theoretically the top-level interface from inside?
import SAWServer.SAWServer

getTypedTerm :: Expression -> Argo.Command SAWState TypedTerm
getTypedTerm inputExpr = do
     cenv <- rwGetCryptolEnv . view sawTopLevelRW <$> Argo.getState
     fileReader <- Argo.getFileReader
     expr <- getCryptolExpr inputExpr
     sc <- biSharedContext . view sawBIC <$> Argo.getState
     moduleCmdResult =<< liftIO (getTypedTermOfCExp fileReader sc cenv expr)

getTypedTermOfCExp ::
  (FilePath -> IO B.ByteString) ->
  SharedContext -> CryptolEnv -> Expr PName -> IO (Either ModuleError TypedTerm, [ModuleWarning])
getTypedTermOfCExp fileReader sc cenv expr = withFileReader sc fileReader $ 
  do extraTySyns <- eExtraTySyns sc
     extraVars <- eExtraVars sc
     nameEnv <- getNamingEnv sc cenv
     mres <- runModuleM sc $
       do npe <- interactive (noPat expr) -- eliminate patterns

          -- resolve names
          re <- interactive (rename interactiveName nameEnv (MR.rename npe))

          -- infer types
          env <- getModuleEnv
          let ifDecls = getAllIfaceDecls env
          let range = fromMaybe emptyRange (getLoc re)
          prims <- getPrimMap
          tcEnv <- genInferInput range prims NoParams ifDecls
          let tcEnv' = tcEnv { inpVars = Map.union extraVars (inpVars tcEnv)
                             , inpTSyns = Map.union extraTySyns (inpTSyns tcEnv)
                             }

          out <- liftIO (tcExpr re tcEnv')
          interactive (runInferOutput out)
     case mres of
       (Right (checkedExpr, schema), ws) ->
         do trm <- liftIO $ translateExpr sc checkedExpr
            return (Right (TypedTerm (TypedTermSchema schema) trm), ws)
       (Left err, ws) -> return (Left err, ws)

moduleCmdResult :: (Either ModuleError a, [ModuleWarning]) -> Argo.Command SAWState a
moduleCmdResult (result, warnings) =
  do -- TODO: Printing warnings directly to stdout here is questionable (#2129)
     -- XXX: also it should not (implicitly) use `show` to render the PP doc
     mapM_ (liftIO . print . CryPP.pretty) warnings
     case result of
       Right a -> return a
       Left err      -> Argo.raise $ cryptolError err warnings

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
