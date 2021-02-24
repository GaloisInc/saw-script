{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TupleSections #-}
module SAWServer.CryptolExpression
 (getCryptolExpr
 , getTypedTerm
 , getTypedTermOfCExp
 ) where

import Control.Lens hiding (re)
import Control.Monad.IO.Class
import qualified Data.ByteString as B
import qualified Data.HashMap.Strict as HM
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.ByteString.Base64 as Base64
import Data.Text (Text)
import qualified Data.Text as T
import Data.Text.Encoding (encodeUtf8)
import Data.Traversable (for)

import Cryptol.Eval (EvalOpts(..))
import Cryptol.ModuleSystem (ModuleRes, ModuleInput(..))
import Cryptol.ModuleSystem.Base (genInferInput, getPrimMap, noPat, rename)
import Cryptol.ModuleSystem.Env (ModuleEnv, meSolverConfig)
import Cryptol.ModuleSystem.Interface (noIfaceParams)
import Cryptol.ModuleSystem.Monad (ModuleM, interactive, runModuleM, setNameSeeds, setSupply, typeCheckWarnings, typeCheckingFailed)
import qualified Cryptol.ModuleSystem.Renamer as MR
import Cryptol.Parser.AST
import qualified Cryptol.Parser as CP
import Cryptol.Parser.Position (emptyRange, getLoc)
import Cryptol.TypeCheck (tcExpr)
import Cryptol.TypeCheck.Monad (InferOutput(..), inpVars, inpTSyns)
import Cryptol.TypeCheck.Solver.SMT (withSolver)
import Cryptol.Utils.Ident (interactiveName)
import Cryptol.Utils.Logger (quietLogger)
import Cryptol.Utils.PP
import Cryptol.Utils.RecordMap (recordFromFields)
import SAWScript.Value (biSharedContext, TopLevelRW(..))
import Verifier.SAW.CryptolEnv
import Verifier.SAW.SharedTerm (SharedContext)
import Verifier.SAW.TypedTerm(TypedTerm(..))

import Argo
import CryptolServer.Data.Expression (Expression(..), TypeArguments(..), LetBinding(..), Encoding(..), bytesToInt)
import CryptolServer.Data.Type (JSONPType(..))
import SAWServer
import CryptolServer.Exceptions (cryptolError, cryptolParseErr, invalidHex, invalidBase64)

getTypedTerm :: Expression -> Method SAWState TypedTerm
getTypedTerm inputExpr =
  do cenv <- rwCryptol . view sawTopLevelRW <$> getState
     fileReader <- getFileReader
     expr <- getCryptolExpr inputExpr
     sc <- biSharedContext . view sawBIC <$> getState
     (t, _) <- moduleCmdResult =<< (liftIO $ getTypedTermOfCExp fileReader sc cenv expr)
     return t

getTypedTermOfCExp ::
  (FilePath -> IO B.ByteString) ->
  SharedContext -> CryptolEnv -> Expr PName -> IO (ModuleRes TypedTerm)
getTypedTermOfCExp fileReader sc cenv expr =
  do let ?fileReader = fileReader
     let env = eModuleEnv cenv
     let minp = ModuleInput True (pure defaultEvalOpts) B.readFile env
     mres <-
       withSolver (meSolverConfig env) $ \s ->
       runModuleM (minp s) $
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



-- FIXME REFACTOR/REMOVE `decode` -- it exists in
-- `cryptol-remote-api` but with less polymorphic type.
decode :: Encoding -> Text -> Argo.Method s Integer
decode Base64 txt =
  let bytes = encodeUtf8 txt
  in
    case Base64.decode bytes of
      Left err ->
        Argo.raise (invalidBase64 bytes err)
      Right decoded -> return $ bytesToInt decoded
decode Hex txt =
  squish <$> traverse hexDigit (T.unpack txt)
  where
    squish = foldl (\acc i -> (acc * 16) + i) 0

-- FIXME REFACTOR/REMOVE `hexDigit` -- it exists in
-- `cryptol-remote-api` but with less polymorphic type.
hexDigit :: Num a => Char -> Argo.Method s a
hexDigit '0' = pure 0
hexDigit '1' = pure 1
hexDigit '2' = pure 2
hexDigit '3' = pure 3
hexDigit '4' = pure 4
hexDigit '5' = pure 5
hexDigit '6' = pure 6
hexDigit '7' = pure 7
hexDigit '8' = pure 8
hexDigit '9' = pure 9
hexDigit 'a' = pure 10
hexDigit 'A' = pure 10
hexDigit 'b' = pure 11
hexDigit 'B' = pure 11
hexDigit 'c' = pure 12
hexDigit 'C' = pure 12
hexDigit 'd' = pure 13
hexDigit 'D' = pure 13
hexDigit 'e' = pure 14
hexDigit 'E' = pure 14
hexDigit 'f' = pure 15
hexDigit 'F' = pure 15
hexDigit c   = Argo.raise (invalidHex c)

-- FIXME REFACTOR/REMOVE `getCryptolExpr` -- it exists in
-- `cryptol-remote-api` (as `getExpr`) but with less polymorphic type.
getCryptolExpr :: Expression -> Argo.Method s (Expr PName)
getCryptolExpr Unit =
  return $
    ETyped
      (ETuple [])
      (TTuple [])
getCryptolExpr (Bit b) =
  return $
    ETyped
      (EVar (UnQual (mkIdent $ if b then "True" else "False")))
      TBit
getCryptolExpr (Integer i) =
  return $
    ETyped
      (ELit (ECNum i (DecLit (T.pack (show i)))))
      (TUser (UnQual (mkIdent "Integer")) [])
getCryptolExpr (IntegerModulo i n) =
  return $
    ETyped
      (ELit (ECNum i (DecLit (T.pack (show i)))))
      (TUser (UnQual (mkIdent "Z")) [TNum n])
getCryptolExpr (Num enc txt w) =
  do d <- decode enc txt
     return $ ETyped
       (ELit (ECNum d (DecLit txt)))
       (TSeq (TNum w) TBit)
getCryptolExpr (Record fields) =
  fmap (ERecord . recordFromFields) $ for (HM.toList fields) $
  \(recName, spec) ->
    (mkIdent recName,) . (emptyRange,) <$> getCryptolExpr spec
getCryptolExpr (Sequence elts) =
  EList <$> traverse getCryptolExpr elts
getCryptolExpr (Tuple projs) =
  ETuple <$> traverse getCryptolExpr projs
getCryptolExpr (Concrete syntax) =
  case CP.parseExpr syntax of
    Left err ->
      Argo.raise (cryptolParseErr syntax err)
    Right e -> pure e
getCryptolExpr (Let binds body) =
  EWhere <$> getCryptolExpr body <*> traverse mkBind binds
  where
    mkBind (LetBinding x rhs) =
      DBind .
      (\bindBody ->
         Bind (fakeLoc (UnQual (mkIdent x))) [] bindBody Nothing False Nothing [] True Nothing) .
      fakeLoc .
      DExpr <$>
        getCryptolExpr rhs

    fakeLoc = Located emptyRange
getCryptolExpr (Application fun (arg :| [])) =
  EApp <$> getCryptolExpr fun <*> getCryptolExpr arg
getCryptolExpr (Application fun (arg1 :| (arg : args))) =
  getCryptolExpr (Application (Application fun (arg1 :| [])) (arg :| args))
getCryptolExpr (TypeApplication gen (TypeArguments args)) =
  EAppT <$> getCryptolExpr gen <*> pure (map inst (Map.toList args))
  where
    inst (n, t) = NamedInst (Named (Located emptyRange n) (unJSONPType t))
