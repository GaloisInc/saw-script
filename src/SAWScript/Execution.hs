{-# LANGUAGE ScopedTypeVariables #-}
module SAWScript.Execution where

import Control.Monad

import Verifier.SAW.Evaluator
import Verifier.SAW.Prelude
import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedAST

import SAWScript.Builtins
import SAWScript.Options

execSAWCore :: Options -> Module -> IO ()
execSAWCore opts m =
  case findDef m mainId of
    Nothing -> putStrLn "Module doesn't include a main function"
    Just _ -> do
      when (verbLevel opts > 0) $
        putStrLn $ "Executing " ++ show (moduleName m) ++ ".main"
      (sc :: SharedContext s) <- mkSharedContext m
      let global = evalGlobal m ((allPrims opts) global)
      let t = Term (FTermF (GlobalDef mainId))
      runSC (fromValue (evalTerm global [] t :: Value s)) sc
  where mainId = (mkIdent (moduleName m) "main")
