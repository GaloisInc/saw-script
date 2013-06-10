{-# LANGUAGE ScopedTypeVariables #-}
module SAWScript.Execution where

import Verifier.SAW.Evaluator
import Verifier.SAW.Prelude
import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedAST

import SAWScript.Builtins

execSAWCore :: Module -> IO ()
execSAWCore m =
  case findDef m mainId of
    Nothing -> putStrLn "Module doesn't include a main function"
    Just mainDef -> do
      putStrLn $ "The main function has type " ++ show (defType (mainDef))
      putStrLn $ "Going to execute SAWCore module " ++ show (moduleName m)
      (sc :: SharedContext s) <- mkSharedContext m
      let global = evalGlobal m (allPrims global)
      let t = Term (FTermF (GlobalDef mainId))
      runSC (fromValue (evalTerm global [] t :: Value s)) sc
  where mainId = (mkIdent (moduleName m) "main")
