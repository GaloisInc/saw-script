module SAWScript.Execution where

import Verifier.SAW.TypedAST

execSAWCore :: Module -> IO ()
execSAWCore m =
  case findDef m (mkIdent (moduleName m) "main") of
    Nothing -> putStrLn "Module doesn't include a main function"
    Just mainDef -> do
      putStrLn $ "The main function has type " ++ show (defType (mainDef))
      putStrLn $ "Would execute SAWCore module " ++ show (moduleName m)
