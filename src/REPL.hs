module REPL where

import System.Console.Haskeline

--import SAWScript.Parser    ( read )
--import SAWScript.Evaluator ( evaluate )
--import SAWScript.AST       ( print )

echo s = do outputStrLn s; return ()

main :: IO ()
main = do
  putStrLn "SAWScript, Version 2.0.0, :? for help\n"
  putStrLn "\n .oooooo..o       .o.    oooooo   oooooo     oooo "
  putStrLn "d8P'    `Y8      .888.    `888.    `888.     .8'  "
  putStrLn "Y88bo.          .8\"888.    `888.   .8888.   .8'   "
  putStrLn " `\"Y8888o.     .8' `888.    `888  .8'`888. .8'    "
  putStrLn "     `\"Y88b   .88ooo8888.    `888.8'  `888.8'     "
  putStrLn "oo     .d8P  .8'     `888.    `888'    `888'      "
  putStrLn "8\"\"88888P'  o88o     o8888o    `8'      `8'       \n"
  runInputT defaultSettings loop
    where 
      loop :: InputT IO ()
      loop = do
        minput <- getInputLine "> "
        case minput of
          Nothing -> return ()
          Just (':':s) -> processDirective s
          Just expr -> do
            --let ast = read expr
            --    val = evaluate ast
            --echo . print $ val
            outputStrLn $ expr ++ " :: <Expr>"--TODO: Replace this line with the above.
        loop

processDirective :: String -> InputT IO ()
processDirective s = case s of
  "h"       -> printHelp
  "?"       -> printHelp
  otherwise -> do echo ("Unrecognized directive: ':"++s++"'."); return ()

printHelp :: InputT IO ()
printHelp = do --TODO: Fill in directives as they are developed.
  echo " Commands available from the prompt:\n"
  echo " -- Commands for debugging:\n"
  echo " -- Commands for changing settings:\n"
  echo " -- Commands for displaying information:\n"
  return ()