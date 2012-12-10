
import SAWScript.AST
import SAWScript.Unify

import SAWScript.LiftPoly
import SAWScript.TypeCheck
import SAWScript.GroundType

import Control.Monad

testAll :: IO ()
testAll = mapM_ testModule
  [ ( "m1"  , m1  )
  , ( "m1b" , m1b )
  , ( "m1c" , m1c )
  , ( "m2"  , m2  )
  , ( "m2b" , m2b )
  , ( "m3"  , m3  )
  , ( "m4"  , m4  )
  , ( "m5"  , m5  )
  , ( "m6"  , m6  )
  ]

compile :: Module MPType -> Err (Module CType)
compile = liftPoly >=> typeCheck >=> groundType

testModule :: (String,Module MPType) -> IO ()
testModule (n,m) = do
  putStrLn (n ++ ":")
  case compile m of
    Left e   -> putStrLn ("Error:\n" ++ indent 2 e)
    Right m' -> putStrLn (indent 2 $ show m')
  putStrLn ""

indent :: Int -> String -> String
indent n = unlines . map (replicate n ' ' ++) . lines

