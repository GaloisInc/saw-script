
import SAWScript.AST
import SAWScript.Token
import SAWScript.Lexer
import SAWScript.Parser

import SAWScript.Unify
import SAWScript.ResolveSyns
import SAWScript.LiftPoly
import SAWScript.TypeCheck
import SAWScript.ConvertType

import Control.Arrow
import Control.Applicative
import Control.Monad
import Data.Maybe
import Test.QuickCheck
import System.IO

-- Handwritten tests {{{

parseFile :: FilePath -> IO [TopStmt MPType]
parseFile = fmap parse . fmap scan . readFile

{-
findMain :: [TopStmt MPType] -> Err Module MPType
findMain ss = case partition findIt ss of
  ([],_) -> fail "No main function defined."
  (m:rest,ts) -> if null rest
    then let (mb,binds,ts) = processMainLet m in
      return $
        Module
          { declarations = TopLet binds : ts
          , mainBlock = mb
          }
    else fail "Multiple main functions defined."
  where
  findIt :: TopStmt MPType -> ([BlockStmt],[(Name,Expr a))]
  findIt s = case s of
    TopLet binds -> any ((== "main") . fst) binds
    _ -> False
  processMainLet :: TopStmt MPType -> ([BlockStmt MPType],[(Name,Expr MPType)],[TopStmt MPType])
  processMainLet (TopLet binds) = 
-}

testAll :: IO ()
testAll = mapM_ (reduceM $ labelModule *** testModule)
  [ ( "m1"  , m1  )
  , ( "m1b" , m1b )
  , ( "m1c" , m1c )
  , ( "m2"  , m2  )
  , ( "m2b" , m2b )
  , ( "m3"  , m3  )
  , ( "m4"  , m4  )
  , ( "m5"  , m5  )
  , ( "m6"  , m6  )
  , ( "inferBit" , inferBit )
  ]
  where
  reduceM = (>>> uncurry (>>))

testModule :: Module MPType -> IO ()
testModule m = do
  case typeModule m of
    Left e   -> putStrLn ("Error:\n" ++ indent 2 e)
    Right m' -> putStrLn (indent 2 $ show m')
  putStrLn ""

-- }}}

labelModule :: String -> IO ()
labelModule n = putStrLn (n ++ ":")

typeModule :: Module MPType -> Err (Module Type)
typeModule = resolveSyns >=> liftPoly >=> typeCheck >=> convertType

indent :: Int -> String -> String
indent n = unlines . map (replicate n ' ' ++) . lines

{-
class Variant a where
  valid :: Gen a
  invalid :: Gen a

wellFormedPInt :: PType -> Bool
wellFormedPInt pt = isJust $ do
  I x <- match pt
  succeed

wellFormedPType :: PType -> Bool
wellFormedPType pt = isJust $ msum
  [ do Bit' <- match pt; succeed
  , do Z' <- match pt; succeed
  , do Quote' <- match pt; succeed
  , do Array' t l <- match pt
       guard (wellFormedPType t)
       guard (wellFormedPInt l)
  , do Tuple' ts <- match pt
       guard (all wellFormedPType ts)
  , do Record' nts <- match pt
       let (ns,ts) = unzip nts
       guard (all wellFormedPType ts)
  , do Function' at bt <- match pt
       guard (wellFormedPType at)
       guard (wellFormedPType bt)
  , do Syn n <- match pt; succeed
  , do Poly n <- match pt; succeed
  ]
-}  

