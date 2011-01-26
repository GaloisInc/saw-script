{
{-# OPTIONS_GHC -fno-warn-name-shadowing      #-}
{-# OPTIONS_GHC -fno-warn-unused-matches      #-}
{-# OPTIONS_GHC -fno-warn-unused-binds        #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing      #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures  #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
module SAWScript.Parser(parseJVs) where

import Data.Maybe(isJust)
import qualified Data.Map as M

import SAWScript.MethodAST
import SAWScript.Token
import SAWScript.Lexer(lexSAW)
import SAWScript.Utils
}

%expect 0
%tokentype { Token Pos }
%monad { Parser }
%lexer { lexer } { TEOF _ }
%error { parseError }
%name parseSAW VerifierCommands

%token
   import { TImport _ }
   str    { TLit _ $$ }
   ';'    { TSemi _   }
%%

VerifierCommands :: { [VerifierCommand] }
VerifierCommands : {- empty -}                          { []      }
                 | VerifierCommands VerifierCommand ';' { $2 : $1 }

VerifierCommand :: { VerifierCommand }
VerifierCommand : import str { ImportCommand (getPos $1) $2 }

{
newtype Parser a = Parser { unP :: FilePath -> [Token Pos] -> Either String a }

instance Monad Parser where
  return x       = Parser (\_ _ -> Right x)
  Parser h >>= k = Parser (\f ts -> case h f ts of
                                      Left  e -> Left e
                                      Right r -> unP (k r) f ts)
  fail s = Parser (\_ _ -> Left s)

happyError :: Parser a
happyError = Parser $ \_ ts -> failAt ts

parseError :: Token Pos -> Parser a
parseError t = Parser (\_ _ -> failAt [t])

failAt :: [Token Pos] -> Either String a
failAt []    = Left $ "File ended before parsing was complete"
failAt (t:_) = Left $ show (getPos t) ++ ": Parse error at <" ++ show t ++ ">"

lexer :: (Token Pos -> Parser a) -> Parser a
lexer cont = Parser (\f ts ->
        case ts of
           []       -> unP (cont (TEOF (endPos f))) f []
           (t : ts) -> unP (cont t)                 f ts)

parse :: FilePath -> String -> Either String [VerifierCommand]
parse f = either Left (Right . reverse) . unP parseSAW f . lexSAW f

parseJVs :: [FilePath] -> IO JV
parseJVs fs = go (zip fs (repeat Nothing)) M.empty
 where go :: [(FilePath, Maybe Pos)] -> JV -> IO JV
       go []     m = return m
       go ((f, mbP) : fs) m
        | isJust (f `M.lookup` m)     -- already seen this file
        = go fs m
        | True
        = do (deps, cmds) <- parseJV (f, mbP)
             go (deps ++ fs) (M.insert f cmds m)

parseJV :: (FilePath, Maybe Pos) -> IO ([(FilePath, Maybe Pos)], [VerifierCommand])
parseJV (f, mbP) = do
       putStrLn $ "Loading " ++ show f ++ ".." ++ reason
       cts <- readFile f
       case parse f cts of
          Left e  -> error $ "*** Error:" ++ e
          Right r -> return (concatMap getImport r, r)
  where getImport (ImportCommand p fp) = [(fp, Just p)]
        getImport _                    = []
        reason = maybe "" (\p -> " (imported at " ++ show p ++ ")") mbP
}
