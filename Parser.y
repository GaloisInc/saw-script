{
{-# OPTIONS_GHC -fno-warn-name-shadowing      #-}
{-# OPTIONS_GHC -fno-warn-unused-matches      #-}
{-# OPTIONS_GHC -fno-warn-unused-binds        #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing      #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures  #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
module SAWScript.Parser(parseSSPgm) where

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

parseSSPgm :: FilePath -> IO (SSPgm, M.Map FilePath [(FilePath, Pos)])
parseSSPgm f = go [(f, Nothing)] M.empty M.empty
 where go :: [(FilePath, Maybe Pos)] -> SSPgm -> M.Map FilePath [(FilePath, Pos)]
          -> IO (SSPgm, M.Map FilePath [(FilePath, Pos)])
       go []              m d = return (m, d)
       go ((f, mbP) : fs) m d
        | isJust (f `M.lookup` m)     -- already seen this file
        = go fs m d
        | True
        = do (deps, cmds) <- parseJV (f, mbP)
             go (reverse [(f, Just p) | (f, p) <- deps] ++ fs) (M.insert f cmds m) (M.insert f deps d)

parseJV :: (FilePath, Maybe Pos) -> IO ([(FilePath, Pos)], [VerifierCommand])
parseJV (f, mbP) = do
       putStrLn $ "Loading " ++ show f ++ ".." ++ reason
       cts <- readFile f
       let res = unP parseSAW f . lexSAW f $ cts
       case res of
         Left e  -> error $ "*** Error:" ++ e
         Right r -> return (concatMap getImport r, reverse r)
  where getImport (ImportCommand p fp) = [(fp, p)]
        getImport _                    = []
        reason = maybe "" (\p -> " (imported at " ++ show p ++ ")") mbP
}
