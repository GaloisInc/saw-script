{-# LANGUAGE PatternGuards #-}
module SAWScript.ParserActions (
     Parser, happyError, parseError, lexer, parseSSPgm
   , parseIntRange, mkExprType
   ) where


import Data.Maybe(isJust, listToMaybe)
import qualified Data.Map as M
import System.Directory(canonicalizePath, makeRelativeToCurrentDirectory)
import System.FilePath(takeDirectory, (</>))
import System.Exit(exitFailure)

import SAWScript.MethodAST
import SAWScript.Token
import SAWScript.Lexer(lexSAW)
import SAWScript.Parser(parseSAW)
import SAWScript.Utils

newtype Parser a = Parser { unP :: FilePath -> [Token Pos] -> IO (Either String a) }

instance Monad Parser where
  return x       = Parser (\_ _ -> return (Right x))
  Parser h >>= k = Parser (\f ts -> do mbE <- h f ts
                                       case mbE of
                                         Left  e -> return $ Left e
                                         Right r -> unP (k r) f ts)
  fail s = Parser (\_ _ -> return (Left s))

happyError :: Parser a
happyError = Parser $ \_ ts -> failAt (listToMaybe ts)

parseError :: Token Pos -> Parser a
parseError t = Parser $ \_ _ -> failAt (Just t)

bailOut :: Pos -> String -> Parser a
bailOut ep msg = Parser $ \_ _ -> do p <- posRelativeToCurrentDirectory ep
                                     return $ Left $ fmtPos p msg

failAt :: Maybe (Token Pos) -> IO (Either String a)
failAt Nothing          = return $ Left $ "File ended before parsing was complete"
failAt (Just (TEOF ep)) = do p <- posRelativeToCurrentDirectory ep
                             return $ Left $ fmtPos p $ "Parse error at the end of file, forgotten semicolon perhaps?"
failAt (Just t)         = do p <- posRelativeToCurrentDirectory (getPos t)
                             return $ Left $ fmtPos p $ "Parse error at " ++ show (show t)  -- double show is intentional

lexer :: (Token Pos -> Parser a) -> Parser a
lexer cont = Parser (\f toks ->
        case toks of
           []       -> unP (cont (TEOF (endPos f))) f []
           (t : ts) -> unP (cont t)                 f ts)

parseSSPgm :: SSOpts -> IO (SSPgm, M.Map FilePath [(FilePath, Pos)])
parseSSPgm ssOpts = go [(entry, Nothing)] M.empty M.empty
 where entry    = entryPoint ssOpts
       entryDir = takeDirectory entry
       go :: [(FilePath, Maybe Pos)] -> SSPgm -> M.Map FilePath [(FilePath, Pos)]
          -> IO (SSPgm, M.Map FilePath [(FilePath, Pos)])
       go []              m d = return (m, d)
       go ((f, mbP) : fs) m d
        | isJust (f `M.lookup` m)     -- already seen this file
        = go fs m d
        | True
        = do (deps, cmds) <- parseJV ssOpts (f, mbP)
             let canon (sf, sp) = do asf <- canonicalizePath (entryDir </> sf)
                                     return ((asf, Just sp), (sf, asf))
             cdepsMap <- mapM canon deps
             let (cdeps, cmap) = unzip cdepsMap
             go (cdeps ++ fs) (M.insert f (map (route cmap) cmds) m) (M.insert f deps d)
       route cmap (ImportCommand p fp)
         | Just cfp <- fp `lookup` cmap = ImportCommand p cfp
         | True                         = error $ "Cannot find import file " ++ show fp ++ " in import-map " ++ show cmap
       route _ (ExternSBV p n fp t)     = ExternSBV p n (routePathThroughPos p fp) t
       route _ c = c

parseJV :: SSOpts -> (FilePath, Maybe Pos) -> IO ([(FilePath, Pos)], [VerifierCommand])
parseJV ssOpts (f, mbP) = do
       notQuiet ssOpts $ do rf <- makeRelativeToCurrentDirectory f
                            let mkP p = do p' <- posRelativeToCurrentDirectory p
                                           return $ " (imported at " ++ show p' ++ ")"
                            reason <- maybe (return "") mkP mbP
                            putStrLn $ "Loading " ++ show rf ++ ".." ++ reason
       cts <- readFile f
       let toks = lexSAW f cts
       debugVerbose ssOpts $ do putStrLn $ "Token stream for " ++ show f ++ ":"
                                print toks
       res <- unP parseSAW f toks
       case res of
         Left e  -> putStrLn e >> exitFailure
         Right r -> return (concatMap getImport r, r)
  where getImport (ImportCommand p fp) = [(fp, p)]
        getImport _                    = []

-- Parse helpers
parseIntRange :: Pos -> (Int, Int) -> Integer -> Parser Int
parseIntRange p (l, h) i
  | i < fromIntegral l || i > fromIntegral h
  = bailOut p $ "Numeric value " ++ show i ++ " is out of expected range: [" ++ show l ++ "," ++ show h ++ "]"
  | True
  = return $ fromIntegral i

mkExprType :: Pos -> ExprWidth -> Maybe ExprType -> Parser ExprType
mkExprType _  w              Nothing  = return $ BitvectorType w
mkExprType _  (WidthConst i) (Just t) = return $ Array i t
mkExprType p  _              _        = bailOut p "malformed expression type"
