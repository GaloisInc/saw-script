{- |
Module           : $Header$
Description      :
Stability        : provisional
Point-of-contact : jhendrix, lerkok
-}

{-# LANGUAGE DeriveDataTypeable  #-}
module SAWScript.Utils where

import Control.Exception
import Control.Monad(when)
import Control.DeepSeq(rnf, NFData(..))
import Data.List(intercalate)
import Data.Char(isSpace)
import System.Console.CmdArgs(Data, Typeable)
import System.Directory(makeRelativeToCurrentDirectory)
import System.FilePath(makeRelative, isAbsolute, (</>), takeDirectory)
import System.Time(TimeDiff(..), getClockTime, diffClockTimes, normalizeTimeDiff, toCalendarTime, formatCalendarTime)
import System.Locale(defaultTimeLocale)
import Text.PrettyPrint.HughesPJ
import Numeric(showFFloat)
import Utils.Common (slashesToDots)
import Utils.IOStateT

import qualified Execution.Codebase as JSS
import qualified JavaParser as JSS

data Pos = Pos !FilePath -- file
               !Int      -- line
               !Int      -- col
         | PosInternal String

endPos :: FilePath -> Pos
endPos f = Pos f 0 0

fmtPos :: Pos -> String -> String
fmtPos p m = show p ++ ":\n" ++ m'
  where m' = intercalate "\n" . map ("  " ++) . lines $ m

fmtPoss :: [Pos] -> String -> String
fmtPoss [] m = fmtPos (PosInternal "saw-script internal") m
fmtPoss ps m = "[" ++ intercalate ",\n " (map show ps) ++ "]:\n" ++ m'
  where m' = intercalate "\n" . map ("  " ++) . lines $ m

posRelativeToCurrentDirectory :: Pos -> IO Pos
posRelativeToCurrentDirectory (Pos f l c)     = makeRelativeToCurrentDirectory f >>= \f' -> return (Pos f' l c)
posRelativeToCurrentDirectory (PosInternal s) = return $ PosInternal s

posRelativeTo :: FilePath -> Pos -> Pos
posRelativeTo d (Pos f l c)     = Pos (makeRelative d f) l c
posRelativeTo _ (PosInternal s) = PosInternal s

routePathThroughPos :: Pos -> FilePath -> FilePath
routePathThroughPos (Pos f _ _) fp
  | isAbsolute fp = fp
  | True          = takeDirectory f </> fp
routePathThroughPos (PosInternal _) fp = fp

instance Show Pos where
  show (Pos f 0 0)     = show f ++ ":end-of-file"
  show (Pos f l c)     = show f ++ ":" ++ show l ++ ":" ++ show c
  show (PosInternal s) = "[internal:" ++ s ++ "]"

data SSOpts = SSOpts {
         classpath  :: String
       , jars       :: String
       , verbose    :: Int
       , dump       :: Bool
       , entryPoint :: FilePath
       } deriving (Show, Data, Typeable)

verboseAtLeast :: Int -> SSOpts -> IO () -> IO ()
verboseAtLeast i o = when (verbose o >= i)

notQuiet :: SSOpts -> IO () -> IO ()
notQuiet o = verboseAtLeast 1 o

debugVerbose :: SSOpts -> IO () -> IO ()
debugVerbose o = verboseAtLeast 10 o

-- | Convert a string to a paragraph formatted document.
ftext :: String -> Doc
ftext msg = fsep (map text $ words msg)

-- ExecException {{{1

-- | Class of exceptions thrown by SBV parser.
data ExecException = ExecException Pos          -- ^ Position
                                   Doc          -- ^ Error message
                                   String       -- ^ Resolution tip
  deriving (Show, Typeable)

instance Exception ExecException

-- | Throw exec exception in a MonadIO.
throwIOExecException :: MonadIO m => Pos -> Doc -> String -> m a
throwIOExecException pos errorMsg resolution = liftIO $ throwIO (ExecException pos errorMsg resolution)

-- Java lookup functions {{{1

-- | Atempt to find class with given name, or throw ExecException if no class
-- with that name exists.
lookupClass ::  (JSS.HasCodebase m, MonadIO m) => Pos -> String -> m JSS.Class
lookupClass pos nm = do
  maybeCl <- JSS.tryLookupClass nm
  case maybeCl of
    Nothing -> do
     let msg = ftext ("The Java class " ++ slashesToDots nm ++ " could not be found.")
         res = "Please check that the --classpath and --jars options are set correctly."
      in throwIOExecException pos msg res
    Just cl -> return cl

-- | Returns method with given name in this class or one of its subclasses.
-- Throws an ExecException if method could not be found or is ambiguous.
findMethod :: (JSS.HasCodebase m, MonadIO m)
           => Pos -> String -> JSS.Class -> m (JSS.Class,JSS.Method)
findMethod pos nm initClass = do
  let javaClassName = slashesToDots (JSS.className initClass)
  let methodMatches m = JSS.methodName m == nm && not (JSS.methodIsAbstract m)
  let impl cl =
        case filter methodMatches (JSS.classMethods cl) of
          [] -> do
            case JSS.superClass cl of
              Nothing ->
                let msg = ftext $ "Could not find method " ++ nm
                            ++ " in class " ++ javaClassName ++ "."
                    res = "Please check that the class and method are correct."
                 in throwIOExecException pos msg res
              Just superName ->
                impl =<< lookupClass pos superName
          [method] -> return (cl,method)
          _ -> let msg = "The method " ++ nm ++ " in class " ++ javaClassName
                           ++ " is ambiguous.  SAWScript currently requires that "
                           ++ "method names are unique."
                   res = "Please rename the Java method so that it is unique."
                in throwIOExecException pos (ftext msg) res
  impl initClass

-- | Returns method with given name in this class or one of its subclasses.
-- Throws an ExecException if method could not be found or is ambiguous.
findField :: (JSS.HasCodebase m, MonadIO m)
          => Pos -> String -> JSS.Class -> m JSS.FieldId
findField pos nm initClass = do
  let impl cl =
        case filter (\f -> JSS.fieldName f == nm) $ JSS.classFields cl of
          [] -> do
            case JSS.superClass cl of
              Nothing ->
                let msg = "Could not find a field named " ++ nm ++ " in "
                            ++ slashesToDots (JSS.className initClass) ++ "."
                    res = "Please check to make sure the field name is correct."
                 in throwIOExecException pos (ftext msg) res
              Just superName -> impl =<< lookupClass pos superName
          [f] -> return $ JSS.FieldId (JSS.className cl) nm (JSS.fieldType f)
          _ -> error "internal: Found multiple fields with the same name."
  impl initClass

-- | Return a string representation of the elapsed time since start
timeIt :: (NFData a, MonadIO m) => m a -> m (a, String)
timeIt action = do
        start <- liftIO $ getClockTime
        r <- action
        end <- rnf r `seq` liftIO getClockTime
        let itd = diffClockTimes end start
            td = normalizeTimeDiff itd
            vals = dropWhile (\(v, _) -> v == 0) (zip [tdYear td, tdMonth td, tdDay td, tdHour td, tdMin td] "YMDhm")
            sec = ' ' : show (tdSec td) ++ dropWhile (/= '.') pico
            pico = showFFloat (Just 3) (((10**(-12))::Double) * fromIntegral (tdPicosec td)) "s"
        return $ (r, dropWhile isSpace $ concatMap (\(v, c) -> ' ':show v ++ [c]) vals ++ sec)

-- | get a readable time stamp
getTimeStamp :: MonadIO m => m String
getTimeStamp = do t <- liftIO (getClockTime >>= toCalendarTime)
                  return $ formatCalendarTime defaultTimeLocale "%l:%M:%S %p" t
