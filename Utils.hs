{-# LANGUAGE DeriveDataTypeable  #-}
module SAWScript.Utils where

import Control.Exception
import Control.Monad(when)
import Data.List(intercalate)
import System.Console.CmdArgs(Data, Typeable)
import System.Directory(makeRelativeToCurrentDirectory)
import System.FilePath(makeRelative, isAbsolute, (</>), takeDirectory)
import Text.PrettyPrint.HughesPJ
import Utils.IOStateT

data Pos = Pos !FilePath -- file
               !Int      -- line
               !Int      -- col
         | PosInternal String

endPos :: FilePath -> Pos
endPos f = Pos f 0 0

fmtPos :: Pos -> String -> String
fmtPos p m = show p ++ ":\n" ++ m'
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
data ExecException = ExecException Pos -- ^ Position
                                   Doc -- ^ Error message
                                   String -- ^ Resolution tip
  deriving (Show, Typeable)

instance Exception ExecException

-- | Throw exec exception in a MonadIO.
throwIOExecException :: MonadIO m => Pos -> Doc -> String -> m a
throwIOExecException pos errorMsg resolution =
  liftIO $ throwIO (ExecException pos errorMsg resolution)
