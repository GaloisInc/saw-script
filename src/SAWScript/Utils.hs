{-# LANGUAGE CPP #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE ScopedTypeVariables #-}
{- |
Module      : $Header$
Description : Miscellaneous utilities.
Maintainer  : jhendrix, atomb
Stability   : provisional
-}

{-# LANGUAGE DeriveDataTypeable  #-}
module SAWScript.Utils where

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative
import Data.Traversable (traverse)
#endif
import Control.Exception as CE
import Control.Monad.State
import Control.Monad.Trans.Except
import Control.DeepSeq(rnf, NFData(..))
import Data.List(intercalate)
import Data.Char(isSpace)
import Data.Data
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Ratio
import Data.Time.Clock
import System.Directory(makeRelativeToCurrentDirectory)
import System.FilePath(makeRelative, isAbsolute, (</>), takeDirectory)
import System.Time(TimeDiff(..), getClockTime, diffClockTimes, normalizeTimeDiff, toCalendarTime, formatCalendarTime)
import System.Locale(defaultTimeLocale)
import System.Exit
import Text.PrettyPrint.ANSI.Leijen hiding ((</>), (<$>))
import Text.Printf
import Numeric(showFFloat)

import qualified Verifier.Java.Codebase as JSS

import SAWScript.Options
import Verifier.SAW.Conversion
import Verifier.SAW.Rewriter
import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedAST

data Pos = Range !FilePath -- file
                 !Int !Int -- start line, col
                 !Int !Int -- end line, col
         | Unknown
         | PosInternal String
         | PosREPL
  deriving (Eq)

renderDoc :: Doc -> String
renderDoc doc = displayS (renderPretty 0.8 80 doc) ""

endPos :: FilePath -> Pos
endPos f = Range f 0 0 0 0

fmtPos :: Pos -> String -> String
fmtPos p m = show p ++ ":\n" ++ m'
  where m' = intercalate "\n" . map ("  " ++) . lines $ m

spanPos :: Pos -> Pos -> Pos
spanPos (PosInternal str) _ = PosInternal str
spanPos PosREPL _ = PosREPL
spanPos _ (PosInternal str) = PosInternal str
spanPos _ PosREPL = PosREPL
spanPos Unknown p = p
spanPos p Unknown = p
spanPos (Range f sl sc el ec) (Range _ sl' sc' el' ec') =  Range f l c l' c'
  where
    (l, c) = minPos sl sc sl' sc'
    (l', c') = maxPos el ec el' ec'
    minPos l1 c1 l2 c2 | l1 < l2   = (l1, c1)
                       | l1 == l2  = (l1, min c1 c2)
                       | otherwise = (l2, c2)
    maxPos l1 c1 l2 c2 | l1 < l2   = (l2, c2)
                       | l1 == l2  = (l1, max c1 c2)
                       | otherwise = (l1, c1)

fmtPoss :: [Pos] -> String -> String
fmtPoss [] m = fmtPos (PosInternal "saw-script internal") m
fmtPoss ps m = "[" ++ intercalate ",\n " (map show ps) ++ "]:\n" ++ m'
  where m' = intercalate "\n" . map ("  " ++) . lines $ m

posRelativeToCurrentDirectory :: Pos -> IO Pos
posRelativeToCurrentDirectory (Range f sl sc el ec) = makeRelativeToCurrentDirectory f >>= \f' -> return (Range f' sl sc el ec)
posRelativeToCurrentDirectory Unknown               = return Unknown
posRelativeToCurrentDirectory (PosInternal s)       = return $ PosInternal s
posRelativeToCurrentDirectory PosREPL               = return PosREPL

posRelativeTo :: FilePath -> Pos -> Pos
posRelativeTo d (Range f sl sc el ec) = Range (makeRelative d f) sl sc el ec
posRelativeTo _ Unknown               = Unknown
posRelativeTo _ (PosInternal s)       = PosInternal s
posRelativeTo _ PosREPL               = PosREPL

routePathThroughPos :: Pos -> FilePath -> FilePath
routePathThroughPos (Range f _ _ _ _) fp
  | isAbsolute fp = fp
  | True          = takeDirectory f </> fp
routePathThroughPos _ fp = fp

instance Show Pos where
  -- show (Pos f 0 0)           = f ++ ":end-of-file"
  -- show (Pos f l c)           = f ++ ":" ++ show l ++ ":" ++ show c
  show (Range f 0 0 0 0) = f ++ ":end-of-file"
  show (Range f sl sc el ec) = f ++ ":" ++ show sl ++ ":" ++ show sc ++ "-" ++ show el ++ ":" ++ show ec
  show Unknown               = "unknown"
  show (PosInternal s)       = "[internal:" ++ s ++ "]"
  show PosREPL               = "REPL"

class Positioned a where
  getPos :: a -> Pos

instance Positioned Pos where
  getPos p = p

maxSpan :: (Functor t, Foldable t, Positioned a) => t a -> Pos
maxSpan xs = foldr spanPos Unknown (fmap getPos xs)

data SSMode = Verify | Blif | CBlif deriving (Eq, Show, Data, Typeable)

-- | Convert a string to a paragraph formatted document.
ftext :: String -> Doc
ftext msg = fillSep (map text $ words msg)

-- | Insert multiple keys that map to the same value in a map.
mapInsertKeys :: Ord k => [k] -> a -> Map k a -> Map k a
mapInsertKeys keys val m = foldr (\i -> Map.insert i val) m keys

-- | Returns the value bound to the first key in the map, or
-- Nothing if none of the keys are in the map.
mapLookupAny :: Ord k => [k] -> Map k a -> Maybe a
mapLookupAny keys m = listToMaybe $ catMaybes $ map (\k -> Map.lookup k m) keys

-- ExecException {{{1

-- | Class of exceptions thrown by SBV parser.
data ExecException = ExecException Pos          -- Position
                                   Doc          -- Error message
                                   String       -- Resolution tip
  deriving (Show, Typeable)

instance Exception ExecException

-- | Throw exec exception in a MonadIO.
throwIOExecException :: MonadIO m => Pos -> Doc -> String -> m a
throwIOExecException site errorMsg resolution = liftIO $ throwIO (ExecException site errorMsg resolution)

-- | Throw exec exception in a MonadIO.
throwExecException :: Pos -> Doc -> String -> m a
throwExecException site errorMsg resolution = throw (ExecException site errorMsg resolution)

-- Timing {{{1

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

showDuration :: NominalDiffTime -> String
showDuration n = printf "%02d:%s" m (show s)
  where s = n - (fromIntegral m * 60)
        m :: Int
        m = floor ((toRational n) * (1 % 60))

-- Java lookup functions {{{1

-- | Atempt to find class with given name, or throw ExecException if no class
-- with that name exists. Class name should be in slash-separated form.
lookupClass :: JSS.Codebase -> Pos -> String -> IO JSS.Class
lookupClass cb site nm = do
  maybeCl <- JSS.tryLookupClass cb nm
  case maybeCl of
    Nothing -> do
     let msg = ftext ("The Java class " ++ JSS.slashesToDots nm ++ " could not be found.")
         res = "Please check that the --classpath and --jars options are set correctly."
      in throwIOExecException site msg res
    Just cl -> return cl

-- | Returns method with given name in this class or one of its subclasses.
-- Throws an ExecException if method could not be found or is ambiguous.
findMethod :: JSS.Codebase -> Pos -> String -> JSS.Class -> IO (JSS.Class, JSS.Method)
findMethod cb site nm initClass = impl initClass
  where javaClassName = JSS.slashesToDots (JSS.className initClass)
        methodMatches m = JSS.methodName m == nm && not (JSS.methodIsAbstract m)
        impl cl =
          case filter methodMatches (JSS.classMethods cl) of
            [] -> do
              case JSS.superClass cl of
                Nothing ->
                  let msg = ftext $ "Could not find method " ++ nm
                              ++ " in class " ++ javaClassName ++ "."
                      res = "Please check that the class and method are correct."
                   in throwIOExecException site msg res
                Just superName ->
                  impl =<< lookupClass cb site superName
            [method] -> return (cl,method)
            _ -> let msg = "The method " ++ nm ++ " in class " ++ javaClassName
                             ++ " is ambiguous.  SAWScript currently requires that "
                             ++ "method names are unique."
                     res = "Please rename the Java method so that it is unique."
                  in throwIOExecException site (ftext msg) res

throwFieldNotFound :: JSS.Type -> String -> ExceptT String IO a
throwFieldNotFound tp fieldName = throwE msg
  where
    msg = "Values with type \'" ++ show tp ++
          "\' do not contain field named " ++
          fieldName ++ "."

findField :: JSS.Codebase -> Pos -> JSS.Type -> String -> ExceptT String IO JSS.FieldId
findField _  _ tp@(JSS.ArrayType _) nm = throwFieldNotFound tp nm
findField cb site tp@(JSS.ClassType clName) nm = impl =<< lift (lookupClass cb site clName)
  where
    impl cl =
      case filter (\f -> JSS.fieldName f == nm) $ JSS.classFields cl of
        [] -> do
          case JSS.superClass cl of
            Nothing -> throwFieldNotFound tp nm
            Just superName -> impl =<< lift (lookupClass cb site superName)
        [f] -> return $ JSS.FieldId (JSS.className cl) nm (JSS.fieldType f)
        _ -> throwE $
             "internal: Found multiple fields with the same name: " ++ nm
findField _ _ _ _ =
  throwE "Primitive types cannot be dereferenced."

defRewrites :: SharedContext -> Ident -> IO [RewriteRule]
defRewrites sc ident =
      case findDef (scModule sc) ident of
        Nothing -> return []
        Just def -> scDefRewriteRules sc def

basic_ss :: SharedContext -> IO Simpset
basic_ss sc = do
  rs1 <- concat <$> traverse (defRewrites sc) (defs ++ defs')
  rs2 <- scEqsRewriteRules sc eqs
  return $ addConvs procs (addRules (rs1 ++ rs2) emptySimpset)
  where
    eqs = map (mkIdent preludeName)
      [ "unsafeCoerce_same"
      , "not_not"
      , "true_implies"
      , "and_True"
      , "and_False"
      , "and_True2"
      , "and_False2"
      , "and_idem"
      , "or_True"
      , "or_False"
      , "or_True2"
      , "or_False2"
      , "or_idem"
      , "not_or"
      , "not_and"
      , "ite_not"
      , "ite_nest1"
      , "ite_nest2"
      , "ite_fold_not"
      , "ite_eq"
      , "ite_true"
      , "ite_false"
      , "or_triv1"
      , "and_triv1"
      , "or_triv2"
      , "and_triv2"
      , "eq_refl"
      , "bvAddZeroL"
      , "bvAddZeroR"
      , "bveq_sameL"
      , "bveq_sameR"
      , "bveq_same2"
      , "bvNat_bvToNat"
      ]
    defs = map (mkIdent preludeName)
      [ "not", "and", "or", "xor", "boolEq", "ite", "addNat", "mulNat", "implies"
      , "compareNat", "equalNat"
      , "bitvector"
      ]
    defs' = map (mkIdent (mkModuleName ["Cryptol"]))
            ["seq", "ecEq", "ecNotEq"]
    procs = [tupleConversion, recordConversion] ++
            bvConversions ++ natConversions ++ vecConversions

-- | Convert a non-negative integer to to an ordinal string.
--
-- Note: @0 -> "0th"@, so do @'ordinal' (n + 1)@ if you want one-based
-- results.
ordinal :: (Integral a, Show a) => a -> String
-- Not sure what to do with negative integers so bail.
ordinal n | n < 0 = error "Only non-negative cardinals are supported."
          | otherwise = show n ++ suffix
  where
    suffix =
      if inTens then "th"
      else case n `mod` 10 of
             1 -> "st"
             2 -> "nd"
             3 -> "rd"
             _ -> "th"
    inTens = (n `mod` 100) `div` 10 == 1

handleException :: Options -> CE.SomeException -> IO a
handleException opts e
    | Just (_ :: ExitCode) <- CE.fromException e = CE.throw e
    | otherwise = printOutLn opts Error (CE.displayException e) >> exitProofUnknown

exitProofFalse,exitProofUnknown,exitProofSuccess :: IO a
exitProofFalse = exitWith (ExitFailure 1)
exitProofUnknown = exitWith (ExitFailure 2)
exitProofSuccess = exitSuccess
