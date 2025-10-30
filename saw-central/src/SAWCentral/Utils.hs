{- |
Module      : SAWCentral.Utils
Description : Miscellaneous utilities.
Maintainer  : jhendrix, atomb
Stability   : provisional
-}

{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

module SAWCentral.Utils where

import Control.Exception as CE
import Control.Monad.State
import Control.Monad.Trans.Except
import Control.DeepSeq(rnf, NFData(..))
import Data.Char(isSpace)
import Data.Data
import Data.Function (on)
import Data.List (sortBy)
import qualified Data.List.NonEmpty as NE
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe
import Data.Ratio
import Data.Time.Clock
import Data.Void
import Prettyprinter as PP
import System.Time(TimeDiff(..), getClockTime, diffClockTimes, normalizeTimeDiff, toCalendarTime, formatCalendarTime)
import System.Locale(defaultTimeLocale)
import qualified System.IO.Error as IOE
import System.Exit
import Text.Printf
import Numeric(showFFloat)

import qualified Lang.JVM.Codebase as JSS

import SAWCentral.Options
import SAWCentral.Position

bullets :: Char -> [PP.Doc ann] -> PP.Doc ann
bullets c = PP.vcat . map (PP.hang 2 . (PP.pretty c PP.<+>))

data SSMode = Verify | Blif | CBlif deriving (Eq, Show, Data, Typeable)

-- | Convert a string to a paragraph formatted document.
ftext :: String -> Doc ann
ftext msg = fillSep (map pretty $ words msg)

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
                                   (Doc Void)   -- Error message
                                   String       -- Resolution tip
  deriving (Show, Typeable)

instance Exception ExecException

-- | Throw exec exception in a MonadIO.
throwIOExecException :: MonadIO m => Pos -> Doc Void -> String -> m a
throwIOExecException site errorMsg resolution = liftIO $ throwIO (ExecException site errorMsg resolution)

-- | Throw exec exception in a MonadIO.
throwExecException :: Pos -> Doc Void -> String -> m a
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
lookupClass :: JSS.Codebase -> Pos -> JSS.ClassName -> IO JSS.Class
lookupClass cb site nm = do
  maybeCl <- JSS.tryLookupClass cb nm
  case maybeCl of
    Nothing -> do
     let msg = ftext ("The Java class " ++ JSS.slashesToDots (JSS.unClassName nm) ++ " could not be found.")
         res = unwords [ "Please check that the path to Java is set correctly"
                       , "(either through the --java-bin-dirs option or your PATH)"
                       , "and you are using Java 8 or earlier"
                       , "(SAW does not support 9+ currently)."
                       ]
      in throwIOExecException site msg res
    Just cl -> return cl

-- | Returns method with given name in this class or one of its subclasses.
-- Throws an ExecException if method could not be found or is ambiguous.
findMethod :: JSS.Codebase -> Pos -> String -> JSS.Class -> IO (JSS.Class, JSS.Method)
findMethod cb site nm initClass = impl [] initClass
  where javaClassName = JSS.slashesToDots (JSS.unClassName (JSS.className initClass))
        methodType m = (JSS.methodParameterTypes m, JSS.methodReturnType m)
        baseName m = JSS.methodName m
        typedName m = JSS.methodName m ++ ":" ++ unparseMethodDescriptor (methodType m)
        methodMatches m = nm `elem` [baseName m, typedName m]
        impl names cl =
          let candidates = filter (not . JSS.methodIsAbstract) (JSS.classMethods cl) in
          case filter methodMatches candidates of
            [] -> do
              case JSS.superClass cl of
                Nothing ->
                  let msg = ftext $ "Could not find method " ++ nm
                              ++ " in class " ++ javaClassName ++ ".\n"
                              ++ "Available methods: "
                              ++ unlines names
                      res = "Please check that the class and method are correct."
                   in throwIOExecException site msg res
                Just superName ->
                  do super <- lookupClass cb site superName
                     impl (names ++ map baseName candidates) super
            [method] -> return (cl,method)
            l -> let msg = "The method " ++ show nm ++ " in class " ++ javaClassName ++ " is ambiguous. " ++
                           "Methods can be disambiguated by appending a type descriptor: " ++
                           unlines [ show (typedName m) | m <- l ]
                     res = "Please disambiguate method name."
                  in throwIOExecException site (ftext msg) res

throwFieldNotFound :: JSS.Type -> String -> [String] -> ExceptT String IO a
throwFieldNotFound tp fieldName names = throwE msg
  where
    msg = "Values with type \'" ++ show tp ++
          "\' do not contain field named " ++
          fieldName ++ "."
          ++ "\nAvailable fields:\n" ++ unlines names

findField :: JSS.Codebase -> Pos -> JSS.Type -> String -> ExceptT String IO JSS.FieldId
findField _  _ tp@(JSS.ArrayType _) nm = throwFieldNotFound tp nm []
findField cb site tp@(JSS.ClassType clName) nm = impl [] =<< lift (lookupClass cb site clName)
  where
    impl nms cl =
      case filter (\f -> nm `elem` names f) $ JSS.classFields cl of
        [] -> do
          case JSS.superClass cl of
            Nothing -> throwFieldNotFound tp nm nms
            Just superName ->
              do super <- lift $ lookupClass cb site superName
                 impl (nms ++ map JSS.fieldName (JSS.classFields cl)) super
        [f] -> return $ JSS.FieldId (JSS.className cl) (JSS.fieldName f) (JSS.fieldType f)
        _ -> throwE $
             "internal: Found multiple fields with the same name: " ++ nm
      where
        names f =
          do prefix <- ["", JSS.unClassName (JSS.className cl) ++ "."]
             suffix <- ["", ":" ++ unparseTypeDescriptor (JSS.fieldType f)]
             pure (prefix ++ JSS.fieldName f ++ suffix)

findField _ _ _ _ =
  throwE "Primitive types cannot be dereferenced."


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
    | Just ioe <- CE.fromException e =
         printOutLn opts Error (displayIOE ioe) >> exitProofUnknown
    | otherwise =
         printOutLn opts Error (CE.displayException e) >> exitProofUnknown

 where
 displayIOE ioe
   | IOE.isUserError ioe = IOE.ioeGetErrorString ioe
   | otherwise = CE.displayException ioe

exitProofFalse,exitProofUnknown,exitProofSuccess :: IO a
exitProofFalse = exitWith (ExitFailure 1)
exitProofUnknown = exitWith (ExitFailure 2)
exitProofSuccess = exitSuccess

--------------------------------------------------------------------------------

unparseTypeDescriptor :: JSS.Type -> String
unparseTypeDescriptor =
  \case
    JSS.ArrayType ty -> "[" ++ unparseTypeDescriptor ty
    JSS.BooleanType  -> "Z"
    JSS.ByteType     -> "B"
    JSS.CharType     -> "C"
    JSS.ClassType cn -> "L" ++ JSS.unClassName cn ++ ";"
    JSS.DoubleType   -> "D"
    JSS.FloatType    -> "F"
    JSS.IntType      -> "I"
    JSS.LongType     -> "J"
    JSS.ShortType    -> "S"

unparseMethodDescriptor :: ([JSS.Type], Maybe JSS.Type) -> String
unparseMethodDescriptor (args, ret) =
  "(" ++ concatMap unparseTypeDescriptor args ++ ")" ++
  maybe "V" unparseTypeDescriptor ret


neGroupOn ::
  Ord b =>
  (a -> b) {- ^ equivalence class projection -} ->
  [a] -> [NE.NonEmpty a]
neGroupOn f = NE.groupBy ((==) `on` f) . sortBy (compare `on` f)

neNubOrd ::
  Ord a =>
  NE.NonEmpty a ->
  NE.NonEmpty a
neNubOrd (hd NE.:| tl) = hd NE.:| loop (Set.singleton hd) tl
  where
    loop _prev [] = []
    loop prev (x:xs)
      | Set.member x prev = loop prev xs
      | otherwise         = x : loop (Set.insert x prev) xs
