module Tests.SharedTerm where

import Control.Monad
import Data.Hashable
import qualified Data.Map as Map
--import qualified Data.HashMap.Strict as HMap
import qualified Data.IntMap.Strict as HMap

import Data.Time.Clock
import Tests.Common

import Verifier.SAW.SharedTerm
import Verifier.SAW.Prelude


time :: String -> IO a -> IO a
time nm act = do
  putStrLn $ "Starting " ++ nm
  t0 <- getCurrentTime
  r <- act
  t1 <- getCurrentTime
  let d = t1 `diffUTCTime` t0
  putStrLn $ "Finished " ++ nm ++ ": " ++ show d
  return r

sharedTermTests :: [TestCase]
sharedTermTests =
  [ preludeSharedSmokeTest
  , mkTestCase "ppSharedTest" $ monadicIO $ run $ do
      sc <- mkSharedContext preludeModule
      bool <- scPreludeBool sc
      and <- scApplyPreludeAnd sc
      let rec x = and x x
      let rep f i x
            | i > 0 = rep f (i-1) =<< f x
            | otherwise = return x
      x <- time "Rep" $ do
        x0 <- scFreshGlobal sc "x" bool
        let cnt = 4000
        r <- rep rec cnt x0
        seq r $ return r
      time "Hash" $ do
        putStrLn $ "Hash " ++ show (hash x)
      time "Count" $ do
        let n0 = scTermCount x
        putStrLn $ "Count " ++ show (HMap.size n0)
      time "Length" $ do
        let n = length $ show $ scPrettyTermDoc x
        putStrLn $ "Length " ++ show n
      return ()
  ]

preludeSharedSmokeTest :: TestCase
preludeSharedSmokeTest =
  mkTestCase "preludeSharedSmokeTest" $ monadicIO $ run $ do
    sc <- mkSharedContext preludeModule
    void $ scPreludeBool sc
    return ()
