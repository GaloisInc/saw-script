{-# LANGUAGE TypeApplications #-}

module Test.FList (tests) where

import Data.Hashable (Hashable)
import FList
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.QuickCheck (Gen, testProperty)

tests :: TestTree
tests =
  testGroup
    "Test.FList"
    [ testProperty "to-from involution" (toFrom @Int),
      testProperty "forward works" (testForward @Int),
      testProperty "backward works" (testBackward @Int),
      testProperty "before works" (testBefore @Int),
      testProperty "after works" (testAfter @Int),
      testProperty "fingers works" (testFingers @Int)
    ]

toFrom :: (Eq a, Hashable a) => [a] -> [a] -> Bool
toFrom xs ys =
  let (xs', ys') = toLists (fromLists xs ys)
   in xs == xs' && ys == ys'

testForward :: (Eq a, Hashable a) => [a] -> a -> Bool
testForward xs x =
  let flist = fromLists xs [x]
   in case forward flist of
        Nothing -> False
        Just flist' ->
          case toLeft flist' of
            Nothing -> False
            Just x' -> x == x'

testBackward :: (Eq a, Hashable a) => a -> [a] -> Bool
testBackward x xs =
  let flist = fromLists [x] xs
   in case backward flist of
        Nothing -> False
        Just flist' ->
          case toRight flist' of
            Nothing -> False
            Just x' -> x == x'

testBefore :: (Eq a, Hashable a) => [a] -> [a] -> Bool
testBefore xs ys =
  let flist = fromLists xs ys
   in xs == before flist

testAfter :: (Eq a, Hashable a) => [a] -> [a] -> Bool
testAfter xs ys =
  let flist = fromLists xs ys
   in ys == after flist

testFingers :: (Eq a, Hashable a) => [a] -> Bool
testFingers xs =
  let fingerSplits = [toLists flist | flist <- fingers xs]
      manualSplits = [splitAt n xs | n <- [0 .. length xs]]
   in fingerSplits == manualSplits
