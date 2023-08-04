{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Test.Util.Stack where

import Control.Monad (replicateM)
import Data.Hashable (Hashable (hash))
import Test.QuickCheck (Arbitrary (..), Gen, chooseInt)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.QuickCheck (testProperty)
import Util.Stack as Stack

instance (Hashable a, Arbitrary a) => Arbitrary (Stack a) where
  -- \| Generate a nonempty stack
  arbitrary =
    do
      len <- chooseInt (1, 100)
      elems <- replicateM len arbitrary
      pure (Stack.fromList elems)

tests :: TestTree
tests =
  testGroup
    "Test.Util.Stack"
    [ testProperty "pushing then popping ints" (pushPop @Int),
      testProperty "pushing then popping chars" (pushPop @Char),
      testProperty "pushing then popping strings" (pushPop @String),
      testProperty "popping then pushing ints" (popPush @Int),
      testProperty "popping then pushing chars" (popPush @Char),
      testProperty "popping then pushing strings" (popPush @String)
    ]

pushPop :: (Arbitrary a, Hashable a) => Stack a -> Gen Bool
pushPop stack =
  do
    element <- arbitrary
    let h = hash stack
        stack' = push element stack
        Just (element', stack'') = pop stack'
        h'' = hash stack''
    pure (element == element' && h == h'')

popPush :: Hashable a => Stack a -> Bool
popPush stack =
  case pop stack of
    Nothing -> True
    Just (top, stack') ->
      let stack'' = push top stack'
          h = hash stack
          h'' = hash stack''
       in (h == h'')
