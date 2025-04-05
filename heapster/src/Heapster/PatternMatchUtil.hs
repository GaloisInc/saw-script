-- | Pattern-matching utilities used within @heapster-saw@.
module Heapster.PatternMatchUtil
  ( expectLengthAtLeastOne
  , expectLengthAtLeastTwo
  ) where

import GHC.Stack

-- | Use this in places where you maintain the invariant that the list argument
-- has at least one element.
expectLengthAtLeastOne :: HasCallStack => [a] -> (a, [a])
expectLengthAtLeastOne (x:xs) = (x, xs)
expectLengthAtLeastOne [] = error "expectLengthAtLeastOne: Unexpected empty list"

-- | Use this in places where you maintain the invariant that the list argument
-- has at least two elements.
expectLengthAtLeastTwo :: HasCallStack => [a] -> (a, a, [a])
expectLengthAtLeastTwo (x1:x2:xs) = (x1, x2, xs)
expectLengthAtLeastTwo [_] = error "expectLengthAtLeastTwo: Unexpected singleton list"
expectLengthAtLeastTwo []  = error "expectLengthAtLeastTwo: Unexpected empty list"
