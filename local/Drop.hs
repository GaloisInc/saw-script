{-# LANGUAGE LambdaCase #-}

module Drop where

import Test.QuickCheck

mydrop1 :: Int -> [a] -> [a]
mydrop1 n = foldr
              (\a as -> if n==0 then a:as else mydrop1 (n-1) as)
              []
  -- WRONG.

prop_eq1 n xs = mydrop1 n xs == drop n xs
prop_eq2 n xs = n >= 0 ==> (mydrop2 n xs == drop n xs)
prop_eq3 n xs = n >= 0 ==> (mydrop3 n xs == drop n xs)

-- prop_2 n xs = drop n xs ==

-- using nat_fold:
mydrop3 :: Int -> [a] -> [a]
mydrop3 n = nat_fold id (\f xs -> f (sfTail xs)) n

sfTail []     = []
sfTail (_:xs) = xs

nat_fold :: a -> (a -> a) -> Int -> a
nat_fold x f 0 = x
nat_fold x f n = f (nat_fold x f (n-1))

test1 n = nat_fold "" ('1':) n

-- using list foldr:
-- (with chatgpt help)
mydrop2 :: Int -> [a] -> [a]
mydrop2 n xs = foldr step base xs n
  where
    -- 'step' takes the current list element 'x' and the
    -- recursively folded function 'r', and returns a new
    -- function that expects "how many elements we still
    -- need to drop".
    step :: a -> (Int -> [a]) -> (Int -> [a])
    step x r k =
      case k of
        0        -> x : r 0    -- if we don't need to drop anymore, keep 'x'
        _        -> r (k - 1)  -- otherwise, drop 'x' and decrement k

    -- 'base' is the function used when the list is empty.
    -- No matter how many we still need to drop, we return [].
    base :: Int -> [a]
    base _ = []
