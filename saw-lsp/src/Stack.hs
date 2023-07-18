module Stack (Stack, emptyStack, push, pop, fromList, toList) where

import Data.Bits (xor)
import Data.Hashable (Hashable (..))
import Text.Printf (printf)

data Stack a = Stack {sElems :: [a], sSize :: Int, sHash :: Int}
  deriving (Eq)

instance Show a => Show (Stack a) where
  show Stack {..} =
    printf "Stack {sElems = %s, sSize = %i, sHash = 0x%x}" (show sElems) sSize sHash

instance Eq a => Hashable (Stack a) where
  hashWithSalt salt Stack {..} = salt `hashWithSalt` sHash
  hash Stack {..} = sHash

push :: Hashable a => a -> Stack a -> Stack a
push x Stack {..} =
  Stack
    { sElems = x : sElems,
      sSize = sSize + 1,
      sHash = sHash `xor` hashStackElem x `xor` hash (show sSize)
    }

pop :: Hashable a => Stack a -> Maybe (a, Stack a)
pop Stack {..} =
  case sElems of
    [] -> Nothing
    (x : xs) ->
      let sElems' = xs
          sSize' = sSize - 1
          sHash' = sHash `xor` hashStackElem x `xor` hash (show sSize')
       in Just (x, Stack {sElems = sElems', sSize = sSize', sHash = sHash'})

emptyStack :: Stack a
emptyStack = Stack {sElems = mempty, sSize = 0, sHash = 0xdeadbeef}

fromList :: (Foldable t, Hashable a) => t a -> Stack a
fromList = foldr push emptyStack

toList :: Stack a -> [a]
toList Stack {..} = sElems

hashStackElem :: Hashable a => a -> Int
hashStackElem x =
  case hash x of
    0 -> 0xfacade
    nonzero -> nonzero
