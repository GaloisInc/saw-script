module Stack (Stack, emptyStack, push, pop, fromList) where

import Data.Bits (xor)
import Data.Hashable (Hashable (..))
import Text.Printf (printf)

data Stack a = Stack {stackElems :: [a], stackHash :: Int}
  deriving (Eq)

instance Show a => Show (Stack a) where
  show Stack {..} =
    printf "Stack {stackElems = %s, stackHash = %x}" (show stackElems) stackHash

instance Eq a => Hashable (Stack a) where
  hashWithSalt salt Stack {..} = salt `hashWithSalt` stackHash
  hash Stack {..} = stackHash

push :: Hashable a => a -> Stack a -> Stack a
push x Stack {..} =
  Stack
    { stackElems = x : stackElems,
      stackHash = stackHash `xor` hashStackElem x
    }

pop :: Hashable a => Stack a -> Maybe (a, Stack a)
pop Stack {..} =
  case stackElems of
    [] -> Nothing
    (x : xs) ->
      Just (x, Stack {stackElems = xs, stackHash = stackHash `xor` hashStackElem x})

emptyStack :: Stack a
emptyStack = Stack {stackElems = mempty, stackHash = 0xdeadbeef}

fromList :: (Foldable t, Hashable a) => t a -> Stack a
fromList = foldr push emptyStack

hashStackElem :: Hashable a => a -> Int
hashStackElem x =
  case hash x of
    0 -> 0xfacade
    nonzero -> nonzero
