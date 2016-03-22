{- |
Module      : Verifier.SAW.Simulator.ANF.Base
Copyright   : Galois, Inc. 2016
License     : BSD3
Maintainer  : huffman@galois.com
Stability   : experimental
Portability : portable

Boolean Formulas in Algebraic Normal Form.
-}

module Verifier.SAW.Simulator.ANF.Base
  ( ANF
  , true, false, lit
  , constant, isBool
  , compl, xor, conj, disj, iff, mux
  , eval
  , sat, allsat
  , degree
  , depth, size
  , explode
  ) where

-- | Boolean formulas in Algebraic Normal Form, using a representation
-- based on the Reed-Muller expansion. Invariants: The last argument
-- to a `Node` constructor should never be `A0`. Also the `Int`
-- arguments should strictly increase as you go deeper in the tree.

data ANF = Node !Int !ANF !ANF | A0 | A1
  deriving (Eq, Show)

-- | Evaluate formula with given variable assignment
eval :: ANF -> (Int -> Bool) -> Bool
eval anf v =
  case anf of
    A0 -> False
    A1 -> True
    Node n a b -> (eval a v) /= (v n && eval b v)

-- | Normalizing constructor
node :: Int -> ANF -> ANF -> ANF
node _ a A0 = a
node n a b = Node n a b

-- | Constant true formula
true :: ANF
true = A1

-- | Constant false formula
false :: ANF
false = A0

-- | Boolean constant formulas
constant :: Bool -> ANF
constant False = false
constant True = true

isBool :: ANF -> Maybe Bool
isBool A0 = Just False
isBool A1 = Just True
isBool _ = Nothing

-- | Boolean literals
lit :: Int -> ANF
lit n = Node n A0 A1

-- | Logical complement
compl :: ANF -> ANF
compl A0 = A1
compl A1 = A0
compl (Node n a b) = Node n (compl a) b

-- | Logical exclusive-or
xor :: ANF -> ANF -> ANF
xor A0 y = y
xor A1 y = compl y
xor x A0 = x
xor x A1 = compl x
xor x@(Node i a b) y@(Node j c d)
  | i < j = Node i (xor a y) b
  | j < i = Node j (xor x c) d
  | otherwise = node i (xor a c) (xor b d)

-- | Logical conjunction
conj :: ANF -> ANF -> ANF
conj A0 _ = A0
conj A1 y = y
conj _ A0 = A0
conj x A1 = x
conj x@(Node i a b) y@(Node j c d)
  | i < j = node i (conj a y) (conj b y)
  | j < i = node j (conj x c) (conj x d)
  | otherwise = node i ac (xor ac (conj (xor a b) (xor c d)))
  where ac = conj a c

-- | Logical disjunction
disj :: ANF -> ANF -> ANF
disj A0 y = y
disj A1 _ = A1
disj x A0 = x
disj _ A1 = A1
disj x@(Node i a b) y@(Node j c d)
  | i < j = node i (disj a y) (conj b (compl y))
  | j < i = node j (disj x c) (conj (compl x) d)
  | otherwise = node i ac (xor ac (disj (xor a b) (xor c d)))
  where ac = disj a c

-- | Logical equivalence
iff :: ANF -> ANF -> ANF
iff x y = xor (compl x) y
{-
iff A0 y = compl y
iff A1 y = y
iff x A0 = compl x
iff x A1 = x
iff x@(Node i a b) y@(Node j c d)
  | i < j = Node i (iff a y) b
  | j < i = Node j (iff x c) d
  | otherwise = node i (iff a c) (xor b d)
-}

-- | Logical if-then-else
mux :: ANF -> ANF -> ANF -> ANF
--mux w x y = xor (conj w x) (conj (compl w) y)
mux A0 _ y = y
mux A1 x _ = x
mux b x y = xor (conj b (xor x y)) y

{-
mux A0 x y = y
mux A1 x y = x
mux w A0 y = conj (compl w) y
mux w A1 y = disj w y
mux w x A0 = conj w x
mux w x A1 = disj (compl w) x
mux w@(Node i a b) x@(Node j c d) y@(Node k e f)
  | i < j && i < k = node i (mux a x y) (conj b (xor x y))
  | j < i && j < k = node i (mux w c y) (conj w d)
  | k < i && k < j = node i (mux w x e) (conj (compl w) f)
  | i == j && i < k = node i (mux a c y) _
-}

-- | Satisfiability checker
sat :: ANF -> Maybe [(Int, Bool)]
sat A0 = Nothing
sat A1 = Just []
sat (Node n a b) =
  case sat a of
    Just xs -> Just ((n, False) : xs)
    Nothing -> fmap ((n, True) :) (sat b)

-- | List of all satisfying assignments
allsat :: ANF -> [[(Int, Bool)]]
allsat A0 = []
allsat A1 = [[]]
allsat (Node n a b) =
  map ((n, False) :) (allsat a) ++ map ((n, True) :) (allsat (xor a b))

-- | Maximum polynomial degree
degree :: ANF -> Int
degree A0 = 0
degree A1 = 0
degree (Node _ a b) = max (degree a) (1 + degree b)

-- | Tree depth
depth :: ANF -> Int
depth A0 = 0
depth A1 = 0
depth (Node _ a b) = 1 + max (depth a) (depth b)

-- | Tree size
size :: ANF -> Int
size A0 = 1
size A1 = 1
size (Node _ a b) = 1 + size a + size b

-- | Convert to an explicit polynomial representation
explode :: ANF -> [[Int]]
explode A0 = []
explode A1 = [[]]
explode (Node i a b) = explode a ++ map (i:) (explode b)
