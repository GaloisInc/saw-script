{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}

{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}

module SAWScript.Unify.Tests where

import SAWScript.Unify

import Control.Monad
import Control.Applicative

import Data.List
import Data.Maybe
import qualified Data.Foldable as F
import qualified Data.Traversable as T

import Debug.Trace

-- Arithmetic {{{

data I a   = I Int   deriving (Show,Functor,F.Foldable,T.Traversable)
data Add a = Add a a deriving (Show,Functor,F.Foldable,T.Traversable)
data Mul a = Mul a a deriving (Show,Functor,F.Foldable,T.Traversable)

instance Equal I where
  equal (I x) (I y) = x == y
instance Equal Add where
  equal (Add x1 y1) (Add x2 y2) = x1 == x2 && y1 == y2
instance Equal Mul where
  equal (Mul x1 y1) (Mul x2 y2) = x1 == x2 && y1 == y2

instance Render I where
  render (I x) = show x
instance Render Add where
  render (Add x y) = "(" ++ show x ++ " + " ++ show y ++ ")"
instance Render Mul where
  render (Mul x y) = "(" ++ show x ++ " * " ++ show y ++ ")"

instance Uni I where
  uni (I x) (I y) = fail ("I: " ++ show x ++ " =/= " ++ show y)
instance Uni Add where
  uni (Add x1 y1) (Add x2 y2) = unify x1 x2 >> unify y1 y2
instance Uni Mul where
  uni (Mul x1 y1) (Mul x2 y2) = unify x1 x2 >> unify y1 y2

i :: (I :<: f) => Int -> Mu f
i x = inject $ I x
add :: (Add :<: f) => Mu f -> Mu f -> Mu f
add x y = inject $ Add x y
mul :: (Mul :<: f) => Mu f -> Mu f -> Mu f
mul x y = inject $ Mul x y

type LArith = Mu (I :+: Add :+: Mul :+: Logic)

testArith1 :: Results LArith
testArith1 = run Nothing Nothing $ \q -> do
  fresh $ \x y -> do
    x === y

testArith2 :: Results LArith
testArith2 = run Nothing Nothing $ \q -> do
  fresh $ \x y z -> do
    y === add x (i 2)
    x === (i 3)
    q === mul z y

testArith3 :: Results (Subst LArith)
testArith3 = runS Nothing Nothing $ \q -> do
  fresh $ \x y -> do
    y === add x (i 2)
    q === mul x y

-- }}}

-- Set {{{

data Set a = Set [a] deriving (Show,Functor,F.Foldable,T.Traversable)

instance Equal Set where
  equal (Set xs1) (Set xs2) = and $ zipWith (==) xs1 xs2

instance Render Set where
  render (Set xs) = "{" ++ (intercalate "," $ map show xs) ++ "}"

-- FIXME: remove overlapping cases
instance Uni Set where
  uni (Set xs) (Set ys) =
    let gx = filter (not . isJust . isVar) xs
        gy = filter (not . isJust . isVar) ys in do
      conj [ conj [ disj [ unify x y | y <- ys ] | x <- gx ]
           , conj [ disj [ unify y x | x <- xs ] | y <- gy ]
           ]
  wkS (Set xs) = do
    xs' <- mapM walkStar xs
    return (Set $ nub xs')
      
--set :: (Set :<: f) => [Mu f] -> Mu f
--set xs = inject $ Set xs

mkSet :: (Render f, Unifiable f, Set :<: f) => [Mu f] -> GoalM (Mu f) (Mu f)
mkSet xs = do
  xs' <- mapM walkStar xs
  let vs = filter (isJust . isVar) xs'
  msum (return (inject $ Set xs') :
        [ do unify v x
             xsFinal <- nub <$> mapM walkStar xs'
             return (inject $ Set xsFinal)
          | v <- vs, x <- xs', v /= x
        ])

-- }}}

-- List {{{

instance Equal [] where
  equal l1 l2 = case (l1,l2) of
    ([],[])       -> True
    (x:l1',y:l2') -> x == y && equal l1' l2'
    _             -> False

instance Render [] where
  render l = "[" ++ (intercalate "," $ map show l) ++ "]"

-- uni only has to be defined for cases where the two values are not directly equal (as in 'unify [] []')
instance Uni [] where
  uni (x:xs) (y:ys) = unify x y >> uni xs ys

list :: ([] :<: f) => [Mu f] -> Mu f
list xs = inject $ xs

-- }}}

-- Val {{{

data Val t a = Val t deriving (Eq,Show,Functor,F.Foldable,T.Traversable)

instance Eq t => Equal (Val t) where
  equal (Val x) (Val y) = x == y
instance Show t => Render (Val t) where
  render (Val x) = show x
instance (Show t, Eq t) => Uni (Val t) where
  uni (Val x) (Val y) = fail ("Val: " ++ show x ++ " =/= " ++ show y)

val :: (Val t :<: f) => t -> Mu f
val x = inject $ Val x

int :: (Val Int :<: f) => Int -> Mu f
int x = inject $ Val x

str :: (Val String :<: f) => String -> Mu f
str x = inject $ Val x

char :: (Val Char :<: f) => Char -> Mu f
char x = inject $ Val x

-- }}}

type CLIST = Mu (Logic :+: I :+: Cons :+: Nil)

-- Cons, Null {{{

data Cons a = Cons a a deriving (Show,Functor,F.Foldable,T.Traversable)

instance Equal Cons where
  equal (Cons a1 d1) (Cons a2 d2) = a1 == a2 && d1 == d2

instance Render Cons where
  render (Cons a d) = "(" ++ show a ++ " . " ++ show d ++ ")"

instance Uni Cons where
  uni (Cons x1 y1) (Cons x2 y2) = unify x1 x2 >> unify y1 y2

data Nil a = Nil deriving (Show,Functor,F.Foldable,T.Traversable)

instance Equal Nil where
  equal Nil Nil = True
  
instance Render Nil where
  render Nil = "()"

instance Uni Nil where
  uni x y = fail ("Nil: " ++ show x ++ " /= " ++ show y)

cons :: (Cons :<: f) => Mu f -> Mu f -> Mu f
cons a d = inject $ Cons a d

nil :: (Nil :<: f) => Mu f
nil = inject Nil

-- }}}

-- MK ops {{{

clist :: (Cons :<: f, Nil :<: f) => [Mu f] -> Mu f
clist = foldr cons nil

appendo :: (Unifiable f, Cons :<: f, Nil :<: f) => Mu f -> Mu f -> Mu f -> Goal (Mu f)
appendo l s ls = disj
  [ do l === nil
       s === ls
  , fresh $ \a d res -> do
      cons a d === l
      cons a res === ls
      appendo d s res
  ]

membero :: (Unifiable f, Cons :<: f, Nil :<: f) => Mu f -> Mu f -> Goal (Mu f)
membero x l = fresh $ \a d -> do
  l === cons a d
  disj [ a === x
       , membero x d
       ]

rembero :: (Unifiable f, Cons :<: f, Nil :<: f) => Mu f -> Mu f -> Mu f -> Goal (Mu f)
rembero x l out = disj
  [ do l === nil
       out === nil
  , fresh $ \d -> do
      l === cons x d
      out === d
  , fresh $ \a d res -> do
      l === cons a d
      rembero x d res
      out === cons a res
  ]

nevero :: (Unifiable f) => Goal (Mu f)
nevero = anyo (fail "nevero")

alwayso :: (Unifiable f) => Goal (Mu f)
alwayso = anyo succeed

-- }}}

-- Oleg Numbers {{{

buildNum :: (Unifiable f, Cons :<: f, Nil :<: f, I :<: f) => Int -> Mu f
buildNum n
  | n == 0    = nil
  | odd n     = cons (i 1) $ buildNum $ quot (n-1) 2
  | otherwise = cons (i 0) $ buildNum $ quot n 2

poso :: (Unifiable f, Cons :<: f, Nil :<: f, I :<: f) => Mu f -> Goal (Mu f)
poso n = fresh $ \a d -> n === cons a d

greaterThanOneo :: (Unifiable f, Cons :<: f, Nil :<: f, I :<: f) => Mu f -> Goal (Mu f)
greaterThanOneo n = fresh $ \a ad dd -> n === cons a (cons ad dd)

fullAddero :: (Unifiable f, Cons :<: f, Nil :<: f, I :<: f) => Mu f -> Mu f -> Mu f -> Mu f -> Mu f -> Goal (Mu f)
fullAddero b x y r c = disj
  [ i 0 === b >> i 0 === x >> i 0 === y >> i 0 === r >> i 0 === c
  , i 1 === b >> i 0 === x >> i 0 === y >> i 1 === r >> i 0 === c
  , i 0 === b >> i 1 === x >> i 0 === y >> i 1 === r >> i 0 === c
  , i 1 === b >> i 1 === x >> i 0 === y >> i 0 === r >> i 1 === c
  , i 0 === b >> i 0 === x >> i 1 === y >> i 1 === r >> i 0 === c
  , i 1 === b >> i 0 === x >> i 1 === y >> i 0 === r >> i 1 === c
  , i 0 === b >> i 1 === x >> i 1 === y >> i 0 === r >> i 1 === c
  , i 1 === b >> i 1 === x >> i 1 === y >> i 1 === r >> i 1 === c
  ]

addero :: (Unifiable f, Cons :<: f, Nil :<: f, I :<: f) => Mu f -> Mu f -> Mu f -> Mu f -> Goal (Mu f)
addero d n m r = disj
 [ i 0 === d >> nil === m >> n === r
 , i 0 === d >> nil === n >> m === r >> poso m
 , i 1 === d >> nil === m >> addero (i 0) n (clist [i 1]) r
 , i 1 === d >> nil === n >> poso m >> addero (i 0) (clist [i 1]) m r
 , clist [i 1] === n >> clist [i 1] === m >> (fresh $ \a c -> clist [a,c] === r >> fullAddero d (i 1) (i 1) a c)
 , clist [i 1] === n >> genAddero d n m r
 , clist [i 1] === m >> greaterThanOneo n >> greaterThanOneo r >> addero d (clist [i 1]) n r
 , greaterThanOneo n >> genAddero d n m r
 ]

genAddero :: (Unifiable f, Cons :<: f, Nil :<: f, I :<: f) => Mu f -> Mu f -> Mu f -> Mu f -> Goal (Mu f)
genAddero d n m r = fresh $ \a b c e x y z -> do
  cons a x === n
  cons b y === m
  poso y
  cons c z === r
  poso z
  fullAddero d a b c e
  addero e x y z

pluso :: (Unifiable f, Cons :<: f, Nil :<: f, I :<: f) => Mu f -> Mu f -> Mu f -> Goal (Mu f)
pluso n m k = addero (i 0) n m k

type OLEG = Mu (I :+: Cons :+: Nil :+: Logic)

testPlus :: Results OLEG
testPlus = run Nothing Nothing $ \q ->
  fresh $ \x y -> do
    x === buildNum 10
    y === buildNum 10
    pluso x y q

testPlus2 :: Results OLEG
testPlus2 = run Nothing Nothing $ \q ->
  fresh $ \x y -> do
    x === buildNum 10
    y === buildNum 10
    q === buildNum 25
    pluso x y q

class Functor f => OlegNum f where
  toInt :: f Int -> Int 

instance (OlegNum f, OlegNum g) => OlegNum (f :+: g) where
  toInt cp = case cp of
    Inl e -> toInt e
    Inr e -> toInt e

instance OlegNum I where
  toInt (I x) = x

instance OlegNum Nil where
  toInt Nil = 0

instance OlegNum Cons where
  toInt (Cons a d) = a + (2*d)

instance OlegNum Logic where
  toInt _ = error "non-ground"

olegToInt :: (OlegNum f) => Mu f -> Int
olegToInt = foldMu toInt

-- }}}

type Base = Val Char :+: Val Int :+: [] :+: Logic
type MK = Mu (Val Char :+: Val Int :+: Cons :+: Nil :+: Logic)
type SET = Mu (Set :+: Base)

-- MK Tests {{{

testMK1 :: Results MK
testMK1 = run Nothing Nothing $ \q -> do
  fresh $ \x y -> do
    disj [ x === int 1
         , x === int 3
         ]
    disj [ y === int 2
         , y === int 4
         ]
    q === clist [x,y]

testMK2 :: Results MK
testMK2 = run Nothing (Just 10) $ \q -> do
  anyo (q === int 1)

testMK3 :: Results MK
testMK3 = run Nothing Nothing $ \q -> do
  onceo $ anyo $ q === int 1

testMK4 :: Results MK
testMK4 = run Nothing Nothing $ \q -> do
  char 'b' === int 3

testMK5 :: Results MK
testMK5 = run Nothing Nothing $ \q -> do
  q === clist [char 'b', int 3]

testMK6 :: Results MK
testMK6 = run Nothing Nothing $ \q -> do
  q === int 1
  q === int 2

-- }}}

-- SET Tests {{{

testSET1 :: Results SET
testSET1 = run Nothing Nothing $ \q -> do
  fresh $ \x y -> do
    x === int 1
    y === int 2
    s <- mkSet [x,y]
    q === s

testSET2 :: Results SET
testSET2 = run Nothing Nothing $ \q -> do
  fresh $ \w x y z -> do
    s1 <- mkSet [w,int 2]
    x === s1
    s2 <- mkSet [int 1,z]
    y === s2
    q === list [x,y]

testSET5 :: Results SET
testSET5 = run Nothing Nothing $ \q -> do
  fresh $ \w x y z -> do
    s1 <- mkSet [w,int 2]
    x === s1
    s2 <- mkSet [int 1,z]
    y === s2
    x === y
    q === list [x,y]

testSET6 :: Results SET
testSET6 = run Nothing Nothing $ \q -> do
  fresh $ \w x y z -> do
    s1 <- mkSet [w,int 2]
    x === s1
    s2 <- mkSet [z]
    y === s2
    x === y
    q === list [x,y]

testSET3 :: Results SET
testSET3 = run Nothing Nothing $ \q -> do
  fresh $ \w x y z -> do
    s1 <- mkSet [w,int 2]
    x === s1
    s2 <- mkSet [int 1,z]
    y === s2
    x === y
    q === list [x,y]

testSET4 :: Results SET
testSET4 = run Nothing Nothing $ \q -> do
  fresh $ \a b c d e -> do
    s1 <- mkSet [b,c,int 2]
    a === s1
    s2 <- mkSet [e,int 1]
    d === s2
    a === d
    q === list [a,d]

-- }}}

-- CLIST Tests {{{

testApp :: Results CLIST
testApp = run Nothing Nothing $ \q -> do
  fresh $ \l1 l2 w x y z -> do
    w === clist [i 1]
    x === clist [i 2]
    y === clist [i 3]
    z === clist [i 4]
    appendo w x l1
    appendo y z l2
    appendo l1 l2 q

testMem :: Results CLIST
testMem = run Nothing Nothing $ \q -> do
  fresh $ \l -> do
    l === clist [i 1, i 2, i 3]
    membero q l

testRem :: Results CLIST
testRem = run Nothing Nothing $ \q -> do
  fresh $ \x l -> do
    l === clist [i 1, i 2, i 3, i 4]
    rembero x l q

-- }}}

