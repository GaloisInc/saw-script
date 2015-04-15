{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module SimpleTypechecker where

import Control.Applicative ((<$>))
import Control.Monad
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set

type Name = String
type Sort = Integer
type DeBruijnIndex = Int

newtype Zero = Zero ()
newtype Succ a = Succ a

data Term = Var DeBruijnIndex -- ^ Variable using deBruijn index
          | Set Sort

          | Pi Term Term
          | Lambda Term
          | App Term Term

            -- | A dependent named constructor.
            -- Terms may contain free variables that reference previous terms in the list.
          | Ctor Name [Term]

          | Sigma Term Term
          | Pair Term Term
          | Proj1 Term
          | Proj2 Term


          | UnitValue
          | UnitType

          -- TODO: Support arbitrary dependent tuples.
          -- | Sigma [Term]
          -- | Tuple  [Term]
          -- | Proj Integer Term
  deriving (Show)

-- | @termVarFn t s@ returns union of @s@ and free variables in @t@.
termVarFn :: Term -> Set DeBruijnIndex -> Set DeBruijnIndex
termVarFn = \t -> go [(0,t)]
  where go :: [(DeBruijnIndex,Term)] -> Set DeBruijnIndex -> Set DeBruijnIndex
        go [] s = s
        go ((i,t):r) s =
          case t of
             Var j | j >= i -> go r (Set.insert (j-i) s)
             Pi a b    -> go ((i,a):(i+1,b):r) s
             Lambda t  -> go ((i+1,t):r) s
             App a b   -> go ((i,a):(i,b):r) s
             Ctor _ l  -> go (zip [i..] l ++ r) s
             Sigma a b -> go ((i,a):(i+1,b):r) s
             Pair a b  -> go ((i,a):(i+1,b):r) s
             Proj1 a   -> go ((i,a):r) s
             Proj2 a   -> go ((i,a):r) s
             _ -> s

termVars :: Term -> Set DeBruijnIndex
termVars t = termVarFn t Set.empty

-- | A list structure that behinds the new element on the right.
-- This is isomophic to the standard list, but the right bind is used so that
-- context and other data types have a syntax that associates in the order used in
-- the literature.
data RList t
    = REmpty
    | RCons (RList t) t
  deriving (Eq, Ord, Functor)

type Telescope = RList Term

-- | Find variable type, lifting free variables in term so they refer to the
-- proper variables in the telescope.
findVarType :: Telescope -> DeBruijnIndex -> Maybe Term
findVarType te lvl = go te lvl
  where go REmpty _ = Nothing
        go (RCons g t) 0 = Just (incVarBy (lvl + 1) t)
        go (RCons g t) i = findVarType g (i-1)

-- | @instantiateVars f t@ substitutes each free variable @Var j@ with the
-- term @f i j@ where @i@ is the number of bound variables around @Var j@.
instantiateVars :: (DeBruijnIndex -> DeBruijnIndex -> Term) ->  Term -> Term
instantiateVars f = go 0
  where go i (Var j)     | j >= i = f i j
        go i (Pi a b)    = Pi     (go i a) (go (i+1) b)
        go i (Lambda a)  = Lambda (go (i+1) a)
        go i (App a b)   = App    (go i a) (go i b)
        go i (Ctor nm l) = Ctor nm (zipWith go [i..] l)
        go i (Sigma a b) = Sigma  (go i a) (go (i+1) b)
        go i (Pair a b)  = Pair   (go i a) (go (i+1) b)
        go i (Proj1 a)   = Proj1  (go i a)
        go i (Proj2 a)   = Proj2  (go i a)
        go _ s           = s

-- | Change the indices of free variables in a pattern.
renumberPatFreeVar :: (DeBruijnIndex -> DeBruijnIndex) -> Pat -> Pat
renumberPatFreeVar f = go
  where fn i j = Var (i + f (j - i))
        go (PVar i) = PVar (f i)
        go (PCtor nm l) = PCtor nm (go <$> l)
        go (PInaccessible t) = PInaccessible $ instantiateVars fn t

removeUnusedFreeVarFn :: DeBruijnIndex -> DeBruijnIndex -> DeBruijnIndex
removeUnusedFreeVarFn l i
  | l  < i = i - 1
  | l == i = error "internal: unexpected free variable referenced."
  | l  > i = i

removeUnusedTermFreeVar :: DeBruijnIndex -> Term -> Term
removeUnusedTermFreeVar l = instantiateVars fn
  where fn i j = Var (i + removeUnusedFreeVarFn l (j - i))

-- | @shiftlTermFreeVar l k t@ moves variable with index @l@ to index @k@.
shiftlTermFreeVar :: DeBruijnIndex -> DeBruijnIndex -> Term -> Term
shiftlTermFreeVar l k =
    case compare k l of
      LT -> instantiateVars h
      EQ -> id
      GT -> shiftlTermFreeVar k l
  where h i j | j == i + l              = Var (i + k)
              | i + k <= j && j < i + l = Var (j + 1)
              | otherwise               = Var j

-- | Increment all free variables by the given count.
incVarBy :: DeBruijnIndex -> Term -> Term
incVarBy 0 = id
incVarBy c = instantiateVars (\_ j -> Var (j+c))

-- | @instantantiateVar Substitute term with var index 0 and shift all remaining free variables.
instantiateVar :: DeBruijnIndex -> Term -> Term -> Term
instantiateVar k t = instantiateVars fn
  where -- Use terms to memoize instantiated versions of t.
        terms = [ incVarBy i t | i <- [0..] ]
        -- Instantiate variable 0.
        fn i j | j  > i + k = Var (j - 1)
               | j == i + k = terms !! i
               | otherwise  = Var j

-- | Substitute term with var index 0 and shift all remaining free variables.
betaReduce :: Term -> Term -> Term
betaReduce s t = instantiateVar 0 t s

-- | Convert term to weak-head normal form.
whnf :: Term -> Term
whnf (App s t) =
  case whnf s of
    Lambda u -> whnf (betaReduce u t)
    u -> App u t
whnf (Proj1 s) =
  case whnf s of
    Pair t _ -> whnf t
    t -> t
whnf (Proj2 s) =
  case whnf s of
    Pair _ t -> whnf t
    t -> t
whnf t = t

newtype TC a = TC (Maybe a)
  deriving (Functor, Monad)

runTC :: TC a -> Maybe a
runTC (TC v) = v

-- | @conversion g s t a@ returns @Just ()@ if @g@ entails that @s@ and @t@ are
-- equal elements both with type @a@.
conversion :: Telescope -> Term -> Term -> Term -> TC ()
conversion g s t a = conversion' g (whnf s) (whnf t) a

-- Conversion for terms in weak head normal form.
conversion' :: Telescope -> Term -> Term -> Term -> TC ()
conversion' g s t (Set _) = conversionSet' g s t
conversion' _ _ _ UnitType = return ()
conversion' g s t (Pi a b) = conversion (RCons g a) (eta s) (eta t) b
  where eta u = App (incVarBy 1 u) (Var 0)
conversion' g s t (Sigma a b) = do
  conversion g (Proj1 s) (Proj1 t) a
  conversion g (Proj2 s) (Proj2 t) (betaReduce b (Proj1 s))
conversion' g s t _ = do
  neutralEquality g s t >> return ()

-- | @conversionSet g s t@ returns true if @s@ and @t@ are equal types
-- with type @Set i@ for some i@.
conversionSet :: Telescope -> Term -> Term -> TC ()
conversionSet g s t = conversionSet' g (whnf s) (whnf t)

-- | @conversionSet@ applied to terms in weak-head normal form.
conversionSet' :: Telescope -> Term -> Term -> TC ()
conversionSet' _ (Set i) (Set j) | i == j = return ()
conversionSet' g (Pi a1 b1) (Pi a2 b2) = do
  conversionSet g a1 a2
  conversionSet (RCons g a1) b1 b2
conversionSet' g (Sigma a1 b1) (Sigma a2 b2) = do
  conversionSet g a1 a2
  conversionSet (RCons g a1) b1 b2
conversionSet' g s t = do
  void $ neutralEquality g s t

-- | Checks two neutral terms are equal, and returns their type if they are.
neutralEquality :: Telescope -> Term -> Term -> TC Term
neutralEquality g (Var i) (Var j) | i == j =
  case findVarType g i of
    Just t -> return t
    Nothing -> fail "Variables are different"
neutralEquality g (App s1 t1) (App s2 t2) = do
  Pi b c <- whnf <$> neutralEquality g s1 s2
  conversion g t1 t2 b
  return (betaReduce c t1)
neutralEquality g (Proj1 s) (Proj1 t) = do
  Sigma b _ <- whnf <$> neutralEquality g s t
  return b
neutralEquality g (Proj2 s) (Proj2 t) = do
  Sigma b c <- whnf <$> neutralEquality g s t
  return (betaReduce c (Proj1 s))
neutralEquality _ _ _ = fail "Terms are not equal"

isSubtype :: Telescope -> Term -> Term -> TC ()
isSubtype g a b = isSubtype' g (whnf a) (whnf b)

-- | Subtyping for weak head normal forms.
isSubtype' :: Telescope -> Term -> Term -> TC ()
isSubtype' _ (Set i) (Set j) | i <= j = return ()
isSubtype' g (Pi  a1 b1) (Pi a2 b2) = do
  conversionSet g a1 a2
  isSubtype (RCons g a1) b1 b2
isSubtype' g (Sigma  a1 b1) (Sigma a2 b2) = do
  conversionSet g  a1 a2
  isSubtype (RCons g a1) b1 b2
isSubtype' g a b = conversionSet g a b

-- | @checkType g s e@ checks that term @s@ has type @e@ and
-- returns possible beta-reduced form of @s@ with type @e@ if so.
checkType :: Telescope -> Term -> Term -> TC Term
checkType g (Lambda e) a = do
  Pi b c <- return (whnf a)
  Lambda <$> checkType (RCons g b) e c
checkType g (Pair e1 e2) a = do
  Sigma b c <- return (whnf a)
  s <- checkType g e1 b
  t <- checkType g e2 (betaReduce c s)
  return (Pair s t)
checkType g e u = do
  (s,t) <- inferType g e
  isSubtype g s u
  return t

-- | Returns type and evaluated term.
inferType :: Telescope -> Term -> TC (Term,Term)
inferType g (Var x) =
  case findVarType g x of
    Nothing -> error "Could not find variable in context"
    Just t -> return (t,Var x)
inferType _ (Set s) = return (Set (s+1), Set s)
inferType g (Pi e1 e2) = do
  (c1,a) <- inferType g e1
  Set i <- return (whnf c1)
  (c2,b) <- inferType (RCons g a) e2
  Set j <- return (whnf c2)
  return (Set (max i j), Pi a b)
inferType g Lambda{} =
  error "We cannot perform type inference on lambda expressions"
inferType g (App e1 e2) = do
  (a,s) <- inferType g e1
  Pi b c <- return (whnf a)
  t <- checkType g e2 b
  return (betaReduce c t, App s t)
inferType g (Ctor nm t) = do
  undefined
inferType g (Sigma e1 e2) = do
  (c1,a) <- inferType g e1
  Set i <- return (whnf c1)
  (c2,b) <- inferType (RCons g a) e2
  Set j <- return (whnf c2)
  return (Set (max i j), Sigma a b)
inferType g Pair{} = error "Cannnot infer types of pair expressions"
inferType g (Proj1 e) = do
  (a,t) <- inferType g e
  case whnf a of
    Sigma b c -> return (b, Proj1 t)
    _ -> fail "Value for proj1 had wrong type"
inferType g (Proj2 e) = do
  (a,t) <- inferType g e
  case whnf a of
    Sigma b c -> return (betaReduce c t, Proj2 t)
    _ -> fail "Value for proj2 had wrong type"
inferType _ UnitValue = return (UnitType,UnitValue)
inferType _ UnitType = return (Set 0, UnitType)

-- A context mapping is a list of patterns that maps one
-- telescope to another.

internalError :: String -> a
internalError msg = error $ "INTERNAL: " ++ msg

-- @instContext t i u@ returns the context that replaces variable @i@ in @t@ with @u@.
-- It assumes that @p@ is well-typed in the context, and may fail if @p@ cannot be
-- typed due to an occurs check failure.
instContext :: Telescope -> DeBruijnIndex -> Term -> Maybe Telescope
instContext ctx x initTerm
    | Set.member x (termVars initTerm) = Nothing -- Occurs check fails (pattern depends on itself)
    | otherwise = go ctx x (termVars initTerm) [] initTerm []
  where merge :: Telescope -> [Term] -> Telescope
        merge = foldl RCons
        go :: -- | Current telescope
              Telescope
              -- | Index of variable being replaced relative to current telescope.
           -> DeBruijnIndex
              -- | Set of free variables needed to type pattern.
              -- Variables are indexed relative to current telescope.
              -- We maintain the invariant that the index of the variable being
              -- replaced may not appear in the set.
           -> Set DeBruijnIndex
              -- | Variable types that are needed to type pattern.
              -- These are stored in reverse order from how they appeared in context.
              -- Free variables are relative to current telescope.
           -> [Term]
              -- | Term to use in instantiation.
              -- Free variables in term must be relative to @merge g supp@ where @g@ is the
              -- curent telescope and @supp@ is the processed terms.
           -> Term
              -- | Variable types that will be bound after those used to type instantiated term.
              -- Free variables reference @merge g supp@.
           -> [Term]
           -> Maybe Telescope
        go REmpty _i _pv _supp _p _subp = internalError "Variable undefined in telescope"
        go (RCons g _) 0 _ supp _ subp
          = return $ merge (merge g supp) subp
        go (RCons g t) i pv supp u subp
          | needed && occursCheck = Nothing -- Fail due to occurs check
          | needed    = go g (pred i)
                           -- Update list of needed variables as @t@ is needed.
                           (Set.union (Set.map pred pv') (termVars t))
                           (t:supp)
                           u
                           subp
          | otherwise =
              let -- Let supp' be the variables used to define the pattern after
                  -- removing @t@ from their scope.
                  supp' = zipWith removeUnusedTermFreeVar [0..] supp
                  -- Let u' be the pattern after removing suppl
                  -- Free variables in u' are defined by (merge g supp')
                  u' = removeUnusedTermFreeVar suppl u
                  suppl = length supp
                  -- Let t1 be the current type after adding all the variables in supp' to the
                  -- context.
                  t1 = incVarBy suppl t
                  -- Let t2 be the current type after substituting @i@ with @u'@.
                  t2 = instantiateVar (suppl + pred i) u' t1
                  -- Let subp' equal subp after @t@ has been shifted to the head of the list.
                  shiftSubpVarFn j e = shiftlTermFreeVar (suppl + j) j e
                  subp' = zipWith shiftSubpVarFn [0..] subp
               in go g (pred i) (Set.map pred pv') supp' u' (t2 : subp')
         where -- Lookup if this variable is needed to type pattern.
               (_,needed,pv') = Set.splitMember 0 pv
               -- Check that @t@ does not need variable being replaced to type itself.
               occursCheck = Set.member (pred i) (termVars t)


-- Delta = (y : Set 0, x : <y,y>)
-- id_Delta = { x |-> x ; y |-> y }

-- c :: (y :: Set 0) (x :: <y,y>) (Set 0);

-- Gamma = { a: Set 0, b : Set 0 }
-- sigma = { a |-> c .y x ; b |-> y }
-- Delta |- c .y x : Set 0

data Pat = PVar DeBruijnIndex
         | PCtor Name [Pat]
         | PPair Pat Pat
         | PInaccessible Term

-- | Returns term associated with pattern.
patTerm :: Pat -> Term
patTerm (PVar i) = Var i
patTerm (PCtor nm l) = Ctor nm (fmap patTerm l)
patTerm (PPair t u) = Pair (patTerm t) (patTerm u)
patTerm (PInaccessible t) = t

-- The head of the context mapping is the pattern for var 0, the second is ht pattern for
-- var 1, etc.
type ContextMapping = RList Pat

data ConstraintResult
  = Stuck ContextMapping ContextMapping
  | Success ContextMapping
  | Failed ContextMapping ContextMapping

-- match(t,p) => q
-- Assume
-- * t is a context mapping (t : D -> G), i.e. t instantiates the variables in
--   G with variables defined in D.
-- * p is a context mapping (p : T -> G), i.e., p instantiates variables in G
--   with variables defined in G.  T |- p : G.
-- * q is a context mapping (q : T -> D).  It should be the case that tq is a
--   context mapping (tq : T -> G) such that tq = p.

test = do
  let emp = REmpty
  let idType = Pi (Set 0) (Pi (Var 0) (Var 1))
  print $ runTC $ inferType emp idType
  let idFn = Lambda (Lambda (Var 0))
  print $ runTC $ checkType emp idFn idType

{-
Glossary

t is a context mapping "t : D -> G"
Means:
t instantiates the variables in G with patterns that have variables in D.

D |- t : G

match(t,p) => q


p is a context mapping "p : T -> G" (i.e., T |- p : G)

p instantiates the variables in G with variables in T.

t : D -> G

t instantiates the variables in G with variables in D.

q : T -> D

t instantes the variables in D with variables in T.

tq = p

q instantiates the variables

-}
