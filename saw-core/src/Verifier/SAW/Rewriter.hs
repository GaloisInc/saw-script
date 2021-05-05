{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

{- |
Module      : Verifier.SAW.Rewriter
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : jhendrix@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module Verifier.SAW.Rewriter
  ( -- * Rewrite rules
    RewriteRule
  , ctxtRewriteRule
  , lhsRewriteRule
  , rhsRewriteRule
  , annRewriteRule
  , ruleOfTerm
  , ruleOfTerms
  , ruleOfProp
  , scDefRewriteRules
  , scEqsRewriteRules
  , scEqRewriteRule
    -- * Simplification sets
  , Simpset
  , emptySimpset
  , addRule
  , delRule
  , addRules
  , addSimp
  , delSimp
  , addConv
  , addConvs
  , scSimpset
  , listRules
  -- * Term rewriting
  , rewriteSharedTerm
  , rewriteSharedTermTypeSafe
  -- * Matching
  , scMatch
  -- * SharedContext
  , rewritingSharedContext

  , replaceTerm
  , hoistIfs
  ) where

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative ((<$>), pure, (<*>))
import Data.Foldable (Foldable)
#endif
import Control.Monad.Identity
import Control.Monad.State
import Control.Monad.Trans.Maybe
import Data.IORef
import qualified Data.Foldable as Foldable
import Data.Map (Map)
import qualified Data.List as List
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Control.Monad.Trans.Writer.Strict
import Numeric.Natural


import Verifier.SAW.Cache
import Verifier.SAW.Conversion
import qualified Verifier.SAW.Recognizer as R
import Verifier.SAW.SharedTerm
import Verifier.SAW.Term.Functor
import Verifier.SAW.TypedAST
import qualified Verifier.SAW.TermNet as Net

data RewriteRule a
  = RewriteRule { ctxt :: [Term], lhs :: Term, rhs :: Term, permutative :: Bool, annotation :: Maybe a }
  deriving (Show)
-- ^ Invariant: The set of loose variables in @lhs@ must be exactly
-- @[0 .. length ctxt - 1]@. The @rhs@ may contain a subset of these.

-- NB, exclude the annotation from equality tests
instance Eq (RewriteRule a) where
  RewriteRule c1 l1 r1 p1 _a1 == RewriteRule c2 l2 r2 p2 _a2 =
    c1 == c2 && l1 == l2 && r1 == r2 && p1 == p2

ctxtRewriteRule :: RewriteRule a -> [Term]
ctxtRewriteRule = ctxt

lhsRewriteRule :: RewriteRule a -> Term
lhsRewriteRule = lhs

rhsRewriteRule :: RewriteRule a -> Term
rhsRewriteRule = rhs

annRewriteRule :: RewriteRule a -> Maybe a
annRewriteRule = annotation

instance Net.Pattern (RewriteRule a) where
  toPat (RewriteRule _ lhs _ _ _) = Net.toPat lhs

----------------------------------------------------------------------
-- Matching

data MatchState =
  MatchState
  { substitution :: Map DeBruijnIndex Term
  , constraints :: [(Term, Natural)]
  }

emptyMatchState :: MatchState
emptyMatchState = MatchState { substitution = Map.empty, constraints = [] }


-- First-order matching

-- | Equivalent to @(lookup k t, insert k x t)@.
insertLookup :: Ord k => k -> a -> Map k a -> (Maybe a, Map k a)
insertLookup k x t = Map.insertLookupWithKey (\_ a _ -> a) k x t

first_order_match :: Term -> Term -> Maybe (Map DeBruijnIndex Term)
first_order_match pat term = match pat term Map.empty
  where
    match x y m =
      case (unwrapTermF x, unwrapTermF y) of
        (LocalVar i, _) ->
            case my' of
              Nothing -> Just m'
              Just y' -> if alphaEquiv y y' then Just m' else Nothing
            where (my', m') = insertLookup i y m
        (App x1 x2, App y1 y2) ->
            match x1 y1 m >>= match x2 y2
        (FTermF xf, FTermF yf) ->
            do zf <- zipWithFlatTermF match xf yf
               Foldable.foldl (>=>) Just zf m
        (_, _) ->
            if alphaEquiv x y then Just m else Nothing
-- ^ Precondition: Every loose variable in the pattern @pat@ must
-- occur as the 2nd argument of an @App@ constructor. This ensures
-- that instantiations are well-typed.

asConstantNat :: Term -> Maybe Natural
asConstantNat t =
  case R.asCtor t of
    Just (i, []) | i == "Prelude.Zero" -> Just 0
    Just (i, [x]) | i == "Prelude.Succ" -> (+ 1) <$> asConstantNat x
    _ ->
      do let (f, xs) = R.asApplyAll t
         i <- R.asGlobalDef f
         case xs of
           [x, y]
             | i == "Prelude.addNat" -> (+) <$> asConstantNat x <*> asConstantNat y
             | i == "Prelude.mulNat" -> (*) <$> asConstantNat x <*> asConstantNat y
             | i == "Prelude.expNat" -> (^) <$> asConstantNat x <*> asConstantNat y
             | i == "Prelude.subNat" ->
                 do x' <- asConstantNat x
                    y' <- asConstantNat y
                    guard (x' >= y')
                    return (x' - y')
             | i == "Prelude.divNat" ->
                 do x' <- asConstantNat x
                    y' <- asConstantNat y
                    guard (y' > 0)
                    return (x' `div` y')
             | i == "Prelude.remNat" ->
                 do x' <- asConstantNat x
                    y' <- asConstantNat y
                    guard (y' > 0)
                    return (x' `rem` y')
           _ -> Nothing

-- | An enhanced matcher that can handle higher-order patterns.
scMatch ::
  SharedContext ->
  Term {- ^ pattern -} ->
  Term {- ^ term -} ->
  IO (Maybe (Map DeBruijnIndex Term))
scMatch sc pat term =
  runMaybeT $
  do --lift $ putStrLn $ "********** scMatch **********"
     MatchState inst cs <- match 0 [] pat term emptyMatchState
     mapM_ (check inst) cs
     return inst
  where
    check :: Map DeBruijnIndex Term -> (Term, Natural) -> MaybeT IO ()
    check inst (t, n) = do
      --lift $ putStrLn $ "checking: " ++ show (t, n)
      -- apply substitution to the term
      t' <- lift $ instantiateVarList sc 0 (Map.elems inst) t
      --lift $ putStrLn $ "t': " ++ show t'
      -- constant-fold nat operations
      -- ensure that it evaluates to the same number
      case asConstantNat t' of
        Just i | i == n -> return ()
        _ -> mzero

    asVarPat :: Int -> Term -> Maybe (DeBruijnIndex, [DeBruijnIndex])
    asVarPat depth = go []
      where
        go js x =
          case unwrapTermF x of
            LocalVar i
              | i >= depth -> Just (i, js)
              | otherwise  -> Nothing
            App t (unwrapTermF -> LocalVar j)
              | j < depth -> go (j : js) t
            _ -> Nothing

    match :: Int -> [(LocalName, Term)] -> Term -> Term -> MatchState -> MaybeT IO MatchState
    match _ _ (STApp i fv _) (STApp j _ _) s
      | fv == emptyBitSet && i == j = return s
    match depth env x y s@(MatchState m cs) =
      --do
      --lift $ putStrLn $ "matching (lhs): " ++ scPrettyTerm defaultPPOpts x
      --lift $ putStrLn $ "matching (rhs): " ++ scPrettyTerm defaultPPOpts y
      case asVarPat depth x of
        Just (i, js) ->
          do -- ensure parameter variables are distinct
             guard (Set.size (Set.fromList js) == length js)
             -- ensure y mentions only variables that are in js
             let fvj = foldl unionBitSets emptyBitSet (map singletonBitSet js)
             let fvy = looseVars y `intersectBitSets` (completeBitSet depth)
             guard (fvy `unionBitSets` fvj == fvj)
             let fixVar t (nm, ty) =
                   do v <- scFreshGlobal sc nm ty
                      let Just ec = R.asExtCns v
                      t' <- instantiateVar sc 0 v t
                      return (t', ec)
             let fixVars t [] = return (t, [])
                 fixVars t (ty : tys) =
                   do (t', ec) <- fixVar t ty
                      (t'', ecs) <- fixVars t' tys
                      return (t'', ec : ecs)
             -- replace local bound variables with global ones
             -- this also decrements loose variables in y by `depth`
             (y1, ecs) <- lift $ fixVars y env
             -- replace global variables with reindexed bound vars
             -- y2 should have no more of the newly-created ExtCns vars
             y2 <- lift $ scAbstractExts sc [ ecs !! j | j <- js ] y1
             let (my3, m') = insertLookup (i - depth) y2 m
             case my3 of
               Nothing -> return (MatchState m' cs)
               Just y3 -> if y2 == y3 then return (MatchState m' cs) else mzero
        Nothing ->
          case (unwrapTermF x, unwrapTermF y) of
            -- check that neither x nor y contains bound variables less than `depth`
            (FTermF xf, FTermF yf) ->
              case zipWithFlatTermF (match depth env) xf yf of
                Nothing -> mzero
                Just zf -> Foldable.foldl (>=>) return zf s
            (App x1 x2, App y1 y2) ->
              match depth env x1 y1 s >>= match depth env x2 y2
            (Lambda _ t1 x1, Lambda nm t2 x2) ->
              match depth env t1 t2 s >>= match (depth + 1) ((nm, t2) : env) x1 x2
            (Pi _ t1 x1, Pi nm t2 x2) ->
              match depth env t1 t2 s >>= match (depth + 1) ((nm, t2) : env) x1 x2
            (App _ _, FTermF (NatLit n)) ->
              -- add deferred constraint
              return (MatchState m ((x, n) : cs))
            (_, _) ->
              -- other possible matches are local vars and constants
              if x == y then return s else mzero

----------------------------------------------------------------------
-- Building rewrite rules

eqIdent :: Ident
eqIdent = mkIdent (mkModuleName ["Prelude"]) "Eq"

ecEqIdent :: Ident
ecEqIdent = mkIdent (mkModuleName ["Cryptol"]) "ecEq"

bvEqIdent :: Ident
bvEqIdent = mkIdent (mkModuleName ["Prelude"]) "bvEq"

boolEqIdent :: Ident
boolEqIdent = mkIdent (mkModuleName ["Prelude"]) "boolEq"

vecEqIdent :: Ident
vecEqIdent = mkIdent (mkModuleName ["Prelude"]) "vecEq"

equalNatIdent :: Ident
equalNatIdent = mkIdent (mkModuleName ["Prelude"]) "equalNat"

-- | Converts a universally quantified equality proposition from a
-- Term representation to a RewriteRule.
ruleOfTerm :: Term -> Maybe a -> RewriteRule a
ruleOfTerm t ann =
    case unwrapTermF t of
      -- NOTE: this assumes the Coq-style equality type Eq X x y, where both X
      -- (the type of x and y) and x are parameters, and y is an index
      FTermF (DataTypeApp ident [_, x] [y])
          | ident == eqIdent -> mkRewriteRule [] x y ann
      Pi _ ty body -> rule { ctxt = ty : ctxt rule }
          where rule = ruleOfTerm body ann
      _ -> error "ruleOfSharedTerm: Illegal argument"

-- Test whether a rewrite rule is permutative
-- this is a rule that immediately loops whether used forwards or backwards.
rulePermutes :: Term -> Term -> Bool
rulePermutes lhs rhs =
    case first_order_match lhs rhs of
        Nothing -> False -- rhs is not an instance of lhs
        Just _ ->
          case first_order_match rhs lhs of
            Nothing -> False -- but here we have a looping rule, not good!
            Just _ -> True

mkRewriteRule :: [Term] -> Term -> Term -> Maybe a -> RewriteRule a
mkRewriteRule c l r ann =
    RewriteRule {ctxt = c, lhs = l, rhs = r , permutative = rulePermutes l r, annotation = ann}

-- | Converts a universally quantified equality proposition between the
-- two given terms to a RewriteRule.
ruleOfTerms :: Term -> Term -> RewriteRule a
ruleOfTerms l r = mkRewriteRule [] l r Nothing

-- | Converts a parameterized equality predicate to a RewriteRule,
-- returning 'Nothing' if the predicate is not an equation.
ruleOfProp :: Term -> Maybe a -> Maybe (RewriteRule a)
ruleOfProp (R.asPi -> Just (_, ty, body)) ann =
  do rule <- ruleOfProp body ann
     Just rule { ctxt = ty : ctxt rule }
ruleOfProp (R.asLambda -> Just (_, ty, body)) ann =
  do rule <- ruleOfProp body ann
     Just rule { ctxt = ty : ctxt rule }
ruleOfProp (R.asApplyAll -> (R.isGlobalDef ecEqIdent -> Just (), [_, _, x, y])) ann =
  Just $ mkRewriteRule [] x y ann
ruleOfProp (R.asApplyAll -> (R.isGlobalDef bvEqIdent -> Just (), [_, x, y])) ann =
  Just $ mkRewriteRule [] x y ann
ruleOfProp (R.asApplyAll -> (R.isGlobalDef equalNatIdent -> Just (), [x, y])) ann =
  Just $ mkRewriteRule [] x y ann
ruleOfProp (R.asApplyAll -> (R.isGlobalDef boolEqIdent -> Just (), [x, y])) ann =
  Just $ mkRewriteRule [] x y ann
ruleOfProp (R.asApplyAll -> (R.isGlobalDef vecEqIdent -> Just (), [_, _, _, x, y])) ann =
  Just $ mkRewriteRule [] x y ann
ruleOfProp (unwrapTermF -> Constant _ body) ann = ruleOfProp body ann
ruleOfProp (R.asEq -> Just (_, x, y)) ann =
  Just $ mkRewriteRule [] x y ann
ruleOfProp (R.asEqTrue -> Just body) ann = ruleOfProp body ann
ruleOfProp _ _ = Nothing

-- | Generate a rewrite rule from the type of an identifier, using 'ruleOfTerm'
scEqRewriteRule :: SharedContext -> Ident -> IO (RewriteRule a)
scEqRewriteRule sc i = ruleOfTerm <$> scTypeOfGlobal sc i <*> pure Nothing

-- | Collects rewrite rules from named constants, whose types must be equations.
scEqsRewriteRules :: SharedContext -> [Ident] -> IO [RewriteRule a]
scEqsRewriteRules sc = mapM (scEqRewriteRule sc)

-- | Transform the given rewrite rule to a set of one or more
-- equivalent rewrite rules, if possible.
--
-- * If the rhs is a lambda, then add an argument to the lhs.
-- * If the rhs is a recursor, then split into a separate rule for each constructor.
-- * If the rhs is a record, then split into a separate rule for each accessor.
scExpandRewriteRule :: SharedContext -> RewriteRule a -> IO (Maybe [RewriteRule a])
scExpandRewriteRule sc (RewriteRule ctxt lhs rhs _ ann) =
  case rhs of
    (R.asLambda -> Just (_, ty, body)) ->
      do let ctxt' = ctxt ++ [ty]
         lhs1 <- incVars sc 0 1 lhs
         var0 <- scLocalVar sc 0
         lhs' <- scApply sc lhs1 var0
         return $ Just [mkRewriteRule ctxt' lhs' body ann]
    (R.asRecordValue -> Just m) ->
      do let mkRule (k, x) =
               do l <- scRecordSelect sc lhs k
                  return (mkRewriteRule ctxt l x ann)
         Just <$> traverse mkRule (Map.assocs m)
    (R.asApplyAll ->
     (R.asRecursorApp -> Just (rec, crec, _ixs, R.asLocalVar -> Just i),
      more)) ->
      do let ctxt1 = reverse (drop (i+1) (reverse ctxt))
         let ctxt2 = reverse (take i (reverse ctxt))
         -- The type @ti@ is in the de Bruijn context @ctxt1@.
         ti <- scWhnf sc (reverse ctxt !! i)
         -- The datatype parameters are also in context @ctxt1@.
         (_d, params1, _ixs) <- maybe (fail "expected DataTypeApp") return (R.asDataTypeParams ti)
         let ctorRule ctor =
               do -- Compute the argument types @argTs@ in context @ctxt1@.
                  ctorT <- piAppType (ctorType ctor) params1
                  let argTs = map snd (fst (R.asPiList ctorT))
                  let nargs = length argTs
                  -- Build a fully-applied constructor @c@ in context @ctxt1 ++ argTs@.
                  params2 <- traverse (incVars sc 0 nargs) params1
                  args <- traverse (scLocalVar sc) (reverse (take nargs [0..]))
                  c <- scCtorAppParams sc (ctorName ctor) params2 args
                  -- Build the list of types of the new context.
                  let ctxt' = ctxt1 ++ argTs ++ ctxt2
                  -- Define function to adjust indices on a term from
                  -- context @ctxt@ into context @ctxt'@. We also
                  -- substitute the constructor @c@ in for the old
                  -- local variable @i@.
                  let adjust t = instantiateVar sc i c =<< incVars sc (i+1) nargs t
                  -- Adjust the indices and substitute the new
                  -- constructor value to make the new params, lhs,
                  -- and rhs in context @ctxt'@.
                  lhs' <- adjust lhs

                  rec'  <- adjust rec
                  crec' <- traverse adjust crec
                  args' <- traverse (incVars sc 0 i) args
                  more' <- traverse adjust more
                  let cn = ctorName ctor

                  rhs1 <- scReduceRecursor sc rec' crec' cn args'
                  rhs2 <- scApplyAll sc rhs1 more'
                  rhs3 <- betaReduce rhs2
                  -- re-fold recursive occurrences of the original rhs
                  let ss = addRule (mkRewriteRule ctxt rhs lhs Nothing) emptySimpset
                  (_,rhs') <- rewriteSharedTerm sc (ss :: Simpset ()) rhs3
                  return (mkRewriteRule ctxt' lhs' rhs' ann)
         dt <- scRequireDataType sc (recursorDataType crec)
         rules <- traverse ctorRule (dtCtors dt)
         return (Just rules)
    _ -> return Nothing
  where
    piAppType :: Term -> [Term] -> IO Term
    piAppType funtype [] = return funtype
    piAppType funtype (arg : args) =
      do (_, _, body) <- maybe (fail "expected Pi type") return (R.asPi funtype)
         funtype' <- instantiateVar sc 0 arg body
         piAppType funtype' args

    betaReduce :: Term -> IO Term
    betaReduce t =
      case R.asApp t of
        Nothing -> return t
        Just (f, arg) ->
          do f' <- betaReduce f
             case R.asLambda f' of
               Nothing -> scApply sc f' arg
               Just (_, _, body) -> instantiateVar sc 0 arg body

-- | Repeatedly apply the rule transformations in 'scExpandRewriteRule'.
scExpandRewriteRules :: SharedContext -> [RewriteRule a] -> IO [RewriteRule a]
scExpandRewriteRules sc rs =
  case rs of
    [] -> return []
    r : rs2 ->
      do m <- scExpandRewriteRule sc r
         case m of
           Nothing -> (r :) <$> scExpandRewriteRules sc rs2
           Just rs1 -> scExpandRewriteRules sc (rs1 ++ rs2)

-- | Create a rewrite rule for a definition that expands the definition, if it
-- has a body to expand to, otherwise return the empty list
scDefRewriteRules :: SharedContext -> Def -> IO [RewriteRule a]
scDefRewriteRules _ (Def { defBody = Nothing }) = return []
scDefRewriteRules sc (Def { defIdent = ident, defBody = Just body }) =
  do lhs <- scGlobalDef sc ident
     rhs <- scSharedTerm sc body
     scExpandRewriteRules sc [mkRewriteRule [] lhs rhs Nothing]


----------------------------------------------------------------------
-- Simpsets

-- | Invariant: 'Simpset's should not contain reflexive rules. We avoid
-- adding them in 'addRule' below.
type Simpset a = Net.Net (Either (RewriteRule a) Conversion)

emptySimpset :: Simpset a
emptySimpset = Net.empty

addRule :: RewriteRule a -> Simpset a -> Simpset a
addRule rule | lhs rule /= rhs rule = Net.insert_term (lhs rule, Left rule)
             | otherwise = id

delRule :: RewriteRule a -> Simpset a -> Simpset a
delRule rule = Net.delete_term (lhs rule, Left rule)

addRules :: [RewriteRule a] -> Simpset a -> Simpset a
addRules rules ss = foldr addRule ss rules

addSimp :: Term -> Maybe a -> Simpset a -> Simpset a
addSimp prop ann = addRule (ruleOfTerm prop ann)

delSimp :: Term -> Simpset a -> Simpset a
delSimp prop = delRule (ruleOfTerm prop Nothing)

addConv :: Conversion -> Simpset a -> Simpset a
addConv conv = Net.insert_term (conv, Right conv)

addConvs :: [Conversion] -> Simpset a -> Simpset a
addConvs convs ss = foldr addConv ss convs

scSimpset :: SharedContext -> [Def] -> [Ident] -> [Conversion] -> IO (Simpset a)
scSimpset sc defs eqIdents convs = do
  defRules <- concat <$> traverse (scDefRewriteRules sc) defs
  eqRules <- mapM (scEqRewriteRule sc) eqIdents
  return $ addRules defRules $ addRules eqRules $ addConvs convs $ emptySimpset

listRules :: Simpset a -> [RewriteRule a]
listRules ss = [ r | Left r <- Net.content ss ]

----------------------------------------------------------------------
-- Destructors for terms

asBetaRedex :: R.Recognizer Term (LocalName, Term, Term, Term)
asBetaRedex t =
    do (f, arg) <- R.asApp t
       (s, ty, body) <- R.asLambda f
       return (s, ty, body, arg)

asPairRedex :: R.Recognizer Term Term
asPairRedex t =
    do (u, b) <- R.asPairSelector t
       (x, y) <- R.asPairValue u
       return (if b then y else x)

asRecordRedex :: R.Recognizer Term Term
asRecordRedex t =
    do (x, i) <- R.asRecordSelector t
       ts <- R.asRecordValue x
       case Map.lookup i ts of
         Just t' -> return t'
         Nothing -> fail "Record field not found"

-- | An iota redex is a recursor application whose main argument is a
-- constructor application; specifically, this function recognizes
--
-- > RecursorApp rec _ (CtorApp c _ args)
asIotaRedex :: R.Recognizer Term (Term, CompiledRecursor Term, Ident, [Term])
asIotaRedex t =
  do (rec, crec, _, arg) <- R.asRecursorApp t
     (c, _, args) <- asCtorOrNat arg
     return (rec, crec, c, args)


----------------------------------------------------------------------
-- Bottom-up rewriting

-- | Term ordering
-- The existing "<" on terms is not adequate for deciding how to handle permutative rules,
-- as then associativity and commutativity can loop.
-- The following rather unsophisticated functions *might* prevent looping.
-- More analysis is needed!
--
-- here we get the "fringe" of arguments in an application, looking at either curried or
-- tupled arguments.  That is
--   for `f x y z`, return [x,y,z]
--   for `f (x,y)` return [x,y]
--   for `f (f x y) z`, return [x,y,z]
--   for `f (x, f (y,z))`, return [x,y,z]
appCollectedArgs :: Term -> [Term]
appCollectedArgs t = step0 (unshared t) []
  where
    unshared (STApp{stAppIndex = _, stAppTermF = tf1}) = tf1
    unshared (Unshared tf1) = tf1
    -- step 0: accumulate curried args, find the function
    step0 ::  TermF Term -> [Term] -> [Term]
    step0 (App f a) args = step0 (unshared f) (a:args)
    step0 other args = step1 other args
    -- step 1: analyse each arg, knowing the called function, append together
    step1 :: TermF Term -> [Term] -> [Term]
    step1 f args = foldl (++) [] (map (\ x -> step2 f $ unshared x) args)
    -- step2: analyse an arg.  look inside tuples, sequences (TBD), more calls to f
    step2 :: TermF Term -> TermF Term -> [Term]
    step2 f (FTermF (PairValue x y)) = (step2 f $ unshared x) ++ (step2 f $ unshared y)
    step2 f (s@(App g a)) = possibly_curried_args s f (unshared g) (step2 f $ unshared a)
    step2 _ a = [Unshared a]
    --
    possibly_curried_args :: TermF Term -> TermF Term -> TermF Term -> [Term] -> [Term]
    possibly_curried_args s f (App g a) args = possibly_curried_args s f (unshared g) ((step2 f $ unshared a) ++ args)
    possibly_curried_args s f h args = if f == h then args else [Unshared s]


termWeightLt :: Term -> Term -> Bool
termWeightLt t t' =
  (appCollectedArgs t) < (appCollectedArgs t')

-- | Do a single reduction step (beta, record or tuple selector) at top
-- level, if possible.
reduceSharedTerm :: SharedContext -> Term -> Maybe (IO Term)
reduceSharedTerm sc (asBetaRedex -> Just (_, _, body, arg)) = Just (instantiateVar sc 0 arg body)
reduceSharedTerm _ (asPairRedex -> Just t) = Just (return t)
reduceSharedTerm _ (asRecordRedex -> Just t) = Just (return t)
reduceSharedTerm sc (asIotaRedex -> Just (rec, crec, c, args)) =
  Just $ scReduceRecursor sc rec crec c args
reduceSharedTerm _ _ = Nothing

-- | Rewriter for shared terms.  The annotations of any used rules are collected
--   and returned in the result set.
rewriteSharedTerm :: forall a. Ord a => SharedContext -> Simpset a -> Term -> IO (Set a, Term)
rewriteSharedTerm sc ss t0 =
    do cache <- newCache
       let ?cache = cache
       setRef <- newIORef mempty
       let ?annSet = setRef
       t <- rewriteAll t0
       anns <- readIORef setRef
       pure (anns, t)

  where
    rewriteAll :: (?cache :: Cache IO TermIndex Term, ?annSet :: IORef (Set a)) => Term -> IO Term
    rewriteAll (Unshared tf) =
        traverseTF rewriteAll tf >>= scTermF sc >>= rewriteTop
    rewriteAll STApp{ stAppIndex = tidx, stAppTermF = tf } =
        useCache ?cache tidx (traverseTF rewriteAll tf >>= scTermF sc >>= rewriteTop)

    traverseTF :: forall b. (b -> IO b) -> TermF b -> IO (TermF b)
    traverseTF _ tf@(Constant {}) = pure tf
    traverseTF f tf = traverse f tf

    rewriteTop :: (?cache :: Cache IO TermIndex Term, ?annSet :: IORef (Set a)) => Term -> IO Term
    rewriteTop t =
        case reduceSharedTerm sc t of
          Nothing -> apply (Net.unify_term ss t) t
          Just io -> rewriteAll =<< io

    recordAnn :: (?annSet :: IORef (Set a)) => Maybe a -> IO ()
    recordAnn Nothing  = return ()
    recordAnn (Just a) = modifyIORef' ?annSet (Set.insert a)

    apply :: (?cache :: Cache IO TermIndex Term, ?annSet :: IORef (Set a)) =>
             [Either (RewriteRule a) Conversion] -> Term -> IO Term
    apply [] t = return t
    apply (Left (RewriteRule {ctxt, lhs, rhs, permutative, annotation}) : rules) t = do
      result <- scMatch sc lhs t
      case result of
        Nothing -> apply rules t
        Just inst
          | lhs == rhs ->
            -- This should never happen because we avoid inserting
            -- reflexive rules into simp sets in the first place.
            do putStrLn $ "rewriteSharedTerm: skipping reflexive rule " ++
                          "(THE IMPOSSIBLE HAPPENED!): " ++ scPrettyTerm defaultPPOpts lhs
               apply rules t
          | Map.keys inst /= take (length ctxt) [0 ..] ->
            do putStrLn $ "rewriteSharedTerm: invalid lhs does not contain all variables: "
                 ++ scPrettyTerm defaultPPOpts lhs
               apply rules t
          | permutative ->
            do
              t' <- instantiateVarList sc 0 (Map.elems inst) rhs
              case termWeightLt t' t of
                True -> recordAnn annotation >> rewriteAll t' -- keep the result only if it is "smaller"
                False -> apply rules t
          | otherwise ->
            do -- putStrLn "REWRITING:"
               -- print lhs
               recordAnn annotation
               rewriteAll =<< instantiateVarList sc 0 (Map.elems inst) rhs
    apply (Right conv : rules) t =
        do -- putStrLn "REWRITING:"
           -- print (Net.toPat conv)
           case runConversion conv t of
             Nothing -> apply rules t
             Just tb -> rewriteAll =<< runTermBuilder tb (scGlobalDef sc) (scTermF sc)

-- | Type-safe rewriter for shared terms
rewriteSharedTermTypeSafe :: forall a. Ord a =>
  SharedContext -> Simpset a -> Term -> IO (Set a, Term)
rewriteSharedTermTypeSafe sc ss t0 =
    do cache <- newCache
       let ?cache = cache
       annRef <- newIORef mempty
       let ?annSet = annRef
       t <- rewriteAll t0
       anns <- readIORef annRef
       return (anns, t)

  where
    rewriteAll :: (?cache :: Cache IO TermIndex Term, ?annSet :: IORef (Set a)) =>
                  Term -> IO Term
    rewriteAll (Unshared tf) =
        rewriteTermF tf >>= scTermF sc >>= rewriteTop
    rewriteAll STApp{ stAppIndex = tidx, stAppTermF = tf } =
        -- putStrLn "Rewriting term:" >> print t >>
        useCache ?cache tidx (rewriteTermF tf >>= scTermF sc >>= rewriteTop)

    rewriteTermF :: (?cache :: Cache IO TermIndex Term, ?annSet :: IORef (Set a)) =>
                    TermF Term -> IO (TermF Term)
    rewriteTermF tf =
        case tf of
          FTermF ftf -> FTermF <$> rewriteFTermF ftf
          App e1 e2 ->
              do t1 <- scTypeOf sc e1
                 case unwrapTermF t1 of
                   -- We only rewrite e2 if type of e1 is not a dependent type.
                   -- This prevents rewriting e2 from changing type of @App e1 e2@.
                   Pi _ _ t | inBitSet 0 (looseVars t) -> App <$> rewriteAll e1 <*> rewriteAll e2
                   _ -> App <$> rewriteAll e1 <*> pure e2
          Lambda pat t e -> Lambda pat t <$> rewriteAll e
          Constant{}     -> return tf
          _ -> return tf -- traverse rewriteAll tf

    rewriteFTermF :: (?cache :: Cache IO TermIndex Term, ?annSet :: IORef (Set a)) =>
                     FlatTermF Term -> IO (FlatTermF Term)
    rewriteFTermF ftf =
        case ftf of
          UnitValue        -> return ftf
          UnitType         -> return ftf
          PairValue{}      -> traverse rewriteAll ftf
          PairType{}       -> return ftf -- doesn't matter
          PairLeft{}       -> traverse rewriteAll ftf
          PairRight{}      -> traverse rewriteAll ftf

          -- NOTE: we don't rewrite arguments of constructors, datatypes, or
          -- recursors because of dependent types, as we could potentially cause
          -- a term to become ill-typed
          CtorApp{}        -> return ftf
          DataTypeApp{}    -> return ftf -- could treat same as CtorApp

          RecursorType{}   -> return ftf
          Recursor{}       -> return ftf
          RecursorApp{}    -> return ftf -- could treat same as CtorApp

          RecordType{}     -> traverse rewriteAll ftf
          RecordValue{}    -> traverse rewriteAll ftf
          RecordProj{}     -> traverse rewriteAll ftf
          Sort{}           -> return ftf -- doesn't matter
          NatLit{}         -> return ftf -- doesn't matter
          ArrayValue t es  -> ArrayValue t <$> traverse rewriteAll es
          Primitive{}      -> return ftf
          StringLit{}      -> return ftf
          ExtCns{}         -> return ftf

    rewriteTop :: (?cache :: Cache IO TermIndex Term, ?annSet :: IORef (Set a)) =>
                  Term -> IO Term
    rewriteTop t = apply (Net.match_term ss t) t

    recordAnn :: (?annSet :: IORef (Set a)) => Maybe a -> IO ()
    recordAnn Nothing  = return ()
    recordAnn (Just a) = modifyIORef' ?annSet (Set.insert a)

    apply :: (?cache :: Cache IO TermIndex Term, ?annSet :: IORef (Set a)) =>
             [Either (RewriteRule a) Conversion] ->
             Term -> IO Term
    apply [] t = return t
    apply (Left rule : rules) t =
      case first_order_match (lhs rule) t of
        Nothing -> apply rules t
        Just inst ->
          do recordAnn (annotation rule)
             rewriteAll =<< instantiateVarList sc 0 (Map.elems inst) (rhs rule)
    apply (Right conv : rules) t =
      case runConversion conv t of
        Nothing -> apply rules t
        Just tb -> rewriteAll =<< runTermBuilder tb (scGlobalDef sc) (scTermF sc)

-- | Generate a new SharedContext that normalizes terms as it builds them.
--   Rule annotations are ignored.
rewritingSharedContext :: SharedContext -> Simpset a -> SharedContext
rewritingSharedContext sc ss = sc'
  where
    sc' = sc { scTermF = rewriteTop }

    rewriteTop :: TermF Term -> IO Term
    rewriteTop tf =
      case asPairRedex t of
        Just t' -> return t'
        Nothing ->
          case asRecordRedex t of
            Just t' -> return t'
            Nothing -> apply (Net.match_term ss t) t
      where t = Unshared tf

    apply :: [Either (RewriteRule a) Conversion] ->
             Term -> IO Term
    apply [] (Unshared tf) = scTermF sc tf
    apply [] STApp{ stAppTermF = tf } = scTermF sc tf
    apply (Left (RewriteRule _ l r _ _ann) : rules) t =
      case first_order_match l t of
        Nothing -> apply rules t
        Just inst
          | l == r ->
            do putStrLn $ "rewritingSharedContext: skipping reflexive rule: " ++ scPrettyTerm defaultPPOpts l
               apply rules t
          | otherwise -> instantiateVarList sc' 0 (Map.elems inst) r
    apply (Right conv : rules) t =
      case runConversion conv t of
        Nothing -> apply rules t
        Just tb -> runTermBuilder tb (scGlobalDef sc) (scTermF sc')


-- FIXME: is there some way to have sensable term replacement in the presence of loose variables
--  and/or under binders?
replaceTerm :: Ord a =>
  SharedContext ->
  Simpset a    {- ^ A simpset of rewrite rules to apply along with the replacement -} ->
  (Term, Term) {- ^ (pat,repl) is a tuple of a pattern term to replace and a replacement term -} ->
  Term         {- ^ the term in which to perform the replacement -} ->
  IO (Set a, Term)
replaceTerm sc ss (pat, repl) t = do
    let fvs = looseVars pat
    unless (fvs == emptyBitSet) $ fail $ unwords
       [ "replaceTerm: term to replace has free variables!", scPrettyTerm defaultPPOpts t ]
    let rule = ruleOfTerms pat repl
    let ss' = addRule rule ss
    rewriteSharedTerm sc ss' t


-------------------------------------------------------------------------------
-- If/then/else hoisting

-- | Find all instances of Prelude.ite in the given term and hoist them
--   higher.  An if-then-else floats upward until it hits a binder that
--   binds one of its free variables, or until it bubbles to the top of
--   the term.  When multiple if-then-else branches bubble to the same
--   place, they will be nested via a canonical term ordering.  This transformation
--   also does rewrites by basic boolean identities.
hoistIfs :: SharedContext
         -> Term
         -> IO Term
hoistIfs sc t = do
   cache <- newCache

   let app x y = join (scTermF sc <$> (pure App <*> x <*> y))
   itePat <-
          (scGlobalDef sc "Prelude.ite")
          `app`
          (scLocalVar sc 0)
          `app`
          (scLocalVar sc 1)
          `app`
          (scLocalVar sc 2)
          `app`
          (scLocalVar sc 3)

   rules <- map (\rt -> ruleOfTerm rt Nothing) <$> mapM (scTypeOfGlobal sc)
              [ "Prelude.ite_true"
              , "Prelude.ite_false"
              , "Prelude.ite_not"
              , "Prelude.ite_nest1"
              , "Prelude.ite_nest2"
              , "Prelude.ite_eq"
              , "Prelude.ite_bit_false_1"
              , "Prelude.ite_bit_true_1"
              , "Prelude.ite_bit"
              , "Prelude.not_not"
              , "Prelude.and_True1"
              , "Prelude.and_False1"
              , "Prelude.and_True2"
              , "Prelude.and_False2"
              , "Prelude.and_idem"
              , "Prelude.or_True1"
              , "Prelude.or_False1"
              , "Prelude.or_True2"
              , "Prelude.or_False2"
              , "Prelude.or_idem"
              , "Prelude.not_or"
              , "Prelude.not_and"
              ]
   let ss :: Simpset () = addRules rules emptySimpset

   (t', conds) <- doHoistIfs sc ss cache itePat . snd =<< rewriteSharedTerm sc ss t
   splitConds sc ss (map fst conds) t'


splitConds :: Ord a => SharedContext -> Simpset a -> [Term] -> Term -> IO Term
splitConds sc ss = go
 where
   go [] t = return t
   go (c:cs) t = go cs =<< splitCond sc ss c t

splitCond :: Ord a => SharedContext -> Simpset a -> Term -> Term -> IO Term
splitCond sc ss c t = do
   ty <- scTypeOf sc t
   trueTerm  <- scBool sc True
   falseTerm <- scBool sc False

   (_,then_branch) <- replaceTerm sc ss (c, trueTerm) t
   (_,else_branch) <- replaceTerm sc ss (c, falseTerm) t
   scGlobalApply sc "Prelude.ite" [ty, c, then_branch, else_branch]


type HoistIfs s = (Term, [(Term, Set (ExtCns Term))])


orderTerms :: SharedContext -> [Term] -> IO [Term]
orderTerms _sc xs = return $ List.sort xs

doHoistIfs :: Ord a =>
  SharedContext ->
  Simpset a ->
  Cache IO TermIndex (HoistIfs s) ->
  Term ->
  Term ->
  IO (HoistIfs s)
doHoistIfs sc ss hoistCache itePat = go

 where go :: Term -> IO (HoistIfs s)
       go t@(STApp{ stAppIndex = idx, stAppTermF = tf}) = useCache hoistCache idx $ top t tf
       go t@(Unshared tf)  = top t tf

       top :: Term -> TermF Term -> IO (HoistIfs s)
       top t tf
          | Just inst <- first_order_match itePat t = do
               let Just branch_tp   = Map.lookup 0 inst
               let Just cond        = Map.lookup 1 inst
               let Just then_branch = Map.lookup 2 inst
               let Just else_branch = Map.lookup 3 inst

               (then_branch',conds1) <- go then_branch
               (else_branch',conds2) <- go else_branch

               t' <- scGlobalApply sc "Prelude.ite" [branch_tp, cond, then_branch', else_branch']
               let ecs = getAllExtSet cond
               return (t', (cond, ecs) : conds1 ++ conds2)

          | otherwise = goF t tf

       goF :: Term -> TermF Term -> IO (HoistIfs s)

       goF t (LocalVar _)  = return (t, [])
       goF t (Constant {}) = return (t, [])

       goF _ (FTermF ftf) = do
                (ftf', conds) <- runWriterT $ traverse WriterT $ (fmap go ftf)
                t' <- scFlatTermF sc ftf'
                return (t', conds)

       goF _ (App f x) = do
           (f', conds1) <- go f
           (x', conds2) <- go x
           t' <- scApply sc f' x'
           return (t', conds1 ++ conds2)

       goF _ (Lambda nm tp body) = goBinder scLambda nm tp body
       goF _ (Pi nm tp body) = goBinder scPi nm tp body

       goBinder close nm tp body = do
           (ec, body') <- scOpenTerm sc nm tp 0 body
           (body'', conds) <- go body'
           let (stuck, float) = List.partition (\(_,ecs) -> Set.member ec ecs) conds

           stuck' <- orderTerms sc (map fst stuck)
           body''' <- splitConds sc ss stuck' body''

           t' <- scCloseTerm close sc ec body'''
           return (t', float)
