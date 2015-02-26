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
Copyright   : Galois, Inc. 2012-2014
License     : BSD3
Maintainer  : jhendrix@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module Verifier.SAW.Rewriter
  ( -- * Rewrite rules
    RewriteRule
  , ruleOfTerm
  , ruleOfTerms
  , ruleOfProp
  , ruleOfDefEqn
  , rulesOfTypedDef
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
  -- * Term rewriting
  , rewriteTerm
  , rewriteSharedTerm
  , rewriteSharedTermToTerm
  , rewriteSharedTermTypeSafe
  -- * SharedContext
  , rewritingSharedContext

  , replaceTerm
  , hoistIfs
  ) where

import Control.Applicative ((<$>), pure, (<*>))
import Control.Lens
import Control.Monad.Identity
import Control.Monad.State
import Data.Bits
import Data.Foldable (Foldable)
import qualified Data.Foldable as Foldable
import Data.IORef (IORef)
import Data.Map (Map)
import qualified Data.List as List
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Maybe (fromJust)
import Control.Monad.Trans.Writer.Strict


import Verifier.SAW.Cache
import Verifier.SAW.Conversion
import qualified Verifier.SAW.Recognizer as R
import Verifier.SAW.SharedTerm hiding (instantiateVarList, incVars)
import qualified Verifier.SAW.SharedTerm as S
import Verifier.SAW.TypedAST
import qualified Verifier.SAW.TermNet as Net

data RewriteRule t
  = RewriteRule { ctxt :: [t], lhs :: t, rhs :: t }
  deriving (Eq, Show, Functor, Foldable, Traversable)
-- ^ Invariant: The set of loose variables in @lhs@ must be exactly
-- @[0 .. length ctxt - 1]@. The @rhs@ may contain a subset of these.


instance Net.Pattern t => Net.Pattern (RewriteRule t) where
  toPat (RewriteRule _ lhs _) = Net.toPat lhs

----------------------------------------------------------------------
-- Matching

-- First-order matching

-- | Equivalent to @(lookup k t, insert k x t)@.
insertLookup :: Ord k => k -> a -> Map k a -> (Maybe a, Map k a)
insertLookup k x t = Map.insertLookupWithKey (\_ a _ -> a) k x t

first_order_match :: (Eq t, Termlike t) => t -> t -> Maybe (Map DeBruijnIndex t)
first_order_match pat term = match pat term Map.empty
  where
    match x y m =
      case (unwrapTermF x, unwrapTermF y) of
        (LocalVar i, _) ->
            case my' of
              Nothing -> Just m'
              Just y' -> if y == y' then Just m' else Nothing
            where (my', m') = insertLookup i y m
        (App x1 x2, App y1 y2) ->
            match x1 y1 m >>= match x2 y2
        (FTermF xf, FTermF yf) ->
            do zf <- zipWithFlatTermF match xf yf
               Foldable.foldl (>=>) Just zf m
        (_, _) ->
            if x == y then Just m else Nothing
-- ^ Precondition: Every loose variable in the pattern @pat@ must
-- occur as the 2nd argument of an @App@ constructor. This ensures
-- that instantiations are well-typed.

----------------------------------------------------------------------
-- Building rewrite rules

eqIdent :: Ident
eqIdent = mkIdent (mkModuleName ["Prelude"]) "Eq"

eqIdent' :: Ident
eqIdent' = mkIdent (mkModuleName ["Prelude"]) "eq"

ecEqIdent :: Ident
ecEqIdent = mkIdent (mkModuleName ["Cryptol"]) "ecEq"

bvEqIdent :: Ident
bvEqIdent = mkIdent (mkModuleName ["Prelude"]) "bvEq"

boolEqIdent :: Ident
boolEqIdent = mkIdent (mkModuleName ["Prelude"]) "boolEq"

vecEqIdent :: Ident
vecEqIdent = mkIdent (mkModuleName ["Prelude"]) "vecEq"

-- | Converts a universally quantified equality proposition from a
-- Term representation to a RewriteRule.
ruleOfTerm :: Termlike t => t -> RewriteRule t
ruleOfTerm t =
    case unwrapTermF t of
      FTermF (DataTypeApp ident [_, x, y])
          | ident == eqIdent -> RewriteRule { ctxt = [], lhs = x, rhs = y }
      Pi _ ty body -> rule { ctxt = ty : ctxt rule }
          where rule = ruleOfTerm body
      _ -> error "ruleOfSharedTerm: Illegal argument"

-- | Converts a universally quantified equality proposition between the
-- two given terms to a RewriteRule.
ruleOfTerms :: Termlike t => t -> t -> RewriteRule t
ruleOfTerms l r = RewriteRule { ctxt = [], lhs = l, rhs = r }

-- | Converts a parameterized equality predicate to a RewriteRule.
ruleOfProp :: SharedTerm s -> RewriteRule (SharedTerm s)
ruleOfProp (R.asLambda -> Just (_, ty, body)) =
  let rule = ruleOfProp body in rule { ctxt = ty : ctxt rule }
ruleOfProp (R.asApplyAll -> (R.isGlobalDef eqIdent' -> Just (), [_, x, y])) =
  RewriteRule { ctxt = [], lhs = x, rhs = y }
ruleOfProp (R.asApplyAll -> (R.isGlobalDef ecEqIdent -> Just (), [_, _, x, y])) =
  RewriteRule { ctxt = [], lhs = x, rhs = y }
ruleOfProp (R.asApplyAll -> (R.isGlobalDef bvEqIdent -> Just (), [_, x, y])) =
  RewriteRule { ctxt = [], lhs = x, rhs = y }
ruleOfProp (R.asApplyAll -> (R.isGlobalDef boolEqIdent -> Just (), [x, y])) =
  RewriteRule { ctxt = [], lhs = x, rhs = y }
ruleOfProp (R.asApplyAll -> (R.isGlobalDef vecEqIdent -> Just (), [_, _, _, x, y])) =
  RewriteRule { ctxt = [], lhs = x, rhs = y }
ruleOfProp t = error $ "ruleOfProp: Predicate not an equation: " ++ show t

-- Create a rewrite rule from an equation.
-- Terms do not have unused variables, so unused variables are introduced
-- as new variables bound after all the used variables.
ruleOfDefEqn :: Ident -> DefEqn Term -> RewriteRule Term
ruleOfDefEqn ident (DefEqn pats rhs@(Term _rtf)) =
      RewriteRule { ctxt = Map.elems varmap
                  , lhs = ruleLhs
                  , rhs = ruleRhs
                  }
  where
    _lvd = emptyLocalVarDoc
        & docShowLocalNames .~ False
        & docShowLocalTypes .~ True
    _varsUnbound t i = freesTerm t `shiftR` i /= 0
    ruleLhs = foldl mkTermApp (Term (FTermF (GlobalDef ident))) args
    ruleRhs = incVars 0 nUnused rhs

    nBound  = sum $ fmap patBoundVarCount  pats
    nUnused = sum $ fmap patUnusedVarCount pats
    n = nBound + nUnused
    mkTermApp :: Term -> Term -> Term
    mkTermApp f x = Term (App f x)

    termOfPat :: Pat Term -> State (Int, Map Int Term) Term
    termOfPat pat =
        case pat of
          PVar _ i tp -> do
            (j, m) <- get
            put (j, Map.insert i tp m)
            return $ Term $ LocalVar (n - 1 - i)
          PUnused i tp -> do
            (j, m) <- get
            put (j + 1, Map.insert j (incVars 0 (j - i) tp) m)
            return $ Term $ LocalVar (n - 1 - j)
          PTuple ps -> (Term . FTermF . TupleValue) <$> traverse termOfPat ps
          PRecord ps -> (Term . FTermF . RecordValue) <$> traverse termOfPat ps
          PCtor c ps -> (Term . FTermF . CtorApp c) <$> traverse termOfPat ps

    (args, (_, varmap)) = runState (traverse termOfPat pats) (nBound, Map.empty)

rulesOfTypedDef :: TypedDef -> [RewriteRule Term]
rulesOfTypedDef def = map (ruleOfDefEqn (defIdent def)) (defEqs def)

-- | Creates a set of rewrite rules from the defining equations of the named constant.
scDefRewriteRules :: SharedContext s -> TypedDef -> IO [RewriteRule (SharedTerm s)]
scDefRewriteRules sc def =
  (traverse . traverse) (scSharedTerm sc) (rulesOfTypedDef def)

-- | Collects rewrite rules from named constants, whose types must be equations.
scEqsRewriteRules :: SharedContext s -> [Ident] -> IO [RewriteRule (SharedTerm s)]
scEqsRewriteRules sc = mapM (scEqRewriteRule sc)

scEqRewriteRule :: SharedContext s -> Ident -> IO (RewriteRule (SharedTerm s))
scEqRewriteRule sc i = ruleOfTerm <$> scTypeOfGlobal sc i

----------------------------------------------------------------------
-- Simpsets

-- | Invariant: 'Simpset's should not contain reflexive rules. We avoid
-- adding them in 'addRule' below.
type Simpset t = Net.Net (Either (RewriteRule t) (Conversion t))

emptySimpset :: Simpset t
emptySimpset = Net.empty

addRule :: (Eq t, Net.Pattern t) => RewriteRule t -> Simpset t -> Simpset t
addRule rule | lhs rule /= rhs rule = Net.insert_term (lhs rule, Left rule)
             | otherwise = id

delRule :: (Eq t, Net.Pattern t) => RewriteRule t -> Simpset t -> Simpset t
delRule rule = Net.delete_term (lhs rule, Left rule)

addRules :: (Eq t, Net.Pattern t) => [RewriteRule t] -> Simpset t -> Simpset t
addRules rules ss = foldr addRule ss rules

addSimp :: (Eq t, Termlike t, Net.Pattern t) => t -> Simpset t -> Simpset t
addSimp prop = addRule (ruleOfTerm prop)

delSimp :: (Eq t, Termlike t, Net.Pattern t) => t -> Simpset t -> Simpset t
delSimp prop = delRule (ruleOfTerm prop)

addConv :: Eq t => Conversion t -> Simpset t -> Simpset t
addConv conv = Net.insert_term (conv, Right conv)

addConvs :: Eq t => [Conversion t] -> Simpset t -> Simpset t
addConvs convs ss = foldr addConv ss convs

scSimpset :: SharedContext s -> [TypedDef] -> [Ident] -> [Conversion (SharedTerm s)] ->
             IO (Simpset (SharedTerm s))
scSimpset sc defs eqIdents convs = do
  defRules <- concat <$> traverse (scDefRewriteRules sc) defs
  eqRules <- mapM (scEqRewriteRule sc) eqIdents
  return $ addRules defRules $ addRules eqRules $ addConvs convs $ emptySimpset

----------------------------------------------------------------------
-- Destructors for terms

asBetaRedex :: (Monad m, Termlike t) => R.Recognizer m t (String, t, t, t)
asBetaRedex t =
    do (f, arg) <- R.asApp t
       (s, ty, body) <- R.asLambda f
       return (s, ty, body, arg)

asTupleRedex :: (Monad m, Termlike t) => R.Recognizer m t ([t], Int)
asTupleRedex t =
    do (x, i) <- R.asTupleSelector t
       ts <- R.asTupleValue x
       return (ts, i)

asRecordRedex :: (Monad m, Termlike t) => R.Recognizer m t (Map FieldName t, FieldName)
asRecordRedex t =
    do (x, i) <- R.asRecordSelector t
       ts <- R.asRecordValue x
       return (ts, i)

----------------------------------------------------------------------
-- Bottom-up rewriting

rewriteTerm :: Simpset Term -> Term -> Term
rewriteTerm ss = rewriteAll
  where
    rewriteAll :: Term -> Term
    rewriteAll t = rewriteTop (rewriteSubterms t)
    rewriteSubterms :: Term -> Term
    rewriteSubterms (Term t) = Term (fmap rewriteAll t)
    rewriteTop :: Term -> Term
    rewriteTop t = apply [ r | Left r <- Net.match_term ss t ] t
    apply :: [RewriteRule Term] -> Term -> Term
    apply [] t = t
    apply (rule : rules) t =
      case first_order_match (lhs rule) t of
        Nothing -> apply rules t
        Just inst -> rewriteAll (instantiateVarList 0 (Map.elems inst) (rhs rule))
-- ^ TODO: implement skeletons (as in Isabelle) to prevent unnecessary
-- re-examination of subterms after applying a rewrite

-- | Like rewriteTerm, but returns an equality theorem instead of just
-- the right-hand side.
{-
rewriteOracle :: Simpset Term -> Term -> Term
rewriteOracle ss lhs = Term (Oracle "rewriter" (Term (EqType lhs rhs)))
  where rhs = rewriteTerm ss lhs
-}
-- TODO: add a constant to the SAWCore prelude to replace defunct "Oracle" constructor:
-- rewriterOracle :: (t : sort 1) -> (x y : t) -> Eq t x y

-- | Do a single reduction step (beta, record or tuple selector) at top
-- level, if possible.
reduceSharedTerm :: SharedContext s -> SharedTerm s -> Maybe (IO (SharedTerm s))
reduceSharedTerm sc (asBetaRedex -> Just (_, _, body, arg)) = Just (instantiateVar sc 0 arg body)
reduceSharedTerm _ (asTupleRedex -> Just (ts, i)) = Just (return (ts !! (i - 1)))
reduceSharedTerm _ (asRecordRedex -> Just (m, i)) = fmap return (Map.lookup i m)
reduceSharedTerm _ _ = Nothing

-- | Rewriter for shared terms
rewriteSharedTerm :: forall s. SharedContext s
                  -> Simpset (SharedTerm s) -> SharedTerm s -> IO (SharedTerm s)
rewriteSharedTerm sc ss t0 =
    do cache <- newCache
       let ?cache = cache in rewriteAll t0
  where
    rewriteAll :: (?cache :: Cache IORef TermIndex (SharedTerm s)) =>
                  SharedTerm s -> IO (SharedTerm s)
    rewriteAll (Unshared tf) =
        traverseTF rewriteAll tf >>= scTermF sc >>= rewriteTop
    rewriteAll (STApp tidx tf) =
        useCache ?cache tidx (traverseTF rewriteAll tf >>= scTermF sc >>= rewriteTop)
    traverseTF :: (a -> IO a) -> TermF a -> IO (TermF a)
    traverseTF _ tf@(Constant _ _ _) = pure tf
    traverseTF f tf = traverse f tf
    rewriteTop :: (?cache :: Cache IORef TermIndex (SharedTerm s)) =>
                  SharedTerm s -> IO (SharedTerm s)
    rewriteTop t =
        case reduceSharedTerm sc t of
          Nothing -> apply (Net.match_term ss t) t
          Just io -> rewriteAll =<< io
    apply :: (?cache :: Cache IORef TermIndex (SharedTerm s)) =>
             [Either (RewriteRule (SharedTerm s)) (Conversion (SharedTerm s))] ->
             SharedTerm s -> IO (SharedTerm s)
    apply [] t = return t
    apply (Left (RewriteRule {lhs, rhs}) : rules) t =
      case first_order_match lhs t of
        Nothing -> apply rules t
        Just inst
          | lhs == rhs ->
            -- This should never happen because we avoid inserting
            -- reflexive rules into simp sets in the first place.
            do putStrLn $ "rewriteSharedTerm: skipping reflexive rule " ++
                          "(THE IMPOSSIBLE HAPPENED!): " ++ show lhs
               apply rules t
          | otherwise ->
            do -- putStrLn "REWRITING:"
               -- print lhs
               rewriteAll =<< S.instantiateVarList sc 0 (Map.elems inst) rhs
    apply (Right conv : rules) t =
        do -- putStrLn "REWRITING:"
           -- print (Net.toPat conv)
           case runConversion conv t of
             Nothing -> apply rules t
             Just tb -> rewriteAll =<< runTermBuilder tb (scTermF sc)

-- | Rewriter for shared terms, returning an unshared term.
rewriteSharedTermToTerm :: forall s. SharedContext s -> Simpset Term -> SharedTerm s -> IO Term
rewriteSharedTermToTerm sc ss t0 =
    do cache <- newCache
       let ?cache = cache in rewriteAll t0
  where
    rewriteAll :: (?cache :: Cache IORef TermIndex Term) => SharedTerm s -> IO Term
    rewriteAll (asBetaRedex -> Just (_, _, body, arg)) =
        instantiateVar sc 0 arg body >>= rewriteAll
    rewriteAll (Unshared tf) =
        liftM Term (traverse rewriteAll tf) >>= rewriteTop
    rewriteAll (STApp tidx tf) =
        useCache ?cache tidx (liftM Term (traverse rewriteAll tf) >>= rewriteTop)
    rewriteTop :: (?cache :: Cache IORef TermIndex Term) => Term -> IO Term
    rewriteTop (asTupleRedex -> Just (ts, i)) = return (ts !! (i - 1))
    rewriteTop (asRecordRedex -> Just (m, i)) = return (fromJust (Map.lookup i m))
    rewriteTop t = apply (Net.match_term ss t) t
    apply :: (?cache :: Cache IORef TermIndex Term) =>
             [Either (RewriteRule Term) (Conversion Term)] -> Term -> IO Term
    apply [] t = return t
    apply (Left (RewriteRule _ lhs rhs) : rules) t =
        case first_order_match lhs t of
          Nothing -> apply rules t
          Just inst -> return (instantiateVarList 0 (Map.elems inst) rhs)
    apply (Right conv : rules) t =
         case runConversion conv t of
             Nothing -> apply rules t
             Just tb -> runTermBuilder tb (return . Term)

-- | Type-safe rewriter for shared terms
rewriteSharedTermTypeSafe
    :: forall s. SharedContext s -> Simpset (SharedTerm s) -> SharedTerm s -> IO (SharedTerm s)
rewriteSharedTermTypeSafe sc ss t0 =
    do cache <- newCache
       let ?cache = cache in rewriteAll t0
  where
    rewriteAll :: (?cache :: Cache IORef TermIndex (SharedTerm s)) =>
                  SharedTerm s -> IO (SharedTerm s)
    rewriteAll (Unshared tf) =
        rewriteTermF tf >>= scTermF sc >>= rewriteTop
    rewriteAll (STApp tidx tf) =
        -- putStrLn "Rewriting term:" >> print t >>
        useCache ?cache tidx (rewriteTermF tf >>= scTermF sc >>= rewriteTop)
    rewriteTermF :: (?cache :: Cache IORef TermIndex (SharedTerm s)) =>
                    TermF (SharedTerm s) -> IO (TermF (SharedTerm s))
    rewriteTermF tf =
        case tf of
          FTermF ftf -> FTermF <$> rewriteFTermF ftf
          App e1 e2 ->
              do t1 <- scTypeOf sc e1
                 case unwrapTermF t1 of
                   -- We only rewrite e2 if type of e1 is not a dependent type.
                   -- This prevents rewriting e2 from changing type of @App e1 e2@.
                   Pi _ _ t | even (looseVars t) -> App <$> rewriteAll e1 <*> rewriteAll e2
                   _ -> App <$> rewriteAll e1 <*> pure e2
          Lambda pat t e -> Lambda pat t <$> rewriteAll e
          Constant{}     -> return tf
          _ -> return tf -- traverse rewriteAll tf
    rewriteFTermF :: (?cache :: Cache IORef TermIndex (SharedTerm s)) =>
                     FlatTermF (SharedTerm s) -> IO (FlatTermF (SharedTerm s))
    rewriteFTermF ftf =
        case ftf of
          TupleValue{}     -> traverse rewriteAll ftf
          TupleType{}      -> return ftf -- doesn't matter
          TupleSelector{}  -> traverse rewriteAll ftf
          RecordValue{}    -> traverse rewriteAll ftf
          RecordSelector{} -> traverse rewriteAll ftf
          RecordType{}     -> return ftf -- doesn't matter
          CtorApp{}        -> return ftf --FIXME
          DataTypeApp{}    -> return ftf -- could treat same as CtorApp
          Sort{}           -> return ftf -- doesn't matter
          NatLit{}         -> return ftf -- doesn't matter
          ArrayValue t es  -> ArrayValue t <$> traverse rewriteAll es
          GlobalDef{}      -> return ftf
          FloatLit{}       -> return ftf
          DoubleLit{}      -> return ftf
          StringLit{}      -> return ftf
          ExtCns{}         -> return ftf
    rewriteTop :: (?cache :: Cache IORef TermIndex (SharedTerm s)) =>
                  SharedTerm s -> IO (SharedTerm s)
    rewriteTop t = apply (Net.match_term ss t) t
    apply :: (?cache :: Cache IORef TermIndex (SharedTerm s)) =>
             [Either (RewriteRule (SharedTerm s)) (Conversion (SharedTerm s))] ->
             SharedTerm s -> IO (SharedTerm s)
    apply [] t = return t
    apply (Left rule : rules) t =
      case first_order_match (lhs rule) t of
        Nothing -> apply rules t
        Just inst -> rewriteAll =<< S.instantiateVarList sc 0 (Map.elems inst) (rhs rule)
    apply (Right conv : rules) t =
      case runConversion conv t of
        Nothing -> apply rules t
        Just tb -> rewriteAll =<< runTermBuilder tb (scTermF sc)

-- | Generate a new SharedContext that normalizes terms as it builds them.
rewritingSharedContext :: forall s. SharedContext s -> Simpset (SharedTerm s) -> SharedContext s
rewritingSharedContext sc ss = sc'
  where
    sc' = sc { scTermF = rewriteTop }

    rewriteTop :: TermF (SharedTerm s) -> IO (SharedTerm s)
    rewriteTop tf = apply (Net.match_term ss t) t
      where t = Unshared tf

    apply :: [Either (RewriteRule (SharedTerm s)) (Conversion (SharedTerm s))] ->
             SharedTerm s -> IO (SharedTerm s)
    apply [] (Unshared tf) = scTermF sc tf
    apply [] (STApp _ tf) = scTermF sc tf
    apply (Left (RewriteRule _ l r) : rules) t =
      case first_order_match l t of
        Nothing -> apply rules t
        Just inst
          | l == r ->
            do putStrLn $ "rewritingSharedContext: skipping reflexive rule: " ++ show l
               apply rules t
          | otherwise -> S.instantiateVarList sc' 0 (Map.elems inst) r
    apply (Right conv : rules) t =
      case runConversion conv t of
        Nothing -> apply rules t
        Just tb -> runTermBuilder tb (scTermF sc')


-- FIXME: is there some way to have sensable term replacement in the presence of loose variables
--  and/or under binders?
replaceTerm :: SharedContext s
            -> Simpset (SharedTerm s)        -- ^ A simpset of rewrite rules to apply along with the replacement
            -> (SharedTerm s, SharedTerm s)  -- ^ (pat,repl) is a tuple of a pattern term to replace and a replacement term
            -> SharedTerm s                  -- ^ the term in which to perform the replacement
            -> IO (SharedTerm s)
replaceTerm sc ss (pat, repl) t = do
    let fvs = looseVars pat
    unless (fvs == 0) $ fail $ unwords
       [ "replaceTerm: term to replace has free variables!", show t ]
    let rule = ruleOfTerms pat repl
    let ss' = addRule rule ss
    rewriteSharedTerm sc ss' t


-------------------------------------------------------------------------------
-- If/then/else hoisting

-- | Find all instances of Prelude.ite in the given term and hoist them
--   higher.  An if/then/else floats upward until it hits a binder that
--   binds one of its free variables, or until it bubbles to the top of
--   the term.  When multiple if/then/else branches bubble to the same
--   place, they will be nested via a canonical term ordering.  This transformation
--   also does rewrites by basic boolean identities.
hoistIfs :: SharedContext s
         -> SharedTerm s
         -> IO (SharedTerm s)
hoistIfs sc t = do
   cache <- newCache

   let app x y = join (scTermF sc <$> (pure App <*> x <*> y))
   itePat <-
          (scFlatTermF sc $ GlobalDef $ "Prelude.ite")
          `app`
          (scTermF sc $ LocalVar 0)
          `app`
          (scTermF sc $ LocalVar 1)
          `app`
          (scTermF sc $ LocalVar 2)
          `app`
          (scTermF sc $ LocalVar 3)

   rules <- map ruleOfTerm <$> mapM (scTypeOfGlobal sc)
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
              , "Prelude.and_True"
              , "Prelude.and_False"
              , "Prelude.and_True2"
              , "Prelude.and_False2"
              , "Prelude.and_idem"
              , "Prelude.or_True"
              , "Prelude.or_False"
              , "Prelude.or_True2"
              , "Prelude.or_False2"
              , "Prelude.or_idem"
              , "Prelude.not_or"
              , "Prelude.not_and"
              ]
   let ss = addRules rules emptySimpset

   (t', conds) <- doHoistIfs sc ss cache itePat =<< rewriteSharedTerm sc ss t
   splitConds sc ss (map fst conds) t'


splitConds :: SharedContext s -> Simpset (SharedTerm s) -> [SharedTerm s] -> SharedTerm s -> IO (SharedTerm s)
splitConds _ _ [] = return
splitConds sc ss (c:cs) = splitCond sc ss c >=> splitConds sc ss cs

splitCond :: SharedContext s -> Simpset (SharedTerm s) -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
splitCond sc ss c t = do
   ty <- scTypeOf sc t
   trueTerm  <- scBool sc True
   falseTerm <- scBool sc False

   then_branch <- replaceTerm sc ss (c, trueTerm) t
   else_branch <- replaceTerm sc ss (c, falseTerm) t
   scGlobalApply sc "Prelude.ite" [ty, c, then_branch, else_branch]

type HoistIfs s = (SharedTerm s, [(SharedTerm s, Set (ExtCns (SharedTerm s)))])


orderTerms :: SharedContext s -> [SharedTerm s] -> IO [SharedTerm s]
orderTerms _sc xs = return $ List.sort xs

doHoistIfs :: forall s. SharedContext s
         -> Simpset (SharedTerm s)
         -> Cache IORef TermIndex (HoistIfs s)
         -> SharedTerm s
         -> SharedTerm s
         -> IO (HoistIfs s)
doHoistIfs sc ss hoistCache itePat = go

 where go :: SharedTerm s -> IO (HoistIfs s)
       go t@(STApp idx tf) = useCache hoistCache idx $ top t tf
       go t@(Unshared tf)  = top t tf

       top :: SharedTerm s -> TermF (SharedTerm s) -> IO (HoistIfs s)
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

       goF :: SharedTerm s -> TermF (SharedTerm s) -> IO (HoistIfs s)

       goF t (LocalVar _)     = return (t, [])
       goF t (Constant _ _ _) = return (t, [])

       goF _ (FTermF ftf) = do
                (ftf', conds) <- runWriterT $ traverse WriterT $ (fmap go ftf)
                t' <- scFlatTermF sc ftf'
                return (t', conds)

       goF _ (App f x) = do
           (f', conds1) <- go f
           (x', conds2) <- go x
           t' <- scApply sc f' x'
           return (t', conds1 ++ conds2)

       goF _ (Let _defs _e) = fail "if hoisting through 'let' not implemented"
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
