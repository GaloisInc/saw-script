{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Verifier.SAW.Rewriter
  ( Simpset
  , emptySimpset
  , addSimp
  , delSimp
  , rewriteTerm
  ) where

import Control.Applicative ((<$>), pure, (<*>))
import Control.Monad.Trans (lift)
import Data.IORef
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Traversable (Traversable, traverse)

import Verifier.SAW.Change
import Verifier.SAW.SharedTerm hiding (instantiateVarList)
import qualified Verifier.SAW.SharedTerm as S
import Verifier.SAW.TypedAST
import qualified Verifier.SAW.TermNet as Net

-- Context, a.k.a. "Telescope"
-- Loose bound variables in the head index the tail of the list
type Context = [Term]

data RewriteRule t =
  RewriteRule
  { ctxt :: [t]
  , lhs :: t
  , rhs :: t
  }
  deriving (Eq, Show)
-- ^ Invariant: The set of loose variables in @lhs@ must be exactly
-- @[0 .. length ctxt - 1]@. The @rhs@ may contain a subset of these.

instance Net.Pattern Term where
  patternShape (Term t) =
    case t of
      GlobalDef d -> Net.Atom (show (defIdent d))
      Sort s      -> Net.Atom (show s)
      IntLit n    -> Net.Atom ('#' : show n)
      App t1 t2   -> Net.App t1 t2
      _           -> Net.Var

instance Net.Pattern (SharedTerm s) where
  patternShape (STApp _ t) =
    case t of
      GlobalDef d -> Net.Atom (show (defIdent d))
      Sort s      -> Net.Atom (show s)
      IntLit n    -> Net.Atom ('#' : show n)
      App t1 t2   -> Net.App t1 t2
      _           -> Net.Var

----------------------------------------------------------------------
-- Matching

-- First-order matching

type Substitution = Map DeBruijnIndex Term

-- | Equivalent to @(lookup k t, insert k x t)@.
insertLookup :: Ord k => k -> a -> Map k a -> (Maybe a, Map k a)
insertLookup k x t = Map.insertLookupWithKey (\_ a _ -> a) k x t

first_order_match :: Context -> Term -> Term -> Maybe Substitution
first_order_match _ pat term = matchGeneric unwrapTerm pat term
  where unwrapTerm (Term tf) = tf

matchSharedTerm :: SharedTerm s -> SharedTerm s -> Maybe (Map DeBruijnIndex (SharedTerm s))
matchSharedTerm pat term = matchGeneric unwrapSharedTerm pat term

matchGeneric :: Eq t => (t -> TermF t) -> t -> t -> Maybe (Map DeBruijnIndex t)
matchGeneric unwrap pat term = match pat term Map.empty
  where
    match x y m =
      case (unwrap x, unwrap y) of
        (LocalVar i _, _) ->
            case y' of
              Nothing -> Just m'
              Just y' -> if y == y' then Just m' else Nothing
            where (y', m') = insertLookup i y m
        (App x1 x2, App y1 y2) ->
            match x1 y1 m >>= match x2 y2
        (_, _) ->
            if x == y then Just m else Nothing
-- ^ Precondition: Every loose variable in the pattern @pat@ must
-- occur as the 2nd argument of an @App@ constructor. This ensures
-- that instantiations are well-typed.

----------------------------------------------------------------------
-- Simpsets

type Simpset t = Net.Net (RewriteRule t)

-- | Converts a universally quantified equality proposition from a
-- Term representation to a RewriteRule.
ruleOfTerm :: Term -> RewriteRule Term
ruleOfTerm (Term (EqType x y)) = RewriteRule { ctxt = [], lhs = x, rhs = y }
ruleOfTerm (Term (Pi _ t e)) = rule { ctxt = t : ctxt rule }
  where rule = ruleOfTerm e
ruleOfTerm _ = error "ruleOfTerm: Illegal argument"

emptySimpset :: Simpset t
emptySimpset = Net.empty

addSimp :: Term -> Simpset Term -> Simpset Term
addSimp prop = Net.insert_term (lhs rule, rule)
  where rule = ruleOfTerm prop

delSimp :: Term -> Simpset Term -> Simpset Term
delSimp prop = Net.delete_term (lhs rule, rule)
  where rule = ruleOfTerm prop

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
    rewriteTop t = apply (Net.match_term ss t) t
    apply :: [RewriteRule Term] -> Term -> Term
    apply [] t = t
    apply (rule : rules) t =
      case first_order_match (ctxt rule) (lhs rule) t of
        Nothing -> apply rules t
        Just inst -> rewriteAll (instantiateVarList 0 (Map.elems inst) (rhs rule))
-- ^ TODO: implement skeletons (as in Isabelle) to prevent unnecessary
-- re-examination of subterms after applying a rewrite

rewriteTermChange :: Simpset Term -> Term -> Change Term
rewriteTermChange ss = rewriteAll
  where
    rewriteAll :: Term -> Change Term
    rewriteAll t = rewriteSubterms t >>= rewriteTop
    rewriteSubterms :: Term -> Change Term
    rewriteSubterms t@(Term tf) = preserve t $ Term <$> traverse rewriteAll tf
    rewriteTop :: Term -> Change Term
    rewriteTop t = apply (Net.match_term ss t) t
    apply :: [RewriteRule Term] -> Term -> Change Term
    apply [] t = pure t
    apply (rule : rules) t =
      case first_order_match (ctxt rule) (lhs rule) t of
        Nothing -> apply rules t
        Just inst -> taint $ rewriteAll (instantiateVarList 0 (Map.elems inst) (rhs rule))

-- | Like rewriteTerm, but returns an equality theorem instead of just
-- the right-hand side.
rewriteOracle :: Simpset Term -> Term -> Term
rewriteOracle ss lhs = Term (Oracle "rewriter" (Term (EqType lhs rhs)))
  where rhs = rewriteTerm ss lhs

-- | Rewriter for shared terms
rewriteSharedTerm :: forall s. (?sc :: SharedContext s) =>
                     Simpset (SharedTerm s) -> SharedTerm s -> IO (SharedTerm s)
rewriteSharedTerm ss t =
    do ref <- newIORef Map.empty
       let ?ref = ref in rewriteAll t
  where
    rewriteAll :: (?ref :: IORef (Map TermIndex (SharedTerm s))) =>
                  SharedTerm s -> IO (SharedTerm s)
    rewriteAll (STApp tidx tf) =
        memoizeIO ?ref tidx (traverse rewriteAll tf >>= scTermF >>= rewriteTop)
    rewriteAll t = return t
    rewriteTop :: (?ref :: IORef (Map TermIndex (SharedTerm s))) =>
                  SharedTerm s -> IO (SharedTerm s)
    rewriteTop t = apply (Net.match_term ss t) t
    apply :: (?ref :: IORef (Map TermIndex (SharedTerm s))) =>
             [RewriteRule (SharedTerm s)] -> SharedTerm s -> IO (SharedTerm s)
    apply [] t = return t
    apply (rule : rules) t =
      case matchSharedTerm (lhs rule) t of
        Nothing -> apply rules t
        Just inst -> rewriteAll =<< S.instantiateVarList 0 (Map.elems inst) (rhs rule)
