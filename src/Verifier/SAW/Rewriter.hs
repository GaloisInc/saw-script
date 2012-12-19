module Verifier.SAW.Rewriter
  ( Simpset
  , emptySimpset
  , addSimp
  , delSimp
  , rewriteTerm
  ) where

import Data.Map (Map)
import qualified Data.Map as Map

import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedAST
import qualified Verifier.SAW.TermNet as Net

-- Context, a.k.a. "Telescope"
-- Loose bound variables in the head index the tail of the list
type Context = [Term]

data RewriteRule =
  RewriteRule
  { ctxt :: Context
  , lhs :: Term
  , rhs :: Term
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

type Simpset = Net.Net RewriteRule

-- | Converts a universally quantified equality proposition from a
-- Term representation to a RewriteRule.
ruleOfTerm :: Term -> RewriteRule
ruleOfTerm (Term (EqType x y)) = RewriteRule { ctxt = [], lhs = x, rhs = y }
ruleOfTerm (Term (Pi _ t e)) = rule { ctxt = t : ctxt rule }
  where rule = ruleOfTerm e
ruleOfTerm _ = error "ruleOfTerm: Illegal argument"

emptySimpset :: Simpset
emptySimpset = Net.empty

addSimp :: Term -> Simpset -> Simpset
addSimp prop = Net.insert_term (lhs rule, rule)
  where rule = ruleOfTerm prop

delSimp :: Term -> Simpset -> Simpset
delSimp prop = Net.delete_term (lhs rule, rule)
  where rule = ruleOfTerm prop

----------------------------------------------------------------------
-- Bottom-up rewriting

rewriteTerm :: Simpset -> Term -> Term
rewriteTerm ss = rewriteAll
  where
    rewriteAll :: Term -> Term
    rewriteAll t = rewriteTop (rewriteSubterms t)
    rewriteSubterms :: Term -> Term
    rewriteSubterms (Term t) = Term (fmap rewriteAll t)
    rewriteTop :: Term -> Term
    rewriteTop t = apply (Net.match_term ss t) t
    apply :: [RewriteRule] -> Term -> Term
    apply [] t = t
    apply (rule : rules) t =
      case first_order_match (ctxt rule) (lhs rule) t of
        Nothing -> apply rules t
        Just inst -> rewriteAll (instantiateVarList 0 (Map.elems inst) t)
-- ^ TODO: implement skeletons (as in Isabelle) to prevent unnecessary
-- re-examination of subterms after applying a rewrite

-- | Like rewriteTerm, but returns an equality theorem instead of just
-- the right-hand side.
rewriteOracle :: Simpset -> Term -> Term
rewriteOracle ss lhs = Term (Oracle "rewriter" (Term (EqType lhs rhs)))
  where rhs = rewriteTerm ss lhs
