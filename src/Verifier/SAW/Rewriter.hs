module Verifier.SAW.Rewriter where

import Data.Map (Map)
import qualified Data.Map as Map

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

first_order_match :: Context -> Term -> Term -> Maybe Substitution
first_order_match ctxt pat term = match pat term Map.empty
  where
    match (Term (LocalVar i _)) y m =
      case y' of
        Nothing -> Just m'
        Just y' -> if y == y' then Just m' else Nothing
      where (y', m') = Map.insertLookupWithKey (\_ a _ -> a) i y m
    match (Term (App x1 x2)) (Term (App y1 y2)) m =
      match x1 y1 m >>= match x2 y2
    match x y m =
      if x == y then Just m else Nothing


-- Bottom-up rewriting

type Simpset = Net.Net RewriteRule

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

