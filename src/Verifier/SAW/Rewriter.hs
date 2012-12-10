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
