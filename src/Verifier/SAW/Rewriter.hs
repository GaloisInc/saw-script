{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Verifier.SAW.Rewriter
  ( Simpset
  , emptySimpset
  , ruleOfTerm
  , addSimp
  , delSimp
  , rewriteTerm
  , rewriteSharedTerm
  ) where

import Control.Applicative ((<$>), pure, (<*>))
import Control.Monad ((>=>))
import Control.Monad.Trans (lift)
import qualified Data.Foldable as Foldable
import Data.IORef
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Traversable (Traversable, traverse)

import Verifier.SAW.Cache
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
      FTermF (GlobalDef d) -> Net.Atom (show d)
      FTermF (Sort s)      -> Net.Atom (show s)
      FTermF (NatLit n)    -> Net.Atom ('#' : show n)
      FTermF (App t1 t2)   -> Net.App t1 t2
      _                    -> Net.Var

instance Net.Pattern (SharedTerm s) where
  patternShape (STApp _ t) =
    case t of
      FTermF (GlobalDef d) -> Net.Atom (show d)
      FTermF (Sort s)      -> Net.Atom (show s)
      FTermF (NatLit n)    -> Net.Atom ('#' : show n)
      FTermF (App t1 t2)   -> Net.App t1 t2
      _                    -> Net.Var

----------------------------------------------------------------------
-- Matching

-- First-order matching

type Substitution = Map DeBruijnIndex Term

-- | Equivalent to @(lookup k t, insert k x t)@.
insertLookup :: Ord k => k -> a -> Map k a -> (Maybe a, Map k a)
insertLookup k x t = Map.insertLookupWithKey (\_ a _ -> a) k x t

first_order_match :: (Eq t, Termlike t) => t -> t -> Maybe (Map DeBruijnIndex t)
first_order_match pat term = match pat term Map.empty
  where
    match x y m =
      case (unwrapTermF x, unwrapTermF y) of
        (LocalVar i _, _) ->
            case y' of
              Nothing -> Just m'
              Just y' -> if y == y' then Just m' else Nothing
            where (y', m') = insertLookup i y m
        (FTermF xf, FTermF yf) ->
            do zf <- zipWithFlatTermF match xf yf
               Foldable.foldl (>=>) Just zf m
        (_, _) ->
            if x == y then Just m else Nothing
-- ^ Precondition: Every loose variable in the pattern @pat@ must
-- occur as the 2nd argument of an @App@ constructor. This ensures
-- that instantiations are well-typed.

----------------------------------------------------------------------
-- Simpsets

type Simpset t = Net.Net (RewriteRule t)

eqIdent :: Ident
eqIdent = mkIdent (mkModuleName ["Prelude"]) "Eq"

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

emptySimpset :: Simpset t
emptySimpset = Net.empty

addSimp :: (Eq t, Termlike t, Net.Pattern t) => t -> Simpset t -> Simpset t
addSimp prop = Net.insert_term (lhs rule, rule)
  where rule = ruleOfTerm prop

delSimp :: (Eq t, Termlike t, Net.Pattern t) => t -> Simpset t -> Simpset t
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
      case first_order_match (lhs rule) t of
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
      case first_order_match (lhs rule) t of
        Nothing -> apply rules t
        Just inst -> taint $ rewriteAll (instantiateVarList 0 (Map.elems inst) (rhs rule))

-- | Like rewriteTerm, but returns an equality theorem instead of just
-- the right-hand side.
{-
rewriteOracle :: Simpset Term -> Term -> Term
rewriteOracle ss lhs = Term (Oracle "rewriter" (Term (EqType lhs rhs)))
  where rhs = rewriteTerm ss lhs
-}
-- TODO: add a constant to the SAWCore prelude to replace defunct "Oracle" constructor:
-- rewriterOracle :: (t : sort 1) -> (x y : t) -> Eq t x y

-- | Rewriter for shared terms
rewriteSharedTerm :: forall s. SharedContext s
                  -> Simpset (SharedTerm s) -> SharedTerm s -> IO (SharedTerm s)
rewriteSharedTerm sc ss t =
    do cache <- newCache
       let ?cache = cache in rewriteAll t
  where
    rewriteAll :: (?cache :: Cache IO TermIndex (SharedTerm s)) =>
                  SharedTerm s -> IO (SharedTerm s)
    rewriteAll (STApp tidx tf) =
        useCache ?cache tidx (traverse rewriteAll tf >>= scTermF sc >>= rewriteTop)
    rewriteAll t = return t
    rewriteTop :: (?cache :: Cache IO TermIndex (SharedTerm s)) =>
                  SharedTerm s -> IO (SharedTerm s)
    rewriteTop t = apply (Net.match_term ss t) t
    apply :: (?cache :: Cache IO TermIndex (SharedTerm s)) =>
             [RewriteRule (SharedTerm s)] -> SharedTerm s -> IO (SharedTerm s)
    apply [] t = return t
    apply (rule : rules) t =
      case first_order_match (lhs rule) t of
        Nothing -> apply rules t
        Just inst -> rewriteAll =<< S.instantiateVarList sc 0 (Map.elems inst) (rhs rule)
