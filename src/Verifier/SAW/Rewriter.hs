{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

module Verifier.SAW.Rewriter
  ( Simpset
  , RewriteRule
  , emptySimpset
  , ruleOfTerm
  , ruleOfDefEqn
  , rulesOfTypedDef
  , addRule
  , delRule
  , addRules
  , addSimp
  , delSimp
  , addConv
  , addConvs
  , rewriteTerm
  , rewriteSharedTerm
  , rewriteSharedTermTypeSafe
  ) where

import Control.Applicative ((<$>), pure, (<*>))
import Control.Monad ((>=>))
import Control.Monad.State
import Control.Monad.Trans (lift)
import Data.Foldable (Foldable)
import qualified Data.Foldable as Foldable
import Data.IORef
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Traversable (Traversable, traverse)

import Verifier.SAW.Cache
import Verifier.SAW.Change
import Verifier.SAW.Conversion
import Verifier.SAW.SharedTerm hiding (instantiateVarList)
import qualified Verifier.SAW.SharedTerm as S
import Verifier.SAW.TypedAST
import qualified Verifier.SAW.TermNet as Net

-- Context, a.k.a. "Telescope"
-- Loose bound variables in the head index the tail of the list
type Context = [Term]

data RewriteRule t
  = RewriteRule { ctxt :: [t], lhs :: t, rhs :: t }
  deriving (Eq, Show, Functor, Foldable, Traversable)
-- ^ Invariant: The set of loose variables in @lhs@ must be exactly
-- @[0 .. length ctxt - 1]@. The @rhs@ may contain a subset of these.

-- | A hack to allow storage of conversions in a term net.
instance Eq (Conversion t) where
    x == y = Net.toPat x == Net.toPat y

instance Show (Conversion t) where
    show x = show (Net.toPat x)

termToPat :: Termlike t => t -> Net.Pat
termToPat t =
    case unwrapTermF t of
      FTermF (GlobalDef d)      -> Net.Atom (show d)
      FTermF (Sort s)           -> Net.Atom ('*' : show s)
      FTermF (NatLit n)         -> Net.Atom (show n)
      FTermF (App t1 t2)        -> Net.App (termToPat t1) (termToPat t2)
      FTermF (DataTypeApp c ts) -> foldl Net.App (Net.Atom (show c)) (map termToPat ts)
      FTermF (CtorApp c ts)     -> foldl Net.App (Net.Atom (show c)) (map termToPat ts)
      _                     -> Net.Var

instance Net.Pattern Term where
  toPat = termToPat

instance Net.Pattern (SharedTerm s) where
  toPat = termToPat

instance Net.Pattern t => Net.Pattern (RewriteRule t) where
  toPat (RewriteRule _ lhs _) = Net.toPat lhs

----------------------------------------------------------------------
-- Simplification procedures

-- belongs in SharedTerm.hs
scBool :: SharedContext s -> Bool -> IO (SharedTerm s)
scBool sc True = scFlatTermF sc (CtorApp (mkIdent (mkModuleName ["Prelude"]) "True") [])
scBool sc False = scFlatTermF sc (CtorApp (mkIdent (mkModuleName ["Prelude"]) "False") [])

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

type Simpset t = Net.Net (Either (RewriteRule t) (Conversion t))

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

ruleOfDefEqn :: Ident -> DefEqn Term -> RewriteRule Term
ruleOfDefEqn ident (DefEqn pats rhs) =
    RewriteRule { ctxt = Map.elems varmap
                , lhs = foldl mkApp (Term (FTermF (GlobalDef ident))) args
                , rhs = incVars 0 nUnused rhs }
  where
    nBound = sum (map patBoundVarCount pats)
    nUnused = sum (map patUnusedVarCount pats)
    n = nBound + nUnused
    mkApp :: Term -> Term -> Term
    mkApp f x = Term (FTermF (App f x))
    termOfPat :: Pat Term -> State (Int, Map Int Term) Term
    termOfPat pat =
        case pat of
          PVar s i e ->
              do (j, m) <- get
                 put (j, Map.insert i e m)
                 return $ Term (LocalVar (n - 1 - i) (incVars 0 (n - i) e))
          PUnused i e ->
              do (j, m) <- get
                 let s = "_" ++ show j
                 put (j + 1, Map.insert j (incVars 0 (j - i) e) m)
                 return $ Term (LocalVar (n - 1 - j) (incVars 0 (n - i) e))
          PTuple pats -> (Term . FTermF . TupleValue) <$> traverse termOfPat pats
          PRecord pats -> (Term . FTermF . RecordValue) <$> traverse termOfPat pats
          PCtor c pats -> (Term . FTermF . CtorApp c) <$> traverse termOfPat pats
    (args, (_, varmap)) = runState (traverse termOfPat pats) (nBound, Map.empty)

rulesOfTypedDef :: TypedDef -> [RewriteRule Term]
rulesOfTypedDef def = map (ruleOfDefEqn (defIdent def)) (defEqs def)

emptySimpset :: Simpset t
emptySimpset = Net.empty

addRule :: (Eq t, Net.Pattern t) => RewriteRule t -> Simpset t -> Simpset t
addRule rule = Net.insert_term (lhs rule, Left rule)

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

----------------------------------------------------------------------
-- Destructors for terms

asApp :: Termlike t => t -> Maybe (t, t)
asApp (unwrapTermF -> FTermF (App x y)) = Just (x, y)
asApp _ = Nothing

asLambda :: Termlike t => t -> Maybe (String, t, t)
asLambda (unwrapTermF -> Lambda (PVar s 0 _) ty body) = Just (s, ty, body)
asLambda _ = Nothing

asTupleValue :: Termlike t => t -> Maybe [t]
asTupleValue (unwrapTermF -> FTermF (TupleValue ts)) = Just ts
asTupleValue _ = Nothing

asRecordValue :: Termlike t => t -> Maybe (Map FieldName t)
asRecordValue (unwrapTermF -> FTermF (RecordValue m)) = Just m
asRecordValue _ = Nothing

asTupleSelector :: Termlike t => t -> Maybe (t, Int)
asTupleSelector (unwrapTermF -> FTermF (TupleSelector t i)) = Just (t, i)
asTupleSelector _ = Nothing

asRecordSelector :: Termlike t => t -> Maybe (t, FieldName)
asRecordSelector (unwrapTermF -> FTermF (RecordSelector t i)) = Just (t, i)
asRecordSelector _ = Nothing

asBetaRedex :: Termlike t => t -> Maybe (String, t, t, t)
asBetaRedex t =
    do (f, arg) <- asApp t
       (s, ty, body) <- asLambda f
       return (s, ty, body, arg)

asTupleRedex :: Termlike t => t -> Maybe ([t], Int)
asTupleRedex t =
    do (x, i) <- asTupleSelector t
       ts <- asTupleValue x
       return (ts, i)

asRecordRedex :: Termlike t => t -> Maybe (Map FieldName t, FieldName)
asRecordRedex t =
    do (x, i) <- asRecordSelector t
       ts <- asRecordValue x
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

rewriteTermChange :: Simpset Term -> Term -> Change Term
rewriteTermChange ss = rewriteAll
  where
    rewriteAll :: Term -> Change Term
    rewriteAll t = rewriteSubterms t >>= rewriteTop
    rewriteSubterms :: Term -> Change Term
    rewriteSubterms t@(Term tf) = preserve t $ Term <$> traverse rewriteAll tf
    rewriteTop :: Term -> Change Term
    rewriteTop t = apply [ r | Left r <- Net.match_term ss t ] t
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

-- | Do a single reduction step (beta, record or tuple selector) at top
-- level, if possible.
reduceSharedTerm :: SharedContext s -> SharedTerm s -> Maybe (IO (SharedTerm s))
reduceSharedTerm sc (asBetaRedex -> Just (_, _, body, arg)) = Just (instantiateVar sc 0 arg body)
reduceSharedTerm sc (asTupleRedex -> Just (ts, i)) = Just (return (ts !! (i - 1)))
reduceSharedTerm sc (asRecordRedex -> Just (m, i)) = fmap return (Map.lookup i m)
reduceSharedTerm _ _ = Nothing

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
    rewriteTop t =
        case reduceSharedTerm sc t of
          Nothing -> apply (Net.match_term ss t) t
          Just io -> rewriteAll =<< io
    apply :: (?cache :: Cache IO TermIndex (SharedTerm s)) =>
             [Either (RewriteRule (SharedTerm s)) (Conversion (SharedTerm s))] ->
             SharedTerm s -> IO (SharedTerm s)
    apply [] t = return t
    apply (Left (RewriteRule _ lhs rhs) : rules) t =
      case first_order_match lhs t of
        Nothing -> apply rules t
        Just inst ->
            do putStrLn "REWRITING:"
               print lhs
               rewriteAll =<< S.instantiateVarList sc 0 (Map.elems inst) rhs
    apply (Right conv : rules) t =
        do putStrLn "REWRITING:"
           print (Net.toPat conv)
           case runConversion conv t of
             Nothing -> apply rules t
             Just tb -> rewriteAll =<< runTermBuilder tb (scTermF sc)

-- | Type-safe rewriter for shared terms
rewriteSharedTermTypeSafe
    :: forall s. SharedContext s -> Simpset (SharedTerm s) -> SharedTerm s -> IO (SharedTerm s)
rewriteSharedTermTypeSafe sc ss t =
    do cache <- newCache
       let ?cache = cache in rewriteAll t
  where
    rewriteAll :: (?cache :: Cache IO TermIndex (SharedTerm s)) =>
                  SharedTerm s -> IO (SharedTerm s)
    rewriteAll t@(STApp tidx tf) =
        putStrLn "Rewriting term:" >> print t >>
        useCache ?cache tidx (rewriteTermF tf >>= scTermF sc >>= rewriteTop)
    rewriteAll t = return t
    rewriteTermF :: (?cache :: Cache IO TermIndex (SharedTerm s)) =>
                    TermF (SharedTerm s) -> IO (TermF (SharedTerm s))
    rewriteTermF tf =
        case tf of
          FTermF ftf -> FTermF <$> rewriteFTermF ftf
          Lambda pat t e -> Lambda pat t <$> rewriteAll e
          _ -> return tf -- traverse rewriteAll tf
    rewriteFTermF :: (?cache :: Cache IO TermIndex (SharedTerm s)) =>
                     FlatTermF (SharedTerm s) -> IO (FlatTermF (SharedTerm s))
    rewriteFTermF ftf =
        case ftf of
          App e1 e2 ->
              do t1 <- scTypeOf sc e1
                 case unwrapTermF t1 of
                   Pi _ _ t | even (looseVars t) -> App <$> rewriteAll e1 <*> rewriteAll e2
                   _ -> App <$> rewriteAll e1 <*> pure e2
          TupleValue{} -> traverse rewriteAll ftf
          TupleType{} -> return ftf -- doesn't matter
          TupleSelector{} -> traverse rewriteAll ftf
          RecordValue{} -> traverse rewriteAll ftf
          RecordSelector{} -> traverse rewriteAll ftf
          RecordType{} -> return ftf -- doesn't matter
          CtorApp ident es -> return ftf --FIXME
          DataTypeApp{} -> return ftf -- could treat same as CtorApp
          Sort{} -> return ftf -- doesn't matter
          NatLit{} -> return ftf -- doesn't matter
          ArrayValue t es -> ArrayValue t <$> traverse rewriteAll es
    rewriteTop :: (?cache :: Cache IO TermIndex (SharedTerm s)) =>
                  SharedTerm s -> IO (SharedTerm s)
    rewriteTop t = apply (Net.match_term ss t) t
    apply :: (?cache :: Cache IO TermIndex (SharedTerm s)) =>
             [Either (RewriteRule (SharedTerm s)) (Conversion (SharedTerm s))] ->
             SharedTerm s -> IO (SharedTerm s)
    apply [] t = return t
    apply (Left rule : rules) t =
      case first_order_match (lhs rule) t of
        Nothing -> apply rules t
        Just inst -> rewriteAll =<< S.instantiateVarList sc 0 (Map.elems inst) (rhs rule)
