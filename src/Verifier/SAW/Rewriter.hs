{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

module Verifier.SAW.Rewriter
  -- * Rewrite rules
  ( RewriteRule
  , ruleOfTerm
  , ruleOfDefEqn
  , rulesOfTypedDef
  , scDefRewriteRules
  , scEqsRewriteRules
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
  , asApp
  ) where

import Control.Applicative ((<$>), pure, (<*>))
import Control.Lens
import Control.Monad.Identity
import Control.Monad.State
import Data.Bits
import Data.Foldable (Foldable)
import qualified Data.Foldable as Foldable
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromJust)

import Verifier.SAW.Cache
import Verifier.SAW.Conversion
import Verifier.SAW.Recognizer
import Verifier.SAW.SharedTerm hiding (instantiateVarList)
import qualified Verifier.SAW.SharedTerm as S
import Verifier.SAW.TypedAST
import qualified Verifier.SAW.TermNet as Net

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
      FTermF (GlobalDef d)      -> Net.Atom (identName d)
      FTermF (Sort s)           -> Net.Atom ('*' : show s)
      FTermF (NatLit n)         -> Net.Atom (show n)
      FTermF (App t1 t2)        -> Net.App (termToPat t1) (termToPat t2)
      FTermF (DataTypeApp c ts) -> foldl Net.App (Net.Atom (identName c)) (map termToPat ts)
      FTermF (CtorApp c ts)     -> foldl Net.App (Net.Atom (identName c)) (map termToPat ts)
      _                         -> Net.Var

instance Net.Pattern Term where
  toPat = termToPat

instance Net.Pattern (SharedTerm s) where
  toPat = termToPat

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
        (LocalVar i _, _) ->
            case my' of
              Nothing -> Just m'
              Just y' -> if y == y' then Just m' else Nothing
            where (my', m') = insertLookup i y m
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
    ruleLhs = foldl mkApp (Term (FTermF (GlobalDef ident))) args
    ruleRhs = incVars 0 nUnused rhs

    nBound  = sum $ fmap patBoundVarCount  pats
    nUnused = sum $ fmap patUnusedVarCount pats
    n = nBound + nUnused
    mkApp :: Term -> Term -> Term
    mkApp f x = Term (FTermF (App f x))

    termOfPat :: Pat Term -> State (Int, Map Int Term) Term
    termOfPat pat =
        case pat of
          PVar _ i tp -> do
            (j, m) <- get
            put (j, Map.insert i tp m)
            let tp' = incVars 0 (n - i) tp
            return $ Term $ LocalVar (n - 1 - i) tp'
          PUnused i tp -> do
            (j, m) <- get
            put (j + 1, Map.insert j (incVars 0 (j - i) tp) m)
            return $ Term $ LocalVar (n - 1 - j) (incVars 0 (n - i) tp)
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
scEqsRewriteRules sc idents = map ruleOfTerm <$> mapM (scTypeOfGlobal sc) idents

----------------------------------------------------------------------
-- Simpsets

type Simpset t = Net.Net (Either (RewriteRule t) (Conversion t))

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

scSimpset :: SharedContext s -> [TypedDef] -> [Ident] -> [Conversion (SharedTerm s)] ->
               IO (Simpset (SharedTerm s))
scSimpset sc defs eqIdents convs = do
  defRules <- concat <$> traverse (scDefRewriteRules sc) defs
  eqRules <- scEqsRewriteRules sc eqIdents
  return $ addRules defRules $ addRules eqRules $ addConvs convs $ emptySimpset

----------------------------------------------------------------------
-- Destructors for terms

asLambda :: Termlike t => Recognizer t (String, t, t)
asLambda (unwrapTermF -> Lambda (PVar s 0 _) ty body) = Just (s, ty, body)
asLambda _ = Nothing

asTupleValue :: Termlike t => Recognizer t [t]
asTupleValue t = do TupleValue ts <- asFTermF t; return ts

asTupleSelector :: Termlike t => Recognizer t (t, Int)
asTupleSelector t = do TupleSelector u i <- asFTermF t; return (u,i)

asRecordValue :: Termlike t => Recognizer t (Map FieldName t)
asRecordValue t = do RecordValue m <- asFTermF t; return m

asRecordSelector :: Termlike t => t -> Maybe (t, FieldName)
asRecordSelector t = do RecordSelector u i <- asFTermF t; return (u,i)

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
    rewriteAll :: (?cache :: Cache IO TermIndex (SharedTerm s)) =>
                  SharedTerm s -> IO (SharedTerm s)
    rewriteAll (STApp tidx tf) =
        useCache ?cache tidx (traverse rewriteAll tf >>= scTermF sc >>= rewriteTop)
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
    apply (Left (RewriteRule {lhs, rhs}) : rules) t =
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

-- | Rewriter for shared terms, returning an unshared term.
rewriteSharedTermToTerm ::
    forall s. SharedContext s -> Simpset Term -> SharedTerm s -> IO Term
rewriteSharedTermToTerm sc ss t0 =
    do cache <- newCache
       let ?cache = cache in rewriteAll t0
  where
    rewriteAll :: (?cache :: Cache IO TermIndex Term) => SharedTerm s -> IO Term
    rewriteAll (asBetaRedex -> Just (_, _, body, arg)) =
        instantiateVar sc 0 arg body >>= rewriteAll
    rewriteAll (STApp tidx tf) =
        useCache ?cache tidx (liftM Term (traverse rewriteAll tf) >>= rewriteTop)
    rewriteTop :: (?cache :: Cache IO TermIndex Term) => Term -> IO Term
    rewriteTop (asTupleRedex -> Just (ts, i)) = return (ts !! (i - 1))
    rewriteTop (asRecordRedex -> Just (m, i)) = return (fromJust (Map.lookup i m))
    rewriteTop t = apply (Net.match_term ss t) t
    apply :: (?cache :: Cache IO TermIndex Term) =>
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
    rewriteAll :: (?cache :: Cache IO TermIndex (SharedTerm s)) =>
                  SharedTerm s -> IO (SharedTerm s)
    rewriteAll t@(STApp tidx tf) =
        putStrLn "Rewriting term:" >> print t >>
        useCache ?cache tidx (rewriteTermF tf >>= scTermF sc >>= rewriteTop)
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
                   -- We only rewrite e2 if type of e1 is not a dependent type.
                   -- This prevents rewriting e2 from changing type of @App e1 e2@.
                   Pi _ _ t | even (looseVars t) -> App <$> rewriteAll e1 <*> rewriteAll e2
                   _ -> App <$> rewriteAll e1 <*> pure e2
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
          ExtCns{}         -> return ftf
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
    rewriteTop tf =
      let t = STApp (-1) tf in
      case reduceSharedTerm sc' t of
        Nothing -> apply (Net.match_term ss t) t
        Just io -> io
    apply :: [Either (RewriteRule (SharedTerm s)) (Conversion (SharedTerm s))] ->
             SharedTerm s -> IO (SharedTerm s)
    apply [] (STApp _ tf) = scTermF sc tf
    apply (Left (RewriteRule _ l r) : rules) t =
      case first_order_match l t of
        Nothing -> apply rules t
        Just inst -> S.instantiateVarList sc' 0 (Map.elems inst) r
    apply (Right conv : rules) t =
      case runConversion conv t of
        Nothing -> apply rules t
        Just tb -> runTermBuilder tb (scTermF sc')
