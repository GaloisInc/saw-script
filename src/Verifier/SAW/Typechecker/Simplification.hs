{-# LANGUAGE ScopedTypeVariables #-}
module Verifier.SAW.Typechecker.Simplification
  ( PatVarParser
  , addPatBindings
  , runPatVarParser
  , patBoundVars
  , tryMatchPat
  , Subst
  , extendPatContext
  , reduce
  , reduceToPiExpr
  ) where

import Control.Applicative
import Control.Arrow (second)
import Control.Monad.Error (ErrorT(..), throwError)
import Control.Monad.State (State, execState, StateT(..), modify)
import Control.Monad.Trans
import Data.Foldable
import Data.Traversable
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Vector as V
import Data.Vector (Vector)
import Text.PrettyPrint
import Prelude hiding (foldr, mapM_)

import Verifier.SAW.Position
import Verifier.SAW.Typechecker.Context
import Verifier.SAW.Typechecker.Monad


type PatVarParser = State (Map Int (String,TCTerm)) ()

addPatBindings :: TCPat -> PatVarParser
addPatBindings (TCPVar nm i tp) = modify $ Map.insert i (nm,tp)
addPatBindings TCPUnused{} = return ()
addPatBindings (TCPatF pf) = traverse_ addPatBindings pf 

runPatVarParser :: PatVarParser -> [(String,TCTerm)]
runPatVarParser pvp = Map.elems (execState pvp Map.empty)

patBoundVars :: TCPat -> [(String,TCTerm)]
patBoundVars pat = runPatVarParser (addPatBindings pat)

extendPatContext :: TermContext s -> TCPat -> TermContext s
extendPatContext tc0 pat = foldr (uncurry consBoundVar) tc0 (patBoundVars pat)

type Subst = Vector TCTerm

type Matcher s = StateT (Map Int TCTerm) (ErrorT String (TC s))

runMatcher :: Matcher s a -> TC s (Maybe (a, Subst))
runMatcher m = fmap finish $ runErrorT $ runStateT m Map.empty
  where finish Left{} = Nothing
        finish (Right p) = Just (second (V.fromList . Map.elems) p)

-- | Attempt to match term against a pat, returns reduced term that matches.
attemptMatch :: TermContext s -> TCPat -> TCTerm -> Matcher s TCTerm
attemptMatch _ (TCPVar _ i _) t = t <$ modify (Map.insert i t)
attemptMatch _ TCPUnused{} t = return t
attemptMatch tc (TCPatF pf) t = do
  let go = attemptMatch tc
  rt <- lift $ lift $ reduce tc t
  case (pf, rt) of
    (UPTuple pl, TCF (UTupleValue tl)) | length pl == length tl ->
      TCF . UTupleValue <$> sequenceA (zipWith go pl tl)
    (UPRecord pm, TCF (URecordValue tm)) | Map.keys pm == Map.keys tm ->
      TCF . URecordValue <$> sequenceA (Map.intersectionWith go pm tm)
    (UPCtor cp pl, TCF (UCtorApp ct tl)) | cp == ct ->
      TCF . UCtorApp ct <$> sequenceA (zipWith go pl tl)
    _ -> lift $ throwError "Pattern match failed."

-- | Match untyped term against pattern, returning variables in reverse order.
-- so that last-bound variable is first.  Also returns the term after it was matched.
-- This may differ to the input term due to the use of reduction during matching.
tryMatchPat :: TermContext s
            -> TCPat -> TCTerm -> TC s (Maybe (TermContext s, Subst, TCTerm))
tryMatchPat tc pat t = do
    fmap (fmap finish) $ runMatcher (attemptMatch tc pat t)
  where finish (r,args) = (tc', args, r)
          where tc' = extendPatContext tc pat

-- | Match untyped term against pattern, returning variables in reverse order.
-- so that last-bound variable is first.  Also returns the term after it was matched.
-- This may differ to the input term due to the use of reduction during matching.
tryMatchPatList :: TermContext s
                -> [TCPat]
                -> [TCTerm]
                -> TC s (Maybe ( TermContext s
                               , Subst
                               , [TCTerm]))
tryMatchPatList tc pats terms =
    fmap (fmap finish) $ runMatcher (go pats terms)
  where go (pat:pl) (term:tl) =
          attemptMatch tc pat term >> go pl tl
        go [] tl = return tl
        go _ [] = fail "Insufficient number of terms"
        finish (tl,args) = (tc', args, tl)
          where bindings = runPatVarParser (mapM_ addPatBindings pats)
                tc' = foldr (uncurry consBoundVar) tc bindings

reduce :: TermContext s -> TCTerm -> TC s TCTerm
reduce tc t =
  case tcAsApp t of
    (TCF (URecordSelector r f), a) -> do
      r' <- reduce tc r
      case r' of
        TCF (URecordValue m) ->
          case Map.lookup f m of
            Just v -> reduce tc (tcMkApp v a)
            Nothing -> fail "Missing record field in reduce"
        _ -> return t
    (TCLambda pat _ rhs, a0:al) -> do
      r <- tryMatchPat tc pat a0
      case r of
        Nothing -> return t
        Just (tc',sub,_) -> reduce tc (tcMkApp t' al)
          where t' = tcApply tc (tc',rhs) (tc,sub)
    (TCF (UGlobal g), al) -> do
        -- Get global equations.
        m <- tryEval (globalDefEqns g tc)
        case m of
          Nothing -> return t
          Just eqs -> procEqs eqs
      where procEqs [] = return t
            procEqs (DefEqnGen pats rhs:eql) = do
              m <- tryMatchPatList tc pats al
              case m of
                Nothing -> procEqs eql
                Just (tc', sub, rest) -> reduce tc (tcMkApp g' rest)
                  where g' = tcApply tc (tc',rhs) (tc,V.reverse sub)
    _ -> return t

-- | Attempt to reduce a term to a  pi expression, returning the pattern, type
-- of the pattern and the right-hand side.
-- Reports error if htis fails.
reduceToPiExpr :: TermContext s -> Pos -> TCTerm -> TC s (TCPat, TCTerm, TCTerm)
reduceToPiExpr tc p tp = do
  rtp <- reduce tc tp
  case rtp of
    TCPi pat l r -> return (pat,l,r)
    _ -> tcFailD p $ text "Unexpected argument to term with type:" $$
                         nest 2 (ppTCTerm tc 0 rtp)