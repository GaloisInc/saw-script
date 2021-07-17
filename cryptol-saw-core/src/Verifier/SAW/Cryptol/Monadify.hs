{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE OverloadedStrings #-}

{- |
Module      : Verifier.SAW.Cryptol.Monadify
Copyright   : Galois, Inc. 2021
License     : BSD3
Maintainer  : westbrook@galois.com
Stability   : experimental
Portability : non-portable (language extensions)

This module implements a "monadification" transformation, which converts "pure"
SAW core terms that use inconsistent operations like @fix@ and convert them to
monadic SAW core terms that use monadic versions of these operations that are
consistent. The monad that is used is the @CompM@ monad that is axiomatized in
the SAW cxore prelude. This is only a partial transformation, meaning that it
will fail on some SAW core terms. Specifically, it requires that all
applications @f arg@ in a term either have a non-dependent function type for @f@
(i.e., a function with type @'Pi' x a b@ where @x@ does not occur in @b@) or a
pure argument @arg@ that does not use any of the inconsistent operations.

FIXME: explain this better

MT(Pi x (sort 0) b) = Pi x (sort 0) CompMT(b)
MT(Pi x Num b) = Pi x Num CompMT(b)
MT(Pi _ a b) = MT(a) -> CompMT(b)
MT(#(a,b)) = #(MT(a),MT(b))
MT(f arg) = f MT(arg)  -- NOTE: f must be a pure function!
MT(cnst) = cnst
MT(dt args) = dt MT(args)
MT(x) = x
MT(_) = error

CompMT(tp = Pi _ _ _) = MT(tp)
CompMT(n : Num) = n
CompMT(tp) = CompM MT(tp)

-- NOTE: polymorphic functions like Pi x (sort 0) x have a CompM return type
-- even if x is a function type. OR: we could make this a Haskell-level
-- function!

MonArg(t : tp) ==> MT(tp)
MonArg(t) =
  case Mon(t) of
    m : CompM MT(a) => shift \k -> m >>= \x -> k x
    _ => t

Mon(t : tp) ==> MT(tp) or CompMT(tp)  (which are the same type for pis)
Mon((f : Pi x a b) arg) = Mon(f) MT(arg)
Mon((f : Pi _ a b) arg) = Mon(f) MonArg(arg)
Mon(Lambda x a t) = Lambda x MT(a) Mon(t)
Mon((t,u)) = (MonArg(t),MonArg(u))
Mon(c args) = c MonArg(args)
Mon(x) = x
Mon(fix) = fixM (of some form...)
Mon(cnst) = cnstM  if cnst is impure and monadifies to constM
Mon(cnst) = cnst   otherwise
-}

module Verifier.SAW.Cryptol.Monadify where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Cont
import qualified Control.Monad.Fail as Fail
-- import Control.Monad.IO.Class (MonadIO, liftIO)

import Verifier.SAW.Name
import Verifier.SAW.Term.Functor
import Verifier.SAW.SharedTerm
import Verifier.SAW.OpenTerm
import Verifier.SAW.SCTypeCheck
import Verifier.SAW.Recognizer
import Verifier.SAW.Position


----------------------------------------------------------------------
-- * Typing All Subterms
----------------------------------------------------------------------

-- | A SAW core term where all of the subterms are typed
data TypedSubsTerm
  = TypedSubsTerm { tpSubsIndex :: Maybe TermIndex,
                    tpSubsFreeVars :: BitSet,
                    tpSubsTermF :: TermF TypedSubsTerm,
                    tpSubsTypeF :: TermF TypedSubsTerm,
                    tpSubsSort :: Sort }

-- | Convert a 'Term' to a 'TypedSubsTerm'
typeAllSubterms :: SharedContext -> Term -> IO TypedSubsTerm
typeAllSubterms = error "FIXME HERE"

-- | Convert a 'TypedSubsTerm' back to a 'Term'
typedSubsTermTerm :: TypedSubsTerm -> Term
typedSubsTermTerm = error "FIXME HERE"

-- | Get the type of a 'TypedSubsTerm' as a 'TypedSubsTerm'
typedSubsTermType :: TypedSubsTerm -> TypedSubsTerm
typedSubsTermType tst =
  TypedSubsTerm { tpSubsIndex = Nothing, tpSubsFreeVars = tpSubsFreeVars tst,
                  tpSubsTermF = tpSubsTypeF tst,
                  tpSubsTypeF = FTermF (Sort $ tpSubsSort tst),
                  tpSubsSort = sortOf (tpSubsSort tst) }

-- | Count the number of right-nested pi-abstractions of a 'TypedSubsTerm'
typedSubsTermArity :: TypedSubsTerm -> Int
typedSubsTermArity (TypedSubsTerm { tpSubsTermF = Pi _ _ tst }) =
  1 + typedSubsTermArity tst
typedSubsTermArity _ = 0

-- | Count the number of right-nested pi abstractions in a term, which
-- represents a type. This assumes that the type is in WHNF.
typeArity :: Term -> Int
typeArity tp = length $ fst $ asPiList tp

class ToTerm a where
  toTerm :: a -> Term

instance ToTerm Term where
  toTerm = id

instance ToTerm TypedSubsTerm where
  toTerm = typedSubsTermTerm

unsharedApply :: Term -> Term -> Term
unsharedApply f arg = Unshared $ App f arg


----------------------------------------------------------------------
-- * Monadifying Types
----------------------------------------------------------------------

data MonKind = MKType Sort | MKNum | MKFun MonKind MonKind deriving Eq

-- | Convert a kind to a SAW core sort, if possible
monKindToSort :: MonKind -> Maybe Sort
monKindToSort (MKType s) = Just s
monKindToSort _ = Nothing

-- | Convert a 'MonKind' to the term it represents
monKindOpenTerm :: MonKind -> OpenTerm
monKindOpenTerm (MKType s) = sortOpenTerm s
monKindOpenTerm MKNum = globalOpenTerm "Cryptol.Num"
monKindOpenTerm (MKFun k1 k2) =
  arrowOpenTerm "_" (monKindOpenTerm k1) (monKindOpenTerm k2)

data MonType
  = MTyForall LocalName MonKind (MonType -> MonType)
  | MTyArrow MonType MonType
  | MTyTuple [MonType]
  | MTyRecord [(FieldName, MonType)]
  | MTyBase MonKind OpenTerm -- A "base type" or type var of a given kind
  | MTyNum OpenTerm

-- | Make a base type of sort 0 from an 'OpenTerm'
mkMonType0 :: OpenTerm -> MonType
mkMonType0 = MTyBase (MKType $ mkSort 0)

-- | Test that a monadification type is monomorphic, i.e., has no foralls
monTypeIsMono :: MonType -> Bool
monTypeIsMono (MTyForall _ _ _) = False
monTypeIsMono (MTyArrow t1 t2) = monTypeIsMono t1 && monTypeIsMono t2
monTypeIsMono (MTyTuple tps) = all monTypeIsMono tps
monTypeIsMono (MTyRecord tps) = all (monTypeIsMono . snd) tps
monTypeIsMono (MTyBase _ _) = True
monTypeIsMono (MTyNum _) = True

-- | Test if a monadification type @tp@ is considered a base type, meaning that
-- @CompMT(tp) = CompM tp@
isBaseType :: MonType -> Bool
isBaseType (MTyForall _ _ _) = False
isBaseType (MTyArrow _ _) = False
isBaseType (MTyTuple _) = True
isBaseType (MTyRecord _) = True
isBaseType (MTyBase (MKType _) _) = True
isBaseType (MTyBase _ _) = True
isBaseType (MTyNum _) = False

-- | Get the kind of a 'MonType', assuming it has one
monTypeKind :: MonType -> Maybe MonKind
monTypeKind (MTyForall _ _ _) = Nothing
monTypeKind (MTyArrow t1 t2) =
  do s1 <- monTypeKind t1 >>= monKindToSort
     s2 <- monTypeKind t2 >>= monKindToSort
     return $ MKType $ maxSort [s1, s2]
monTypeKind (MTyTuple tps) =
  do sorts <- mapM (monTypeKind >=> monKindToSort) tps
     return $ MKType $ maxSort sorts
monTypeKind (MTyRecord tps) =
  do sorts <- mapM (monTypeKind . snd >=> monKindToSort) tps
     return $ MKType $ maxSort sorts
monTypeKind (MTyBase k _) = Just k
monTypeKind (MTyNum _) = Just MKNum

-- | Get the 'Sort' @s@ of a 'MonType' if it has kind @'MKType' s@
monTypeSort :: MonType -> Maybe Sort
monTypeSort = monTypeKind >=> monKindToSort

-- | Convert a SAW core 'Term' to a monadification kind, if possible
monadifyKind :: Term -> Maybe MonKind
monadifyKind (asDataType -> Just (num, []))
  | primName num == "Cryptol.Num" = return MKNum
monadifyKind (asSort -> Just s) = return $ MKType s
monadifyKind (asPi -> Just (_, tp_in, tp_out)) =
  MKFun <$> monadifyKind tp_in <*> monadifyKind tp_out
monadifyKind _ = Nothing

-- | Get the kind of a type constructor with kind @k@ applied to type @t@, or
-- return 'Nothing' if the kinds do not line up
applyKind :: MonKind -> MonType -> Maybe MonKind
applyKind (MKFun k1 k2) t
  | Just kt <- monTypeKind t
  , kt == k1 = Just k2
applyKind _ _ = Nothing

-- | Perform 'applyKind' for 0 or more argument types
applyKinds :: MonKind -> [MonType] -> Maybe MonKind
applyKinds = foldM applyKind

-- | Convert a 'MonType' to the argument type @MT(tp)@ it represents
monTypeArgType :: MonType -> OpenTerm
monTypeArgType (MTyForall x k body) =
  piOpenTerm x (monKindOpenTerm k) (\tp -> monTypeCompType (body $ MTyBase k tp))
monTypeArgType (MTyArrow t1 t2) =
  arrowOpenTerm "_" (monTypeArgType t1) (monTypeCompType t2)
monTypeArgType (MTyTuple tps) =
  tupleTypeOpenTerm $ map monTypeArgType tps
monTypeArgType (MTyRecord tps) =
  recordTypeOpenTerm $ map (\(f,tp) -> (f, monTypeArgType tp)) tps
monTypeArgType (MTyBase _ t) = t
monTypeArgType (MTyNum n) = n

-- | Convert a 'MonType' to the computation type @CompMT(tp)@ it represents
monTypeCompType :: MonType -> OpenTerm
monTypeCompType mtp@(MTyForall _ _ _) = monTypeArgType mtp
monTypeCompType mtp@(MTyArrow _ _) = monTypeArgType mtp
monTypeCompType mtp =
  applyOpenTerm (globalOpenTerm "Prelude.CompM") (monTypeArgType mtp)

-- | A context of local variables used for monadifying types, which includes the
-- variable names, their original types (before monadification), and, if their
-- types corespond to 'MonKind's, a local 'MonType' that quantifies over them
type MonadifyTypeCtx = [(LocalName,Term,Maybe MonType)]

ppTermInTypeCtx :: MonadifyTypeCtx -> Term -> String
ppTermInTypeCtx ctx t =
  scPrettyTermInCtx defaultPPOpts (map (\(x,_,_) -> x) ctx) t

mkTermBaseType :: MonadifyTypeCtx -> MonKind -> Term -> MonType
mkTermBaseType ctx k t =
  MTyBase k $ openOpenTerm (map (\(x,tp,_) -> (x,tp)) ctx) t

-- | Convert a SAW core 'Term' to a monadification type
monadifyType :: MonadifyTypeCtx -> Term -> MonType
monadifyType ctx (asPi -> Just (x, tp_in, tp_out))
  | Just k <- monadifyKind tp_in =
    MTyForall x k (\tp' -> monadifyType ((x,tp_in,Just tp'):ctx) tp_out)
monadifyType ctx tp@(asPi -> Just (_, _, tp_out))
  | inBitSet 0 (looseVars tp_out) =
    error ("monadifyType: " ++
           "dependent function type with non-kind argument type: " ++
           ppTermInTypeCtx ctx tp)
monadifyType ctx tp@(asPi -> Just (x, tp_in, tp_out)) =
  MTyArrow (monadifyType ctx tp_in)
  (monadifyType ((x,tp,Nothing):ctx) tp_out)
monadifyType ctx (asTupleType -> Just tps) =
  MTyTuple (map (monadifyType ctx) tps)
monadifyType ctx (asRecordType -> Just tps) =
  MTyRecord $ map (\(fld,tp) -> (fld, monadifyType ctx tp)) $ Map.toList tps
monadifyType ctx tp@(asDataType -> Just (pn, args))
  | Just pn_k <- monadifyKind (primType pn)
  , tps <- map (monadifyType ctx) args
  , Just k_out <- applyKinds pn_k tps =
    mkTermBaseType ctx k_out tp
monadifyType ctx tp@(asApplyAll -> (f, args@(_:_)))
  | Just (ec, _) <- asConstant f
  , Just ec_k <- monadifyKind (ecType ec)
  , tps <- map (monadifyType ctx) args
  , Just k_out <- applyKinds ec_k tps =
    mkTermBaseType ctx k_out tp
monadifyType ctx (asLocalVar -> Just i)
  | i < length ctx
  , (_,_,Just tp) <- ctx!!i = tp
monadifyType ctx tp =
  error ("monadifyType: not a valid type for monadification: "
         ++ ppTermInTypeCtx ctx tp)


----------------------------------------------------------------------
-- * Monadified Terms
----------------------------------------------------------------------

data ArgMonTerm
  = BaseMonTerm MonType OpenTerm
  | FunMonTerm LocalName MonType MonType (ArgMonTerm -> MonTerm)
  | ForallMonTerm LocalName MonKind (MonType -> MonTerm)

data MonTerm
  = ArgMonTerm ArgMonTerm
  | CompMonTerm MonType OpenTerm

-- | Get the type of a argument term
argMonTermType :: ArgMonTerm -> MonType
argMonTermType (BaseMonTerm tp _) = tp
argMonTermType (ForallMonTerm x k body) = MTyForall x k (monTermType . body)
argMonTermType (FunMonTerm _ tp_in tp_out _) = MTyArrow tp_in tp_out

-- | Get the type of a monadification term, irrespective of if it is pure or not
monTermType :: MonTerm -> MonType
monTermType (ArgMonTerm t) = argMonTermType t
monTermType (CompMonTerm tp _) = tp

-- | Apply a monadified term to a type or term argument
applyMonTerm :: MonTerm -> Either MonType ArgMonTerm -> MonTerm
applyMonTerm (ArgMonTerm (FunMonTerm _ _ _ f)) (Right arg) = f arg
applyMonTerm (ArgMonTerm (ForallMonTerm _ _ f)) (Left mtp) = f mtp
applyMonTerm _ _ = error "applyMonTerm: application at incorrect type"

-- | Apply a monadified term to 0 or more arguments
applyMonTermMulti :: MonTerm -> [Either MonType ArgMonTerm] -> MonTerm
applyMonTermMulti = foldl applyMonTerm

-- | Convert an 'ArgMonTerm' to a SAW core term of type @CompMT(tp)@
argMonTermCompTerm :: ArgMonTerm -> OpenTerm
argMonTermCompTerm (BaseMonTerm tp t) =
  applyOpenTermMulti (globalOpenTerm "Prelude.returnM")
  [monTypeArgType tp, t]
argMonTermCompTerm (FunMonTerm x tp_in _ body) =
  lambdaOpenTerm x (monTypeArgType tp_in) (monTermCompTerm . body
                                            . mkArgMonTerm tp_in)
argMonTermCompTerm (ForallMonTerm x k body) =
  lambdaOpenTerm x (monKindOpenTerm k) (monTermCompTerm . body . MTyBase k)

-- | Convert a 'MonTerm' to a SAW core term of type @CompMT(tp)@
monTermCompTerm :: MonTerm -> OpenTerm
monTermCompTerm (ArgMonTerm amtrm) = argMonTermCompTerm amtrm
monTermCompTerm (CompMonTerm _ trm) = trm

-- | Convert an 'ArgMonTerm' to a SAW core term of type @MT(tp)@
argMonTermArgTerm :: ArgMonTerm -> OpenTerm
argMonTermArgTerm (BaseMonTerm _ t) = t
argMonTermArgTerm t = argMonTermCompTerm t

-- | Build an 'ArgMonTerm' from an 'OpenTerm' of argument type
mkArgMonTerm :: MonType -> OpenTerm -> ArgMonTerm
mkArgMonTerm (MTyForall x k body) t =
  ForallMonTerm x k (\tp -> mkMonTerm (body tp) (applyOpenTerm t $
                                                 monTypeArgType tp))
mkArgMonTerm (MTyArrow t1 t2) t =
  FunMonTerm "_" t1 t2 (\x -> mkMonTerm t2 $
                              applyOpenTerm t $ argMonTermArgTerm x)
mkArgMonTerm tp trm | isBaseType tp = BaseMonTerm tp trm
mkArgMonTerm _ _ = error "mkArgMonTerm: malformed type for term"

-- | Build a 'MonTerm' from an 'OpenTerm' of argument type
mkMonTerm :: MonType -> OpenTerm -> MonTerm
mkMonTerm tp t = ArgMonTerm $ mkArgMonTerm tp t

-- | Build a 'MonTerm' from a global of a given argument type. Note that this
-- only works for first-order types, i.e., where the global does not take in any
-- functions (though it can take in type variables).
mkGlobalMonTerm :: MonType -> Ident -> MonTerm
mkGlobalMonTerm tp ident = mkMonTerm tp (globalOpenTerm ident)

-- | Build a 'MonTerm' that 'fail's when converted to a term
failMonTerm :: MonType -> String -> MonTerm
failMonTerm tp str = mkMonTerm tp (failOpenTerm str)


----------------------------------------------------------------------
-- * The Monadification Monad
----------------------------------------------------------------------

-- | An environment of named definitions that have already been monadified
type MonadifyEnv = Map Ident MonTerm

-- | A context for monadifying 'Term's which maintains, for each deBruijn index
-- in scope, both its original un-monadified type along with either a 'MonTerm'
-- or 'MonType' for the translation of the variable to a local variable of
-- monadified type or monadified kind
type MonadifyCtx = [(LocalName,Term,Either MonType MonTerm)]

-- | The read-only state of a monadification computation
data MonadifyROState = MonadifyROState {
  -- | The monadification environment
  monStEnv :: MonadifyEnv,
  -- | The monadification context 
  monStCtx :: MonadifyCtx,
  -- | The monadified return type of the top-level term being monadified
  monStTopRetType :: OpenTerm
}

-- | The state of a monadification computation = a memoization table
type MonadifyState = Map TermIndex MonTerm

-- | The monad for monadifying SAW core terms
newtype MonadifyM a =
  MonadifyM { unMonadifyM ::
                ReaderT MonadifyROState (StateT MonadifyState
                                         (Cont MonTerm)) a }
  deriving (Functor, Applicative, Monad,
            MonadReader MonadifyROState, MonadState MonadifyState)

instance Fail.MonadFail MonadifyM where
  fail str =
    do ret_tp <- topRetType
       shiftMonadifyM $ \_ -> failMonTerm (mkMonType0 ret_tp) str

-- | Capture the current continuation and pass it to a function, which must
-- return the final computation result. Note that this is slightly differnet
-- from normal shift, and I think corresponds to the C operator, but my quick
-- googling couldn't find the right name...
shiftMonadifyM :: ((a -> MonTerm) -> MonTerm) -> MonadifyM a
shiftMonadifyM f = MonadifyM $ lift $ lift $ cont f

-- | Locally run a 'MonadifyM' computation with an empty memoization table,
-- making all binds be local to that computation, and return the result
resetMonadifyM :: OpenTerm -> MonadifyM MonTerm -> MonadifyM MonTerm
resetMonadifyM ret_tp m =
  do ro_st <- ask
     return $ runMonadifyM (monStEnv ro_st) (monStCtx ro_st) ret_tp m

-- | Get the monadified return type of the top-level term being monadified
topRetType :: MonadifyM OpenTerm
topRetType = monStTopRetType <$> ask

-- | Run a monadification computation
--
-- FIXME: document the arguments
runMonadifyM :: MonadifyEnv -> MonadifyCtx -> OpenTerm -> MonadifyM MonTerm ->
                MonTerm
runMonadifyM env ctx top_ret_tp m =
  let ro_st = MonadifyROState env ctx top_ret_tp in
  runCont (evalStateT (runReaderT (unMonadifyM m) ro_st) Map.empty) id

-- | Run a monadification computation using a mapping for identifiers that have
-- already been monadified and generate a SAW core term
runCompleteMonadifyM :: MonadIO m => SharedContext -> MonadifyEnv -> Term ->
                        MonadifyM MonTerm -> m Term
runCompleteMonadifyM sc env top_ret_tp m =
  liftIO $ completeOpenTerm sc $ monTermCompTerm $
  runMonadifyM env [] (monTypeArgType $ monadifyType [] top_ret_tp) m

-- | Memoize a computation of the monadified term associated with a 'TermIndex'
memoizingM :: TermIndex -> MonadifyM MonTerm -> MonadifyM MonTerm
memoizingM i m =
  (Map.lookup i <$> get) >>= \case
  Just ret  -> return ret
  Nothing ->
    do ret <- m
       modify (Map.insert i ret)
       return ret

-- | Turn a 'MonTerm' of type @CompMT(tp)@ to a term of argument type @MT(tp)@
-- by inserting a monadic bind if the 'MonTerm' is computational
argifyMonTerm :: MonTerm -> MonadifyM ArgMonTerm
argifyMonTerm (ArgMonTerm mtrm) = return mtrm
argifyMonTerm (CompMonTerm mtp trm) =
  do let tp = monTypeArgType mtp
     top_ret_tp <- topRetType
     shiftMonadifyM $ \k ->
       CompMonTerm (mkMonType0 top_ret_tp) $
       applyOpenTermMulti (globalOpenTerm "Prelude.bindM")
       [tp, top_ret_tp, trm,
        lambdaOpenTerm "x" tp (monTermCompTerm . k . mkArgMonTerm mtp)]


----------------------------------------------------------------------
-- * Monadification
----------------------------------------------------------------------


{-
Mon(t : tp) ==> MT(tp) or CompMT(tp)  (which are the same type for pis)
Mon((f : Pi x a b) arg) = Mon(f) MT(arg)
Mon((f : Pi _ a b) arg) = Mon(f) MonArg(arg)
Mon(Lambda x a t) = Lambda x MT(a) Mon(t)
Mon((t,u)) = (MonArg(t),MonArg(u))
Mon(c args) = c MonArg(args)
Mon(x) = x
Mon(fix) = fixM (of some form...)
Mon(cnst) = cnstM  if cnst is impure and monadifies to constM
Mon(cnst) = cnst   otherwise
-}

mondifyArg :: MonType -> Term -> MonadifyM ArgMonTerm
mondifyArg mtp t = monadifyTerm mtp t >>= argifyMonTerm

monadifyTerm :: MonType -> Term -> MonadifyM MonTerm
monadifyTerm mtp t@(STApp { stAppIndex = ix }) =
  memoizingM ix $ monadifyTerm' mtp t
monadifyTerm mtp t = monadifyTerm' mtp t

monadifyTerm' :: MonType -> Term -> MonadifyM MonTerm
monadifyTerm' mtp@(MTyForall _ _ _) t =
  ask >>= \ro_st ->
  return $ monadifyLambdas (monStEnv ro_st) (monStCtx ro_st) mtp t
monadifyTerm' mtp@(MTyArrow _ _) t =
  ask >>= \ro_st ->
  return $ monadifyLambdas (monStEnv ro_st) (monStCtx ro_st) mtp t

-- | FIXME: documentation; get our type down to a base type before going into
-- the MonadifyM monad
monadifyLambdas :: MonadifyEnv -> MonadifyCtx -> MonType -> Term -> MonTerm
monadifyLambdas env ctx (MTyForall _ k tp_f) (asLambda ->
                                              Just (x, x_tp, body)) =
  -- FIXME: check that monadifyKind x_tp == k
  ArgMonTerm $ ForallMonTerm x k $ \mtp ->
  monadifyLambdas env ((x,x_tp,Left mtp) : ctx) (tp_f mtp) body
monadifyLambdas env ctx (MTyArrow tp_in tp_out) (asLambda ->
                                                 Just (x, x_tp, body)) =
  -- FIXME: check that monadifyType x_tp == tp_in
  ArgMonTerm $ FunMonTerm x tp_in tp_out $ \arg ->
  monadifyLambdas env ((x,x_tp,Right (ArgMonTerm arg)) : ctx) tp_out body
monadifyLambdas env ctx tp t =
  monadifyEtaExpand env ctx tp tp t []

monadifyEtaExpand :: MonadifyEnv -> MonadifyCtx -> MonType ->
                     MonType -> Term -> [Either MonType ArgMonTerm] -> MonTerm
monadifyEtaExpand env ctx top_mtp (MTyForall x k tp_f) t args =
  ArgMonTerm $ ForallMonTerm x k $ \mtp ->
  monadifyEtaExpand env ctx top_mtp (tp_f mtp) t (args ++ [Left mtp])
monadifyEtaExpand env ctx top_mtp (MTyArrow tp_in tp_out) t args =
  ArgMonTerm $ FunMonTerm "_" tp_in tp_out $ \arg ->
  monadifyEtaExpand env ctx top_mtp tp_out t (args ++ [Right arg])
monadifyEtaExpand env ctx top_mtp mtp t args =
  applyMonTermMulti
  (runMonadifyM env ctx (monTypeArgType mtp) (monadifyTerm top_mtp t))
  args


{-
-- | Monadify a 'Term' and then purify it using 'purifyMonTerm'
monadifyPure :: Monadify a => a -> MonadifyM OpenTerm
monadifyPure = monadify >=> purifyMonTerm

-- | Monadify a term and run the resulting computation
monadifyTermAndRun :: MonadifyEnv -> MonadifyCtx -> Term -> MonTerm
monadifyTermAndRun env ctx trm =
  let m_tp =
        bindTCMOpenTerm
        (do tp <-
              atPos (Pos "debug1" "debug1" 0 0)
              (liftTCM scTypeOf' (map fst ctx) trm >>= typeCheckWHNF)
            tp_tp <-
              atPos (Pos "debug2" "debug2" 0 0)
              (liftTCM scTypeOf' (map fst ctx) tp >>= typeCheckWHNF)
            sort <- case asSort tp_tp of
              Just sort -> return sort
              Nothing -> error "Monadification: type of type is not a sort!"
            return (tp,sort)) $ \(tp,sort) ->
        monTermForcePure "Monadification failed: type is impure" $
        runMonadifyM env ctx (sortOpenTerm sort) (monadify tp) in
  runMonadifyM env ctx m_tp $ monadify trm

-- | Monadify a 'TypedSubsTerm' and run the resulting computation
monadifyTSTermAndRun :: MonadifyEnv -> MonadifyCtx -> TypedSubsTerm -> MonTerm
monadifyTSTermAndRun env ctx tst =
  let tp =
        monTermForcePure "Monadification failed: type is impure" $
        runMonadifyM env ctx (sortOpenTerm $ tpSubsSort tst) (monadify tst) in
  runMonadifyM env ctx tp $ monadify tst

-- | Monadify a term in a context that has been extended with an additional free
-- variable, whose type is given by the first argument. Return a function over
-- that variable.
monadifyInBinding :: Term -> Term -> MonadifyM (OpenTerm -> MonTerm)
monadifyInBinding tp tst =
  do ro_st <- ask
     return $ \x_trm ->
       monadifyTermAndRun (monStEnv ro_st) ((tp,x_trm) : monStCtx ro_st) tst

-- | Monadify a term in a context that has been extended with an additional free
-- variable, whose type is given by the first argument. Return a function over
-- that variable.
monadifyTSInBinding :: Term -> TypedSubsTerm -> MonadifyM (OpenTerm -> MonTerm)
monadifyTSInBinding tp tst =
  do ro_st <- ask
     return $ \x_trm ->
       monadifyTSTermAndRun (monStEnv ro_st) ((tp,x_trm) : monStCtx ro_st) tst

-- | Test if the first term has dependent function type, and, if so, return a
-- failure 'OpenTerm', otherwise return the second 'OpenTerm'
failIfDepFun :: [Term] -> Term -> OpenTerm -> OpenTerm
failIfDepFun t_ctx t1 t2 =
  bindTCMOpenTerm (liftTCM scTypeOf' t_ctx t1 >>= typeCheckWHNF) $ \case
  (asPi -> Just (_, _, tp_out))
    | inBitSet 0 (looseVars tp_out) ->
      failOpenTerm ("Monadification failed: dependent function "
                    ++ "applied to impure argument")
  _ -> t2

-- | FIXME HERE: documentation: t1 is the untranslated form of mtrm1
monadifyApply :: MonTerm -> MonTerm -> MonadifyM MonTerm
monadifyApply mtrm1 mtrm2 =
  do -- t_ctx <- map fst <$> monStCtx <$> ask
     let mtrm2' =
           -- If t1 has a dependent type and t2 is not pure then monadification
           -- fails. We represent this changing mtrm2 to a failure OpenTerm if
           -- it is computational.
           {-
           case mtrm2 of
             CompMonTerm tp trm ->
               CompMonTerm tp $ failIfDepFun t_ctx t1 trm
             _ -> mtrm2 -}
           -- FIXME: figure out how to detect this error!
           mtrm2
     case mtrm1 of
       -- If t1 is a pure function, apply it
       FunMonTerm _ _ body_f ->
         body_f <$> purifyMonTerm mtrm2'

       -- Otherwise, purify t1 to a monadic function and apply it
       _ ->
         do trm1 <- purifyMonTerm mtrm1
            trm2 <- purifyMonTerm mtrm2'
            return $ CompMonTerm
              (applyOpenTerm trm1 trm2)
              (applyPiOpenTerm (monTermPureType mtrm1) trm2)

-- | FIXME HERE: documentation
monadifyApplyMulti :: MonTerm -> [MonTerm] -> MonadifyM MonTerm
monadifyApplyMulti = foldM monadifyApply

-- | Generic function to monadify terms
class Monadify a where
  monadify :: a -> MonadifyM MonTerm

instance Monadify Term where
  monadify (STApp { stAppIndex = i, stAppTermF = tf}) =
    memoizingM i $ monadify tf
  monadify (Unshared tf) =
    monadify tf

instance Monadify TypedSubsTerm where
  monadify (TypedSubsTerm { tpSubsIndex = Just i, tpSubsTermF = tf}) =
     memoizingM i $ monadify tf
  monadify (TypedSubsTerm { tpSubsIndex = Nothing, tpSubsTermF = tf}) =
    monadify tf


instance Monadify (TermF Term) where
  monadify (FTermF ftf) = monadify ftf
  monadify (App t1 t2) =
    do mtrm1 <- monadify t1
       mtrm2 <- monadify t2
       monadifyApply mtrm1 mtrm2

  monadify (Lambda x tp body) =
    do tp' <- monadifyPure tp
       body_f <- monadifyInBinding tp body
       return $ FunMonTerm x tp' body_f

  monadify (Pi x tp body) =
    do tp' <- monadifyPure tp
       body_f <- monadifyInBinding tp body
       retPure $ piOpenTerm x tp' $
         monTermForcePure "Monadification failed: body of pi is impure" . body_f

  monadify (LocalVar ix) =
    do ctx <- monStCtx <$> ask
       retPure $ snd (ctx!!ix)

  monadify (Constant ec _t) =
    do env <- monStEnv <$> ask
       case ecName ec of
         ModuleIdentifier ident
           | Just mtrm <- Map.lookup ident env ->
             return mtrm
         _ ->
           -- FIXME: if a definition is not in the environment, we just unfold
           -- it; is this correct?
           --monadify t
           fail ("Monadification failed: no translation for constant: "
                 ++ show (toAbsoluteName $ ecName ec))


instance Monadify (TermF TypedSubsTerm) where
  monadify (FTermF ftf) = monadify ftf
  monadify (App t1 t2) =
    ((,) <$> monadify t1 <*> monadify t2) >>= \case

    -- If t1 has a dependent type and t2 is not pure then monadification fails
    (_, mtrm2)
      | isCompTerm mtrm2
      , Pi _ _ tp_out <- tpSubsTypeF t1
      , inBitSet 0 (tpSubsFreeVars tp_out) ->
        fail ("Monadification failed: "
              ++ "dependent function applied to impure argument")

    -- If t1 is a pure function, apply it
    (FunMonTerm _ _ body_f, mtrm2) ->
      body_f <$> purifyMonTerm mtrm2

    -- Otherwise, purify t1 to a monadic function and apply it
    (mtrm1, mtrm2) ->
      do trm1 <- purifyMonTerm mtrm1
         trm2 <- purifyMonTerm mtrm2
         return $ CompMonTerm
           (applyOpenTerm trm1 trm2)
           (applyPiOpenTerm (monTermPureType mtrm1) trm2)

  monadify (Lambda x tp body) =
    do tp' <- monadifyPure tp
       body_f <- monadifyTSInBinding (typedSubsTermTerm tp) body
       return $ FunMonTerm x tp' body_f

  monadify (Pi x tp body) =
    do tp' <- monadifyPure tp
       body_f <- monadifyTSInBinding (typedSubsTermTerm tp) body
       retPure $ piOpenTerm x tp' $
         monTermForcePure "Monadification failed: body of pi is impure" . body_f

  monadify (LocalVar ix) =
    do ctx <- monStCtx <$> ask
       retPure $ snd (ctx!!ix)

  monadify (Constant ec _t) =
    do env <- monStEnv <$> ask
       case ecName ec of
         ModuleIdentifier ident
           | Just mtrm <- Map.lookup ident env ->
             return mtrm
         _ ->
           -- FIXME: if a definition is not in the environment, we just unfold
           -- it; is this correct?
           --monadify t
           fail ("Monadification failed: no translation for constant: "
                 ++ show (toAbsoluteName $ ecName ec))


instance (Monadify a, ToTerm a) => Monadify (FlatTermF a) where
  monadify (Primitive nm) =
    do env <- monStEnv <$> ask
       case Map.lookup (primName nm) env of
         Just mtrm -> return mtrm
         Nothing ->
           error ("Monadification failed: no translation for primitive: "
                  ++ show (primName nm))
           -- NOTE: we could assume primitives not in the environment are pure,
           -- by using something like this:
           --
           -- pureFunMonTerm (typedSubsTermArity $ primType nm) trm
  monadify UnitValue = retPure unitOpenTerm
  monadify UnitType = retPure unitTypeOpenTerm
  monadify (PairValue t1 t2) =
    pureMonTerm <$> (pairOpenTerm <$> monadifyPure t1 <*> monadifyPure t2)
  monadify (PairType t1 t2) =
    pureMonTerm <$> (pairTypeOpenTerm <$> monadifyPure t1 <*> monadifyPure t2)
  monadify (PairLeft t) = pureMonTerm <$> pairLeftOpenTerm <$> monadifyPure t
  monadify (PairRight t) = pureMonTerm <$> pairRightOpenTerm <$> monadifyPure t
  monadify (DataTypeApp pn params args) =
    mapM monadify (params ++ args) >>=
    monadifyApplyMulti (pureFunMonTerm
                        (typeArity $ toTerm $ primType pn)
                        (closedOpenTerm $ toTerm $ primType pn)
                        (dataTypeOpenTerm $ primName pn))
  monadify (CtorApp pn params args) =
    mapM monadify (params ++ args) >>=
    monadifyApplyMulti (pureFunMonTerm
                        (typeArity $ toTerm $ primType pn)
                        (closedOpenTerm $ toTerm $ primType pn)
                        (ctorOpenTerm $ primName pn))
  monadify (Sort s) = retPure (sortOpenTerm s)
  monadify (NatLit n) = retPure $ natOpenTerm n
  monadify (StringLit str) = retPure $ stringLitOpenTerm str
  monadify _ = error "FIXME HERE: missing cases for monadify"


----------------------------------------------------------------------
-- * Top-Level Entrypoints
----------------------------------------------------------------------

-- | Monadify a term, or 'fail' if this is not possible
monadifyTerm :: SharedContext -> MonadifyEnv -> Term -> IO Term
monadifyTerm sc env t =
  completeOpenTerm sc $ monTermComp $ monadifyTermAndRun env [] t

-- | Monadify a term, or 'fail' if this is not possible
monadifyTerm' :: SharedContext -> MonadifyEnv -> Term -> IO Term
monadifyTerm' sc env t =
  do tst <- typeAllSubterms sc t
     completeOpenTerm sc $ monTermComp $ monadifyTSTermAndRun env [] tst

-- | The definitions and primitives considered to be pure in 'defaultMonEnv',
-- along with their arities
defaultMonPureIds :: [(Ident,Int)]
defaultMonPureIds =
  [("Cryptol.PLiteral", 1),
   ("Cryptol.ecNumber", 3)
  ]

-- | The default monadification environment
defaultMonEnv :: MonadifyEnv
defaultMonEnv = Map.fromList $
  map (\(ident,arity) ->
        (ident, pureGlobalMonTerm arity ident))
  defaultMonPureIds
  ++
  []
-}
