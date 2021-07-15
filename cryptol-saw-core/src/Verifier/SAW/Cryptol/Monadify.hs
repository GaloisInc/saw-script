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

The monadification @Mon(t)@ of term @t@ is defined as follows (where we have
simplified the input langauge to just contain pairs, sums, units, and
functions):

FIXME: either talk about CPS or drop the definition

> Mon(sort s) = sort s
> Mon(#()) = #()
> Mon(T * U) = Mon(T) * Mon(U)
> Mon(Either T U) = Either Mon(T) Mon(U)
> Mon(Pi x a b) = Pi x Mon(T) (CompM Mon(U))
> Mon()
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
-- * Monadified Terms and Types
----------------------------------------------------------------------

-- | When we monadify a term @trm@ of type @tp@, we in general get a term
-- @Mon(trm) : CompM Mon(tp)@. But sometimes we can do better, and get a term of
-- a "more pure" type that can be embedded into @CompM Mon(tp)@. A
-- monadification term represents one of these possibly more pure terms.
data MonTerm
     -- | A "pure" term of type @Mon(tp)@
  = PureMonTerm OpenTerm OpenTerm
    -- | A "computational" term of type @CompM Mon(tp)@, where the supplied
    -- 'OpenTerm' gives the pure type @Mon(tp)@
  | CompMonTerm OpenTerm OpenTerm
    -- | A (dependent) function of type @Pi x t u@ for monadification type
    -- @u@. Note that this is "more pure" than 'PureMonTerm', because that
    -- constructor uses a type of the form @Pi x t (CompM u)@ for functions,
    -- whereas this constructor allows the return type to be pure as well.
  | FunMonTerm LocalName OpenTerm (OpenTerm -> MonTerm)

-- FIXME: maybe make the body of a FunMonTerm be a MonTerm -> MonTerm?

-- | Build a pure 'MonTerm' from a pure 'OpenTerm'
pureMonTerm :: OpenTerm -> MonTerm
pureMonTerm trm = PureMonTerm trm $ openTermType trm

-- | Build a pure 'MonTerm' from a pure function of the given arity which has
-- the given type. NOTE: this only works for first-order functions, i.e.,
-- functions whose argument types do not themselves contain function types.
pureFunMonTerm :: Int -> OpenTerm -> ([OpenTerm] -> OpenTerm) -> MonTerm
pureFunMonTerm 0 _ f = pureMonTerm (f [])
pureFunMonTerm i tp f =
  FunMonTerm "x" (piArgOpenTerm tp) $ \x ->
  pureFunMonTerm (i-1) (applyPiOpenTerm tp x) $ \xs -> f (x : xs)

-- | Build a pure 'MonTerm' from a global definition or primitive of the given
-- arity. NOTE: this only works for first-order functions, i.e., functions whose
-- argument types do not themselves contain function types.
pureGlobalMonTerm :: Int -> Ident -> MonTerm
pureGlobalMonTerm i ident =
  pureFunMonTerm i
  (openTermType (globalOpenTerm ident))
  (applyOpenTermMulti (globalOpenTerm ident))

-- | Build a 'MonTerm' for a 'failOpenTerm'
failMonTerm :: String -> MonTerm
failMonTerm str = pureMonTerm $ failOpenTerm str

-- | Convert the type of a 'MonType' to its most general pure type @Mon(tp)@
monTermPureType :: MonTerm -> OpenTerm
monTermPureType (PureMonTerm _ tp) = tp
monTermPureType (CompMonTerm _ tp) = tp
monTermPureType (FunMonTerm x tp body_f) =
  piOpenTerm x tp (monTermCompType . body_f)

-- | Convert the type of a 'MonTerm' to its most general computational type
-- @CompM Mon(tp)@
monTermCompType :: MonTerm -> OpenTerm
monTermCompType =
  applyOpenTerm (globalOpenTerm "Prelude.CompM") . monTermPureType

-- | Test if a 'MonTerm' is a computational term, i.e., of @CompM@ type
isCompTerm :: MonTerm -> Bool
isCompTerm (CompMonTerm _ _) = True
isCompTerm _ = False

-- | Convert a 'FunMonType' function of type @Pi x t u@ to its most general pure
-- type @Pi x t ('monTermPureType' u)@
funTermPure :: LocalName -> OpenTerm -> (OpenTerm -> MonTerm) -> OpenTerm
funTermPure x tp body_f = lambdaOpenTerm x tp (monTermComp . body_f)

-- | Embed a 'MonTerm' into type @CompM Mon(tp)@
monTermComp :: MonTerm -> OpenTerm
monTermComp (PureMonTerm trm tp) =
  applyOpenTermMulti (globalOpenTerm "Prelude.returnM") [tp, trm]
monTermComp (CompMonTerm trm _) = trm
monTermComp mtrm@(FunMonTerm x tp body_f) =
  applyOpenTermMulti (globalOpenTerm "Prelude.returnM")
  [monTermPureType mtrm, funTermPure x tp body_f]

-- | Try to convert a 'MonTerm' into a pure term by converting any 'CompFunType'
-- function to its most general @Pi x t (CompM u)@ form. For computational
-- 'MonTerm's, return 'Nothing'
monTermTryPure :: MonTerm -> Maybe OpenTerm
monTermTryPure (PureMonTerm trm _) = Just trm
monTermTryPure (FunMonTerm x tp body) =
  return $ funTermPure x tp body
monTermTryPure (CompMonTerm _ _) = Nothing

-- | Convert a 'MonTerm' to a pure term using 'monTermTryPure' or return an
-- 'OpenTerm' that 'fail's when completed
monTermForcePure :: String -> MonTerm -> OpenTerm
monTermForcePure _ mtrm | Just trm <- monTermTryPure mtrm = trm
monTermForcePure str _ = failOpenTerm str


----------------------------------------------------------------------
-- * The Monadification Monad
----------------------------------------------------------------------

-- | An environment of named definitions that have already been monadified
type MonadifyEnv = Map Ident MonTerm

-- | A context for monadifying 'Term's which maintains, for each deBruijn index
-- in scope, both its original un-monadified type along with an 'OpenTerm' for
-- the translation of the variable to a local variable of monadified type
type MonadifyCtx = [(Term,OpenTerm)]

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
    MonadifyM $ lift $ lift $ cont $ \_ -> failMonTerm str

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
runCompleteMonadifyM :: MonadIO m => SharedContext -> MonadifyEnv -> OpenTerm ->
                        MonadifyM MonTerm -> m Term
runCompleteMonadifyM sc env top_ret_tp m =
  liftIO $ completeOpenTerm sc $ monTermComp $ runMonadifyM env [] top_ret_tp m

-- | Memoize a computation of the monadified term associated with a 'TermIndex'
memoizingM :: TermIndex -> MonadifyM MonTerm -> MonadifyM MonTerm
memoizingM i m =
  (Map.lookup i <$> get) >>= \case
  Just ret  -> return ret
  Nothing ->
    do ret <- m
       modify (Map.insert i ret)
       return ret

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

-- | Turn a 'MonTerm' into a pure term by inserting a monadic bind if the
-- 'MonTerm' is computational and converting any 'CompFunType' function to its
-- most general @Pi x t (CompM u)@ form
purifyMonTerm :: MonTerm -> MonadifyM OpenTerm
purifyMonTerm (PureMonTerm trm _) = return trm
purifyMonTerm (FunMonTerm x tp body) =
  return $ funTermPure x tp body
purifyMonTerm (CompMonTerm trm tp) =
  topRetType >>= \top_ret_tp ->
  shiftMonadifyM $ \k ->
  pureMonTerm $ applyOpenTermMulti (globalOpenTerm "Prelude.bindM")
  [tp, top_ret_tp, trm, lambdaOpenTerm "x" tp (monTermComp . k)]

-- | Return a pure 'MonTerm' as the result of monadification
retPure :: OpenTerm -> MonadifyM MonTerm
retPure = return . pureMonTerm


----------------------------------------------------------------------
-- * Monadification
----------------------------------------------------------------------

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
