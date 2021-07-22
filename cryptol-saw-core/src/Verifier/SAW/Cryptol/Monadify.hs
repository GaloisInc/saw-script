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

import Data.Maybe
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Cont
import qualified Control.Monad.Fail as Fail
-- import Control.Monad.IO.Class (MonadIO, liftIO)

import Verifier.SAW.Name
import Verifier.SAW.Term.Functor
import Verifier.SAW.SharedTerm
import Verifier.SAW.OpenTerm
-- import Verifier.SAW.SCTypeCheck
import Verifier.SAW.Recognizer
-- import Verifier.SAW.Position

-- import Debug.Trace


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

-- | Test if a 'Term' is a first-order function type
isFirstOrderType :: Term -> Bool
isFirstOrderType (asPi -> Just (_, asPi -> Just _, _)) = False
isFirstOrderType (asPi -> Just (_, _, tp_out)) = isFirstOrderType tp_out
isFirstOrderType _ = True

-- | A global definition, which is either a primitive or a constant
data GlobalDef = GlobalDef { globalDefName :: NameInfo,
                             globalDefType :: Term,
                             globalDefTerm :: Term }

-- | Build an 'OpenTerm' from a 'GlobalDef'
globalDefOpenTerm :: GlobalDef -> OpenTerm
globalDefOpenTerm = closedOpenTerm . globalDefTerm

-- | Recognize a named global definition, including its type
asTypedGlobalDef :: Recognizer Term GlobalDef
asTypedGlobalDef t =
  case unwrapTermF t of
    FTermF (Primitive pn) ->
      Just $ GlobalDef (ModuleIdentifier $ primName pn) (primType pn) t
    Constant ec t_def ->
      Just $ GlobalDef (ecName ec) (ecType ec) t_def
    _ -> Nothing


data MonKind = MKType Sort | MKNum | MKFun MonKind MonKind deriving Eq

-- | Convert a kind to a SAW core sort, if possible
monKindToSort :: MonKind -> Maybe Sort
monKindToSort (MKType s) = Just s
monKindToSort _ = Nothing

-- | Convert a 'MonKind' to the term it represents
monKindOpenTerm :: MonKind -> OpenTerm
monKindOpenTerm (MKType s) = sortOpenTerm s
monKindOpenTerm MKNum = dataTypeOpenTerm "Cryptol.Num" []
monKindOpenTerm (MKFun k1 k2) =
  arrowOpenTerm "_" (monKindOpenTerm k1) (monKindOpenTerm k2)

data MonType
  = MTyForall LocalName MonKind (MonType -> MonType)
  | MTyArrow MonType MonType
  | MTyPair MonType MonType
  | MTyRecord [(FieldName, MonType)]
  | MTyBase MonKind OpenTerm -- A "base type" or type var of a given kind
  | MTyNum OpenTerm

-- | Make a base type of sort 0 from an 'OpenTerm'
mkMonType0 :: OpenTerm -> MonType
mkMonType0 = MTyBase (MKType $ mkSort 0)

-- | Test that a monadification type is monomorphic, i.e., has no foralls
monTypeIsMono :: MonType -> Bool
monTypeIsMono (MTyForall _ _ _) = False
monTypeIsMono (MTyArrow tp1 tp2) = monTypeIsMono tp1 && monTypeIsMono tp2
monTypeIsMono (MTyPair tp1 tp2) = monTypeIsMono tp1 && monTypeIsMono tp2
monTypeIsMono (MTyRecord tps) = all (monTypeIsMono . snd) tps
monTypeIsMono (MTyBase _ _) = True
monTypeIsMono (MTyNum _) = True

-- | Test if a monadification type @tp@ is considered a base type, meaning that
-- @CompMT(tp) = CompM tp@
isBaseType :: MonType -> Bool
isBaseType (MTyForall _ _ _) = False
isBaseType (MTyArrow _ _) = False
isBaseType (MTyPair _ _) = True
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
monTypeKind (MTyPair tp1 tp2) =
  do sort1 <- monTypeKind tp1 >>= monKindToSort
     sort2 <- monTypeKind tp2 >>= monKindToSort
     return $ MKType $ maxSort [sort1, sort2]
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

-- | Convert a 'MonType' to the pure type @tp@ it was translated from
toPureType :: MonType -> OpenTerm
toPureType (MTyForall x k body) =
  piOpenTerm x (monKindOpenTerm k) (\tp -> toPureType (body $ MTyBase k tp))
toPureType (MTyArrow t1 t2) =
  arrowOpenTerm "_" (toPureType t1) (toPureType t2)
toPureType (MTyPair mtp1 mtp2) =
  pairTypeOpenTerm (toPureType mtp1) (toPureType mtp2)
toPureType (MTyRecord tps) =
  recordTypeOpenTerm $ map (\(f,tp) -> (f, toPureType tp)) tps
toPureType (MTyBase _ t) = t
toPureType (MTyNum n) = n

-- | Convert a 'MonType' to the argument type @MT(tp)@ it represents
toArgType :: MonType -> OpenTerm
toArgType (MTyForall x k body) =
  piOpenTerm x (monKindOpenTerm k) (\tp -> monTypeCompType (body $ MTyBase k tp))
toArgType (MTyArrow t1 t2) =
  arrowOpenTerm "_" (toArgType t1) (monTypeCompType t2)
toArgType (MTyPair mtp1 mtp2) =
  pairTypeOpenTerm (toArgType mtp1) (toArgType mtp2)
toArgType (MTyRecord tps) =
  recordTypeOpenTerm $ map (\(f,tp) -> (f, toArgType tp)) tps
toArgType (MTyBase _ t) = t
toArgType (MTyNum n) = n

-- | Convert a 'MonType' to the computation type @CompMT(tp)@ it represents
monTypeCompType :: MonType -> OpenTerm
monTypeCompType mtp@(MTyForall _ _ _) = toArgType mtp
monTypeCompType mtp@(MTyArrow _ _) = toArgType mtp
monTypeCompType mtp =
  applyOpenTerm (globalOpenTerm "Prelude.CompM") (toArgType mtp)

-- | A context of local variables used for monadifying types, which includes the
-- variable names, their original types (before monadification), and, if their
-- types corespond to 'MonKind's, a local 'MonType' that quantifies over them.
--
-- NOTE: the reason this type is different from 'MonadifyCtx', the context type
-- for monadifying terms, is that monadifying arrow types does not introduce a
-- local 'MonTerm' argument, since they are not dependent functions and so do
-- not use a HOAS encoding.
type MonadifyTypeCtx = [(LocalName,Term,Maybe MonType)]

-- | Pretty-print a 'Term' relative to a 'MonadifyTypeCtx'
ppTermInTypeCtx :: MonadifyTypeCtx -> Term -> String
ppTermInTypeCtx ctx t =
  scPrettyTermInCtx defaultPPOpts (map (\(x,_,_) -> x) ctx) t

-- | Extract the variables and their original types from a 'MonadifyTypeCtx'
typeCtxPureCtx :: MonadifyTypeCtx -> [(LocalName,Term)]
typeCtxPureCtx = map (\(x,tp,_) -> (x,tp))

-- | Make a monadification type that is to be considered a base type
mkTermBaseType :: MonadifyTypeCtx -> MonKind -> Term -> MonType
mkTermBaseType ctx k t =
  MTyBase k $ openOpenTerm (typeCtxPureCtx ctx) t

-- | Monadify a type and convert it to its corresponding argument type
monadifyTypeArgType :: MonadifyTypeCtx -> Term -> OpenTerm
monadifyTypeArgType ctx t = toArgType $ monadifyType ctx t

-- | Convert a SAW core 'Term' to a monadification type
monadifyType :: MonadifyTypeCtx -> Term -> MonType
{-
monadifyType ctx t
  | trace ("\nmonadifyType:\n" ++ ppTermInTypeCtx ctx t) False = undefined
-}
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
monadifyType ctx (asPairType -> Just (tp1, tp2)) =
  MTyPair (monadifyType ctx tp1) (monadifyType ctx tp2)
monadifyType ctx (asRecordType -> Just tps) =
  MTyRecord $ map (\(fld,tp) -> (fld, monadifyType ctx tp)) $ Map.toList tps
monadifyType ctx (asDataType -> Just (eq_pn, [k_trm, tp1, tp2]))
  | primName eq_pn == "Prelude.Eq"
  , isJust (monadifyKind k_trm) =
    -- NOTE: technically this is a Prop and not a sort 0, but it doesn't matter
    mkMonType0 $ dataTypeOpenTerm "Prelude.Eq" [monadifyTypeArgType ctx tp1,
                                                monadifyTypeArgType ctx tp2]
monadifyType ctx (asDataType -> Just (pn, args))
  | Just pn_k <- monadifyKind (primType pn)
  , margs <- map (monadifyType ctx) args
  , Just k_out <- applyKinds pn_k margs =
    -- NOTE: this case only recognizes data types whose arguments are all types
    -- and/or Nums
    MTyBase k_out $ dataTypeOpenTerm (primName pn) (map toArgType margs)
monadifyType ctx (asVectorType -> Just (len, tp)) =
  mkMonType0 (applyOpenTermMulti (globalOpenTerm "Prelude.Vec")
              [openOpenTerm (typeCtxPureCtx ctx) len,
               monadifyTypeArgType ctx tp])
monadifyType ctx (asApplyAll -> (f, args))
  | Just glob <- asTypedGlobalDef f
  , Just ec_k <- monadifyKind $ globalDefType glob
  , margs <- map (monadifyType ctx) args
  , Just k_out <- applyKinds ec_k margs =
    MTyBase k_out (applyOpenTermMulti (globalDefOpenTerm glob) $
                   map toArgType margs)
monadifyType ctx tp@(asCtor -> Just (pn, _))
  | primName pn == "Cryptol.TCNum" || primName pn == "Cryptol.TCInf" =
    MTyNum $ openOpenTerm (typeCtxPureCtx ctx) tp
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
  = PureMonTerm MonType OpenTerm
  | FunMonTerm LocalName MonType MonType (ArgMonTerm -> MonTerm)
  | ForallMonTerm LocalName MonKind (MonType -> MonTerm)

data MonTerm
  = ArgMonTerm ArgMonTerm
  | CompMonTerm MonType OpenTerm

-- | Get the monadification type of a monadification term, irrespective of if it
-- is pure or an argument or computational
class GetMonType a where
  getMonType :: a -> MonType

instance GetMonType ArgMonTerm where
  getMonType (PureMonTerm tp _) = tp
  getMonType (ForallMonTerm x k body) = MTyForall x k (getMonType . body)
  getMonType (FunMonTerm _ tp_in tp_out _) = MTyArrow tp_in tp_out

instance GetMonType MonTerm where
  getMonType (ArgMonTerm t) = getMonType t
  getMonType (CompMonTerm tp _) = tp


class ToCompTerm a where
  -- | Convert a monadification term to a SAW core term of type @CompMT(tp)@
  toCompTerm :: a -> OpenTerm

instance ToCompTerm ArgMonTerm where
  toCompTerm (PureMonTerm (MTyForall x k tp_body) t) =
    lambdaOpenTerm x (monKindOpenTerm k) $ \tp ->
    toCompTerm $ PureMonTerm (tp_body $ MTyBase k tp) (applyOpenTerm t tp)
  toCompTerm (PureMonTerm (MTyArrow tp_in tp_out) t)
    | isBaseType tp_in =
      -- In this case, tp_in = MT(tp_in), so we can apply t to x
      lambdaOpenTerm "_" (toArgType tp_in) $ \x ->
      toCompTerm $ PureMonTerm tp_out (applyOpenTerm t x)
  toCompTerm (PureMonTerm (MTyArrow _ _) _) =
    -- In this case we have a pure higher-order function of some type of the
    -- form (a -> b) -> c, and we need to convert to (a -> CompMT(b)) ->
    -- CompMT(c).  This is impossible because that would require converting a
    -- monadic function to a pure function, so we throw an error.
    failOpenTerm "Monadification failed: cannot monadify a pure higher-order function"
  toCompTerm (PureMonTerm mtp t)
    | isBaseType mtp =
      applyOpenTermMulti (globalOpenTerm "Prelude.returnM")
      [toPureType mtp, t]
  toCompTerm (PureMonTerm _mtp _t) = error "FIXME HERE: toCompTerm for pure terms"
  toCompTerm (FunMonTerm x tp_in _ body) =
    lambdaOpenTerm x (toArgType tp_in) (toCompTerm . body . fromArgTerm tp_in)
  toCompTerm (ForallMonTerm x k body) =
    lambdaOpenTerm x (monKindOpenTerm k) (toCompTerm . body . MTyBase k)

instance ToCompTerm MonTerm where
  toCompTerm (ArgMonTerm amtrm) = toCompTerm amtrm
  toCompTerm (CompMonTerm _ trm) = trm


class ToPureTerm a where
  -- | Convert a monadification term to a "pure" SAW core term of type @tp@, if
  -- possible
  toPureTerm :: a -> OpenTerm

instance ToPureTerm ArgMonTerm where
  toPureTerm (PureMonTerm _ t) = t
  toPureTerm (FunMonTerm x tp_in _ f) =
    lambdaOpenTerm x (toPureType tp_in) $ \x_trm ->
    toPureTerm $ f $ PureMonTerm tp_in x_trm
  toPureTerm (ForallMonTerm x k body) =
    lambdaOpenTerm x (monKindOpenTerm k) $ \tp ->
    toPureTerm $ body $ MTyBase k tp

instance ToPureTerm MonTerm where
  toPureTerm (ArgMonTerm mtrm) = toPureTerm mtrm
  toPureTerm (CompMonTerm _ _) =
    failOpenTerm
    "Monadification failed: could not convert computational term to pure term"

-- | Convert an 'ArgMonTerm' to a SAW core term of type @MT(tp)@
toArgTerm :: ArgMonTerm -> OpenTerm
toArgTerm (PureMonTerm mtp t) | isBaseType mtp = t
toArgTerm t = toCompTerm t


-- | Build a monadification term from a term of type @MT(tp)@
class FromArgTerm a where
  fromArgTerm :: MonType -> OpenTerm -> a

instance FromArgTerm ArgMonTerm where
  fromArgTerm (MTyForall x k body) t =
    ForallMonTerm x k (\tp -> fromCompTerm (body tp) (applyOpenTerm t $
                                                      toArgType tp))
  fromArgTerm (MTyArrow t1 t2) t =
    FunMonTerm "_" t1 t2 (\x -> fromCompTerm t2 (applyOpenTerm t $ toArgTerm x))
  fromArgTerm tp t | isBaseType tp = PureMonTerm tp t
  fromArgTerm _ _ = error "fromArgTerm: malformed type for term"

instance FromArgTerm MonTerm where
  fromArgTerm mtp t = ArgMonTerm $ fromArgTerm mtp t

-- | Build a monadification term from a computational term of type @CompMT(tp)@
fromCompTerm :: MonType -> OpenTerm -> MonTerm
fromCompTerm mtp t | isBaseType mtp = CompMonTerm mtp t
fromCompTerm mtp t = ArgMonTerm $ fromArgTerm mtp t

-- | Build a 'MonTerm' that 'fail's when converted to a term
failMonTerm :: MonType -> String -> MonTerm
failMonTerm mtp str = fromArgTerm mtp (failOpenTerm str)

-- | Build an 'ArgMonTerm' that 'fail's when converted to a term
failArgMonTerm :: MonType -> String -> ArgMonTerm
failArgMonTerm tp str = fromArgTerm tp (failOpenTerm str)

-- | Apply a monadified term to a type or term argument
applyMonTerm :: MonTerm -> Either MonType ArgMonTerm -> MonTerm
applyMonTerm (ArgMonTerm (FunMonTerm _ _ _ f)) (Right arg) = f arg
applyMonTerm (ArgMonTerm (PureMonTerm (MTyArrow _ tp_out) t)) (Right arg) =
  ArgMonTerm $ PureMonTerm tp_out $ applyOpenTerm t $ toPureTerm arg
applyMonTerm (ArgMonTerm (ForallMonTerm _ _ f)) (Left mtp) = f mtp
applyMonTerm (ArgMonTerm (PureMonTerm (MTyForall _ _ body) t)) (Left mtp) =
  ArgMonTerm $ PureMonTerm (body mtp) $ applyOpenTerm t $ toArgType mtp
applyMonTerm _ _ = error "applyMonTerm: application at incorrect type"

-- | Apply a monadified term to 0 or more arguments
applyMonTermMulti :: MonTerm -> [Either MonType ArgMonTerm] -> MonTerm
applyMonTermMulti = foldl applyMonTerm

-- | Build a 'MonTerm' from a global of a given argument type
mkGlobalArgMonTerm :: MonType -> Ident -> ArgMonTerm
mkGlobalArgMonTerm tp ident = fromArgTerm tp (globalOpenTerm ident)

-- | Build a 'MonTerm' from a 'GlobalDef' of pure type
mkPureGlobalDefArgMonTerm :: GlobalDef -> ArgMonTerm
mkPureGlobalDefArgMonTerm glob =
  PureMonTerm (monadifyType [] $ globalDefType glob) (globalDefOpenTerm glob)

-- | Build a 'MonTerm' from a constructor with the given 'PrimName'
mkCtorArgMonTerm :: PrimName Term -> ArgMonTerm
mkCtorArgMonTerm pn
  | not (isFirstOrderType (primType pn)) =
    failArgMonTerm (monadifyType [] $ primType pn)
    ("monadification failed: cannot handle constructor "
     ++ show (primName pn) ++ " with higher-order type")
mkCtorArgMonTerm pn =
  ctorHelper (monadifyType [] $ primType pn) (ctorOpenTerm $ primName pn)
  where
    ctorHelper :: MonType -> ([OpenTerm] -> OpenTerm) -> ArgMonTerm
    ctorHelper (MTyForall x k body) f =
      ForallMonTerm x k $ \tp ->
      ArgMonTerm $ ctorHelper (body tp) (f . (toArgType tp:))
    ctorHelper (MTyArrow t1 t2) f =
      FunMonTerm "_" t1 t2 $ \x ->
      ArgMonTerm $ ctorHelper t2 (f . (toArgTerm x:))
    ctorHelper tp f | isBaseType tp = PureMonTerm tp (f [])
    ctorHelper _ _ = error "mkCtorArgMonTerm: malformed type for constructor"


----------------------------------------------------------------------
-- * The Monadification Monad
----------------------------------------------------------------------

-- | A monadification macro is a function that inspects its first @N@ arguments
-- before being able to be converted to an 'ArgMonTerm'
data MonMacro = MonMacro { macroNumArgs :: Int,
                           macroApply :: [Term] -> ArgMonTerm }

-- | Make a simple 'MonMacro' that inspects 0 arguments and just returns a term
monMacro0 :: ArgMonTerm -> MonMacro
monMacro0 mtrm = MonMacro 0 (const mtrm)

-- | An environment of named definitions that have already been monadified
type MonadifyEnv = Map NameInfo MonMacro

-- | A context for monadifying 'Term's which maintains, for each deBruijn index
-- in scope, both its original un-monadified type along with either a 'MonTerm'
-- or 'MonType' for the translation of the variable to a local variable of
-- monadified type or monadified kind
type MonadifyCtx = [(LocalName,Term,Either MonType MonTerm)]

-- | Convert a 'MonadifyCtx' to a 'MonadifyTypeCtx'
ctxToTypeCtx :: MonadifyCtx -> MonadifyTypeCtx
ctxToTypeCtx = map (\(x,tp,arg) ->
                     (x,tp,case arg of
                         Left mtp -> Just mtp
                         Right _ -> Nothing))

-- | Pretty-print a 'Term' relative to a 'MonadifyCtx'
ppTermInMonCtx :: MonadifyCtx -> Term -> String
ppTermInMonCtx ctx t =
  scPrettyTermInCtx defaultPPOpts (map (\(x,_,_) -> x) ctx) t


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
type MonadifyState = IntMap MonTerm

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
  runCont (evalStateT (runReaderT (unMonadifyM m) ro_st) IntMap.empty) id

-- | Run a monadification computation using a mapping for identifiers that have
-- already been monadified and generate a SAW core term
runCompleteMonadifyM :: MonadIO m => SharedContext -> MonadifyEnv -> Term ->
                        MonadifyM MonTerm -> m Term
runCompleteMonadifyM sc env top_ret_tp m =
  liftIO $ completeOpenTerm sc $ toCompTerm $
  runMonadifyM env [] (toArgType $ monadifyType [] top_ret_tp) m

-- | Memoize a computation of the monadified term associated with a 'TermIndex'
memoizingM :: TermIndex -> MonadifyM MonTerm -> MonadifyM MonTerm
memoizingM i m =
  (IntMap.lookup i <$> get) >>= \case
  Just ret  -> return ret
  Nothing ->
    do ret <- m
       modify (IntMap.insert i ret)
       return ret

-- | Turn a 'MonTerm' of type @CompMT(tp)@ to a term of argument type @MT(tp)@
-- by inserting a monadic bind if the 'MonTerm' is computational
argifyMonTerm :: MonTerm -> MonadifyM ArgMonTerm
argifyMonTerm (ArgMonTerm mtrm) = return mtrm
argifyMonTerm (CompMonTerm mtp trm) =
  do let tp = toArgType mtp
     top_ret_tp <- topRetType
     shiftMonadifyM $ \k ->
       CompMonTerm (mkMonType0 top_ret_tp) $
       applyOpenTermMulti (globalOpenTerm "Prelude.bindM")
       [tp, top_ret_tp, trm,
        lambdaOpenTerm "x" tp (toCompTerm . k . fromArgTerm mtp)]


----------------------------------------------------------------------
-- * Monadification
----------------------------------------------------------------------

-- | Monadify a term to a monadified term of argument type
monadifyArg :: Maybe MonType -> Term -> MonadifyM ArgMonTerm
monadifyArg mtp t = monadifyTerm mtp t >>= argifyMonTerm

-- | Monadify a term to argument type and convert back to a term
monadifyArgTerm :: Maybe MonType -> Term -> MonadifyM OpenTerm
monadifyArgTerm mtp t = toArgTerm <$> monadifyArg mtp t

-- | Monadify a term
monadifyTerm :: Maybe MonType -> Term -> MonadifyM MonTerm
monadifyTerm mtp t@(STApp { stAppIndex = ix }) =
  memoizingM ix $ monadifyTerm' mtp t
monadifyTerm mtp t = monadifyTerm' mtp t

-- | The main implementation of 'monadifyTerm', which monadifies a term given an
-- optional monadification type. The type must be given for introduction forms
-- (i.e.,, lambdas, pairs, and records), but is optional for elimination forms
-- (i.e., applications, projections, and also in this case variables). Note that
-- this means monadification will fail on terms with beta or tuple redexes.
monadifyTerm' :: Maybe MonType -> Term -> MonadifyM MonTerm
monadifyTerm' (Just mtp@(MTyForall _ _ _)) t =
  ask >>= \ro_st ->
  return $ monadifyLambdas (monStEnv ro_st) (monStCtx ro_st) mtp t
monadifyTerm' (Just mtp@(MTyArrow _ _)) t =
  ask >>= \ro_st ->
  return $ monadifyLambdas (monStEnv ro_st) (monStCtx ro_st) mtp t
monadifyTerm' (Just mtp@(MTyPair mtp1 mtp2)) (asPairValue ->
                                              Just (trm1, trm2)) =
  fromArgTerm mtp <$> (pairOpenTerm <$>
                       monadifyArgTerm (Just mtp1) trm1 <*>
                       monadifyArgTerm (Just mtp2) trm2)
monadifyTerm' (Just mtp@(MTyRecord fs_mtps)) (asRecordValue -> Just trm_map)
  | length fs_mtps == Map.size trm_map
  , (fs,mtps) <- unzip fs_mtps
  , Just trms <- mapM (\f -> Map.lookup f trm_map) fs =
    fromArgTerm mtp <$> recordOpenTerm <$> zip fs <$>
    zipWithM monadifyArgTerm (map Just mtps) trms
monadifyTerm' _ (asPairSelector -> Just (trm, False)) =
  do mtrm <- monadifyArg Nothing trm
     mtp <- case getMonType mtrm of
       MTyPair t _ -> return t
       _ -> fail "Monadification failed: projection on term of non-pair type"
     return $ fromArgTerm mtp $
       pairLeftOpenTerm $ toArgTerm mtrm
monadifyTerm' _ (asPairSelector -> Just (trm, True)) =
  do mtrm <- monadifyArg Nothing trm
     mtp <- case getMonType mtrm of
       MTyPair _ t -> return t
       _ -> fail "Monadification failed: projection on term of non-pair type"
     return $ fromArgTerm mtp $
       pairRightOpenTerm $ toArgTerm mtrm
monadifyTerm' _ (asRecordSelector -> Just (trm, fld)) =
  do mtrm <- monadifyArg Nothing trm
     mtp <- case getMonType mtrm of
       MTyRecord mtps | Just mtp <- lookup fld mtps -> return mtp
       _ -> fail ("Monadification failed: " ++
                  "record projection on term of incorrect type")
     return $ fromArgTerm mtp $ projRecordOpenTerm (toArgTerm mtrm) fld
monadifyTerm' _ (asLocalVar -> Just ix) =
  (monStCtx <$> ask) >>= \case
  ctx | ix >= length ctx -> fail "Monadification failed: vaiable out of scope!"
  ctx | (_,_,Right mtrm) <- ctx !! ix -> return mtrm
  _ -> fail "Monadification failed: type variable used in term position!"
monadifyTerm' _ (asCtor -> Just (pn, args)) =
  monadifyApply (ArgMonTerm $ mkCtorArgMonTerm pn) args
monadifyTerm' _ (asApplyAll -> (asTypedGlobalDef -> Just glob, args)) =
  do env <- monStEnv <$> ask
     let macro =
           case Map.lookup (globalDefName glob) env of
             Just m -> m
             Nothing -> monMacro0 $ mkPureGlobalDefArgMonTerm glob
         (macro_args, reg_args) = splitAt (macroNumArgs macro) args
         mtrm_f = macroApply macro macro_args
     monadifyApply (ArgMonTerm mtrm_f) reg_args
monadifyTerm' _ t =
  (monStCtx <$> ask) >>= \ctx ->
  fail ("Monadifiction failed: no case for term: " ++ ppTermInMonCtx ctx t)


-- | Monadify the application of a monadified term to a list of terms, using the
-- type of the already monadified to monadify the arguments
monadifyApply :: MonTerm -> [Term] -> MonadifyM MonTerm
monadifyApply f (t : ts)
  | MTyArrow tp_in _ <- getMonType f =
    do mtrm <- monadifyArg (Just tp_in) t
       monadifyApply (applyMonTerm f (Right mtrm)) ts
monadifyApply f (t : ts)
  | MTyForall _ _ _ <- getMonType f =
    do ctx <- monStCtx <$> ask
       let mtp = monadifyType (ctxToTypeCtx ctx) t
       monadifyApply (applyMonTerm f (Left mtp)) ts
monadifyApply _ (_:_) = fail "monadifyApply: application at incorrect type"
monadifyApply f [] = return f


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

-- | FIXME: documentation
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
  (runMonadifyM env ctx (toArgType mtp) (monadifyTerm (Just top_mtp) t))
  args


----------------------------------------------------------------------
-- * Handling the Primitives
----------------------------------------------------------------------

unsafeAssertMacro :: MonMacro
unsafeAssertMacro = MonMacro 1 $ \ts ->
  let numFunType =
        MTyForall "n" (MKType $ mkSort 0) $ \n ->
        MTyForall "m" (MKType $ mkSort 0) $ \m ->
        MTyBase (MKType $ mkSort 0) $
        dataTypeOpenTerm "Prelude.Eq"
        [dataTypeOpenTerm "Prelude.Num" [],
         toArgType n, toArgType m] in
  case ts of
    [(asDataType -> Just (num, []))]
      | primName num == "Cryptol.Num" ->
        mkGlobalArgMonTerm numFunType "Cryptol.numAssertEqM"
    _ ->
      failArgMonTerm numFunType
      "Monadification failed: unsafeAssert applied to non-Num type"

-- | The default monadification environment
defaultMonEnv :: MonadifyEnv
defaultMonEnv =
  Map.fromList $ map (\(ident,macro) -> (ModuleIdentifier ident, macro)) $
  [
    ("Prelude.unsafeAssert", unsafeAssertMacro)
  ]


----------------------------------------------------------------------
-- * Top-Level Entrypoints
----------------------------------------------------------------------

-- | Monadify a term of the specified type, or 'fail' if this is not possible
monadify :: SharedContext -> MonadifyEnv -> Term -> Term -> IO Term
monadify sc env trm tp =
  runCompleteMonadifyM sc env tp (monadifyTerm (Just $ monadifyType [] tp) trm)
