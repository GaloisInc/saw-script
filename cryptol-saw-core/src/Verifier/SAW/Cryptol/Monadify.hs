{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveGeneric #-}

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
consistent. The monad that is used is the @SpecM@ monad that is axiomatized in
the SAW core prelude. This is only a partial transformation, meaning that it
will fail on some SAW core terms. Specifically, it requires that all
applications @f arg@ in a term either have a non-dependent function type for @f@
(i.e., a function with type @'Pi' x a b@ where @x@ does not occur in @b@) or a
pure argument @arg@ that does not use any of the inconsistent operations.

FIXME: explain this better


Type-level translation:

MT(Pi x (sort 0) b) = Pi x (sort 0) CompMT(b)
MT(Pi x Num b) = Pi x Num CompMT(b)
MT(Pi _ a b) = MT(a) -> CompMT(b)
MT(#(a,b)) = #(MT(a),MT(b))
MT(seq n a) = mseq n MT(a)
MT(f arg) = f MT(arg)  -- NOTE: f must be a pure function!
MT(cnst) = cnst
MT(dt args) = dt MT(args)
MT(x) = x
MT(_) = error

CompMT(tp = Pi _ _ _) = MT(tp)
CompMT(n : Num) = n
CompMT(tp) = SpecM MT(tp)


Term-level translation:

MonArg(t : tp) ==> MT(tp)
MonArg(t) =
  case Mon(t) of
    m : SpecM MT(a) => shift \k -> m >>= \x -> k x
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
import qualified Data.Text as T
import qualified Text.URI as URI
import GHC.Generics (Generic)

import Verifier.SAW.Name
import Verifier.SAW.Term.Functor
import Verifier.SAW.SharedTerm
import Verifier.SAW.OpenTerm
import Verifier.SAW.TypedTerm
import Verifier.SAW.Cryptol (Env)
import Verifier.SAW.SCTypeCheck
import Verifier.SAW.Recognizer
-- import Verifier.SAW.Position
import Verifier.SAW.Cryptol.PreludeM

import GHC.Stack
import Debug.Trace


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
                  tpSubsTypeF = FTermF (Sort (tpSubsSort tst) noFlags),
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

-- | A global definition, which is either a primitive or a constant. As
-- described in the documentation for 'ExtCns', the names need not be unique,
-- but the 'VarIndex' is, and this is what is used to index 'GlobalDef's.
data GlobalDef = GlobalDef { globalDefName :: NameInfo,
                             globalDefIndex :: VarIndex,
                             globalDefType :: Term,
                             globalDefTerm :: Term,
                             globalDefBody :: Maybe Term }

instance Eq GlobalDef where
  gd1 == gd2 = globalDefIndex gd1 == globalDefIndex gd2

instance Ord GlobalDef where
  compare gd1 gd2 = compare (globalDefIndex gd1) (globalDefIndex gd2)

instance Show GlobalDef where
  show = show . globalDefName

-- | Get the 'String' name of a 'GlobalDef'
globalDefString :: GlobalDef -> String
globalDefString = T.unpack . toAbsoluteName . globalDefName

-- | Build an 'OpenTerm' from a 'GlobalDef'
globalDefOpenTerm :: GlobalDef -> OpenTerm
globalDefOpenTerm = closedOpenTerm . globalDefTerm

-- | Recognize a named global definition, including its type
asTypedGlobalDef :: Recognizer Term GlobalDef
asTypedGlobalDef t =
  case unwrapTermF t of
    FTermF (Primitive pn) ->
      Just $ GlobalDef (ModuleIdentifier $
                        primName pn) (primVarIndex pn) (primType pn) t Nothing
    Constant ec body ->
      Just $ GlobalDef (ecName ec) (ecVarIndex ec) (ecType ec) t body
    FTermF (ExtCns ec) ->
      Just $ GlobalDef (ecName ec) (ecVarIndex ec) (ecType ec) t Nothing
    _ -> Nothing

-- | The event type and function stack arguments to the @SpecM@ type, using type
-- @tm@ for terms
data SpecMParams tm = SpecMParams { specMEvType :: tm, specMStack :: tm }
                      deriving (Generic, Show)

-- | Convert a 'SpecMParams' to a list of terms
paramsToTerms :: SpecMParams tm -> [tm]
paramsToTerms SpecMParams { specMEvType = ev, specMStack = stack } = [ev,stack]

-- | The implicit argument version of 'SpecMParams'
type HasSpecMParams = (?specMParams :: SpecMParams OpenTerm)

-- | Build a @LetRecType@ for a nested pi type
lrtFromMonType :: HasSpecMParams => MonType -> OpenTerm
lrtFromMonType (MTyForall x k body_f) =
  ctorOpenTerm "Prelude.LRT_Fun"
  [monKindOpenTerm k,
   lambdaOpenTerm x (monKindOpenTerm k) (\tp -> lrtFromMonType $
                                                body_f $ MTyBase k tp)]
lrtFromMonType (MTyArrow mtp1 mtp2) =
  ctorOpenTerm "Prelude.LRT_Fun"
  [toArgType mtp1,
   lambdaOpenTerm "_" (toArgType mtp1) (\_ -> lrtFromMonType mtp2)]
lrtFromMonType mtp =
  ctorOpenTerm "Prelude.LRT_Ret" [toArgType mtp]

-- | Push a frame of recursive functions with the given 'MonType's onto a
-- @FunStack@
--
-- FIXME HERE: This will give the incorrect type if any of the 'MonType's are
-- higher-order, meaning they themselves take in or return types containing
-- @SpecM@. In order to fix this, we will need a more general @LetRecType@.
pushSpecMFrame :: HasSpecMParams => [MonType] -> OpenTerm -> OpenTerm
pushSpecMFrame tps stack =
  let frame =
        list1OpenTerm (dataTypeOpenTerm "Prelude.LetRecType" []) $
        map lrtFromMonType tps in
  applyGlobalOpenTerm "Prelude.pushFunStack" [frame, stack]

-- | The empty function stack
emptyStackOpenTerm :: OpenTerm
emptyStackOpenTerm = globalOpenTerm "Prelude.emptyFunStack"

-- | Build a 'SpecMParams' with the empty stack from an 'EvType'
paramsOfEvType :: OpenTerm -> SpecMParams OpenTerm
paramsOfEvType ev = SpecMParams ev emptyStackOpenTerm

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
  | MTySeq OpenTerm MonType
  | MTyPair MonType MonType
  | MTyRecord [(FieldName, MonType)]
  | MTyBase MonKind OpenTerm -- A "base type" or type var of a given kind
  | MTyNum OpenTerm

-- | Make a base type of sort 0 from an 'OpenTerm'
mkMonType0 :: OpenTerm -> MonType
mkMonType0 = MTyBase (MKType $ mkSort 0)

-- | Make a 'MonType' for the Boolean type
boolMonType :: MonType
boolMonType = mkMonType0 $ globalOpenTerm "Prelude.Bool"

-- | Test that a monadification type is monomorphic, i.e., has no foralls
monTypeIsMono :: MonType -> Bool
monTypeIsMono (MTyForall _ _ _) = False
monTypeIsMono (MTyArrow tp1 tp2) = monTypeIsMono tp1 && monTypeIsMono tp2
monTypeIsMono (MTyPair tp1 tp2) = monTypeIsMono tp1 && monTypeIsMono tp2
monTypeIsMono (MTyRecord tps) = all (monTypeIsMono . snd) tps
monTypeIsMono (MTySeq _ tp) = monTypeIsMono tp
monTypeIsMono (MTyBase _ _) = True
monTypeIsMono (MTyNum _) = True

-- | Test if a monadification type @tp@ is considered a base type, meaning that
-- @CompMT(tp) = CompM MT(tp)@
isBaseType :: MonType -> Bool
isBaseType (MTyForall _ _ _) = False
isBaseType (MTyArrow _ _) = False
isBaseType (MTySeq _ _) = True
isBaseType (MTyPair _ _) = True
isBaseType (MTyRecord _) = True
isBaseType (MTyBase (MKType _) _) = True
isBaseType (MTyBase _ _) = True
isBaseType (MTyNum _) = False

-- | If a 'MonType' is a type-level number, return its 'OpenTerm', otherwise
-- return 'Nothing'
monTypeNum :: MonType -> Maybe OpenTerm
monTypeNum (MTyNum t) = Just t
monTypeNum (MTyBase MKNum t) = Just t
monTypeNum _ = Nothing

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
monTypeKind (MTySeq _ tp) =
  do sort <- monTypeKind tp >>= monKindToSort
     return $ MKType sort
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
toArgType :: HasSpecMParams => MonType -> OpenTerm
toArgType (MTyForall x k body) =
  piOpenTerm x (monKindOpenTerm k) (\tp -> toCompType (body $ MTyBase k tp))
toArgType (MTyArrow t1 t2) =
  arrowOpenTerm "_" (toArgType t1) (toCompType t2)
toArgType (MTySeq n t) =
  applyOpenTermMulti (globalOpenTerm "CryptolM.mseq")
  [specMEvType ?specMParams, specMStack ?specMParams, n, toArgType t]
toArgType (MTyPair mtp1 mtp2) =
  pairTypeOpenTerm (toArgType mtp1) (toArgType mtp2)
toArgType (MTyRecord tps) =
  recordTypeOpenTerm $ map (\(f,tp) -> (f, toArgType tp)) tps
toArgType (MTyBase _ t) = t
toArgType (MTyNum n) = n

-- | Convert a 'MonType' to the computation type @CompMT(tp)@ it represents
toCompType :: HasSpecMParams => MonType -> OpenTerm
toCompType mtp@(MTyForall _ _ _) = toArgType mtp
toCompType mtp@(MTyArrow _ _) = toArgType mtp
toCompType mtp =
  let SpecMParams { specMEvType = ev, specMStack = stack } = ?specMParams in
  applyOpenTermMulti (globalOpenTerm "Prelude.SpecM") [ev, stack, toArgType mtp]

-- | The mapping for monadifying Cryptol typeclasses
-- FIXME: this is no longer needed, as it is now the identity
typeclassMonMap :: [(Ident,Ident)]
typeclassMonMap =
  [("Cryptol.PEq", "Cryptol.PEq"),
   ("Cryptol.PCmp", "Cryptol.PCmp"),
   ("Cryptol.PSignedCmp", "Cryptol.PSignedCmp"),
   ("Cryptol.PZero", "Cryptol.PZero"),
   ("Cryptol.PLogic", "Cryptol.PLogic"),
   ("Cryptol.PRing", "Cryptol.PRing"),
   ("Cryptol.PIntegral", "Cryptol.PIntegral"),
   ("Cryptol.PLiteral", "Cryptol.PLiteral")]

-- | The list of functions that are monadified as themselves in types
typeLevelOpMonList :: [Ident]
typeLevelOpMonList = ["Cryptol.tcAdd", "Cryptol.tcSub", "Cryptol.tcMul",
                      "Cryptol.tcDiv", "Cryptol.tcMod", "Cryptol.tcExp",
                      "Cryptol.tcMin", "Cryptol.tcMax"]

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

-- | Monadify a type and convert it to its corresponding argument type
monadifyTypeArgType :: (HasCallStack, HasSpecMParams) => MonadifyTypeCtx ->
                       Term -> OpenTerm
monadifyTypeArgType ctx t = toArgType $ monadifyType ctx t

-- | Apply a monadified type to a type or term argument in the sense of
-- 'applyPiOpenTerm', meaning give the type of applying @f@ of a type to a
-- particular argument @arg@
applyMonType :: HasCallStack => MonType -> Either MonType ArgMonTerm -> MonType
applyMonType (MTyArrow _ tp_ret) (Right _) = tp_ret
applyMonType (MTyForall _ _ f) (Left mtp) = f mtp
applyMonType _ _ = error "applyMonType: application at incorrect type"

-- | Convert a SAW core 'Term' to a monadification type
monadifyType :: (HasCallStack, HasSpecMParams) => MonadifyTypeCtx -> Term ->
                MonType
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
monadifyType _ (asTupleType -> Just []) = mkMonType0 unitTypeOpenTerm
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
  let lenOT = monadifyTypeNat ctx len in
  MTySeq (ctorOpenTerm "Cryptol.TCNum" [lenOT]) $ monadifyType ctx tp
monadifyType ctx (asApplyAll -> ((asGlobalDef -> Just seq_id), [n, a]))
  | seq_id == "Cryptol.seq" =
    let nOT = monadifyTypeArgType ctx n in
    MTySeq nOT $ monadifyType ctx a
monadifyType ctx (asApp -> Just ((asGlobalDef -> Just f), arg))
  | Just f_trans <- lookup f typeclassMonMap =
    MTyBase (MKType $ mkSort 1) $
    applyOpenTerm (globalOpenTerm f_trans) $ monadifyTypeArgType ctx arg
monadifyType _ (asGlobalDef -> Just bool_id)
  | bool_id == "Prelude.Bool" =
    mkMonType0 (globalOpenTerm "Prelude.Bool")
{-
monadifyType ctx (asApplyAll -> (f, args))
  | Just glob <- asTypedGlobalDef f
  , Just ec_k <- monadifyKind $ globalDefType glob
  , margs <- map (monadifyType ctx) args
  , Just k_out <- applyKinds ec_k margs =
    MTyBase k_out (applyOpenTermMulti (globalDefOpenTerm glob) $
                   map toArgType margs)
-}
monadifyType _ (asCtor -> Just (pn, []))
  | primName pn == "Cryptol.TCInf"
  = MTyNum $ ctorOpenTerm "Cryptol.TCInf" []
monadifyType ctx (asCtor -> Just (pn, [n]))
  | primName pn == "Cryptol.TCNum"
  = MTyNum $ ctorOpenTerm "Cryptol.TCNum" [monadifyTypeNat ctx n]
monadifyType ctx (asApplyAll -> ((asGlobalDef -> Just f), args))
  | f `elem` typeLevelOpMonList =
    MTyNum $
    applyOpenTermMulti (globalOpenTerm f) $ map (monadifyTypeArgType ctx) args
monadifyType ctx (asLocalVar -> Just i)
  | i < length ctx
  , (_,_,Just tp) <- ctx!!i = tp
monadifyType ctx tp =
  error ("monadifyType: not a valid type for monadification: "
         ++ ppTermInTypeCtx ctx tp)

-- | Monadify a type-level natural number
monadifyTypeNat :: (HasCallStack, HasSpecMParams) => MonadifyTypeCtx -> Term ->
                   OpenTerm
monadifyTypeNat _ (asNat -> Just n) = natOpenTerm n
monadifyTypeNat ctx (asLocalVar -> Just i)
  | i < length ctx
  , (_,_,Just tp) <- ctx!!i = toArgType tp
monadifyTypeNat ctx tp =
  error ("monadifyTypeNat: not a valid natural number for monadification: "
         ++ ppTermInTypeCtx ctx tp)


----------------------------------------------------------------------
-- * Monadified Terms
----------------------------------------------------------------------

-- | A representation of a term that has been translated to argument type
-- @MT(tp)@
data ArgMonTerm
    -- | A monadification term of a base type @MT(tp)@
  = BaseMonTerm MonType OpenTerm
    -- | A monadification term of non-depedent function type
  | FunMonTerm LocalName MonType MonType (ArgMonTerm -> MonTerm)
    -- | A monadification term of polymorphic type
  | ForallMonTerm LocalName MonKind (MonType -> MonTerm)

-- | A representation of a term that has been translated to computational type
-- @CompMT(tp)@
data MonTerm
  = ArgMonTerm ArgMonTerm
  | CompMonTerm MonType OpenTerm

-- | Get the monadification type of a monadification term
class GetMonType a where
  getMonType :: a -> MonType

instance GetMonType ArgMonTerm where
  getMonType (BaseMonTerm tp _) = tp
  getMonType (ForallMonTerm x k body) = MTyForall x k (getMonType . body)
  getMonType (FunMonTerm _ tp_in tp_out _) = MTyArrow tp_in tp_out

instance GetMonType MonTerm where
  getMonType (ArgMonTerm t) = getMonType t
  getMonType (CompMonTerm tp _) = tp


-- | Convert a monadification term to a SAW core term of type @CompMT(tp)@
class ToCompTerm a where
  toCompTerm :: HasSpecMParams => a -> OpenTerm

instance ToCompTerm ArgMonTerm where
  toCompTerm (BaseMonTerm mtp t) =
    applyOpenTermMulti (globalOpenTerm "Prelude.retS")
    [specMEvType ?specMParams, specMStack ?specMParams, toArgType mtp, t]
  toCompTerm (FunMonTerm x tp_in _ body) =
    lambdaOpenTerm x (toArgType tp_in) (toCompTerm . body . fromArgTerm tp_in)
  toCompTerm (ForallMonTerm x k body) =
    lambdaOpenTerm x (monKindOpenTerm k) (toCompTerm . body . MTyBase k)

instance ToCompTerm MonTerm where
  toCompTerm (ArgMonTerm amtrm) = toCompTerm amtrm
  toCompTerm (CompMonTerm _ trm) = trm


-- | Convert an 'ArgMonTerm' to a SAW core term of type @MT(tp)@
toArgTerm :: HasSpecMParams => ArgMonTerm -> OpenTerm
toArgTerm (BaseMonTerm _ t) = t
toArgTerm t = toCompTerm t


-- | Build a monadification term from a term of type @MT(tp)@
class FromArgTerm a where
  fromArgTerm :: HasSpecMParams => MonType -> OpenTerm -> a

instance FromArgTerm ArgMonTerm where
  fromArgTerm (MTyForall x k body) t =
    ForallMonTerm x k (\tp -> fromCompTerm (body tp) (applyOpenTerm t $
                                                      toArgType tp))
  fromArgTerm (MTyArrow t1 t2) t =
    FunMonTerm "_" t1 t2 (\x -> fromCompTerm t2 (applyOpenTerm t $ toArgTerm x))
  fromArgTerm tp t = BaseMonTerm tp t

instance FromArgTerm MonTerm where
  fromArgTerm mtp t = ArgMonTerm $ fromArgTerm mtp t

-- | Build a monadification term from a computational term of type @CompMT(tp)@
fromCompTerm :: HasSpecMParams => MonType -> OpenTerm -> MonTerm
fromCompTerm mtp t | isBaseType mtp = CompMonTerm mtp t
fromCompTerm mtp t = ArgMonTerm $ fromArgTerm mtp t

-- | Take a function of type @A1 -> ... -> An -> SpecM E emptyFunStack B@ and
-- lift the stack of the output type to an arbitrary @stack@ parameter using
-- @liftStackS@. Note that @liftStackS@ is only added if the stack of the
-- output type is non-empty, i.e. not @emptyFunStack@. Otherwise, this operation
-- leaves the function unchanged.
class LiftCompStack a where
  liftCompStack :: HasSpecMParams => a -> a

instance LiftCompStack ArgMonTerm where
  liftCompStack t@(BaseMonTerm _ _) =
    -- A pure term need not be lifted, because it is not computational
    t
  liftCompStack (FunMonTerm nm tp_in tp_out body) =
    FunMonTerm nm tp_in tp_out $ \x -> liftCompStack $ body x
  liftCompStack (ForallMonTerm nm k body) =
    ForallMonTerm nm k $ \x -> liftCompStack $ body x

instance LiftCompStack MonTerm where
  liftCompStack (ArgMonTerm amtrm) = ArgMonTerm $ liftCompStack amtrm
  liftCompStack (CompMonTerm mtp trm) = CompMonTerm mtp $ OpenTerm $ do
    -- Only add @liftStackS@ when the stack is not @emptyFunStack@
    empty_stk <- typedVal <$> unOpenTerm emptyStackOpenTerm
    curr_stk  <- typedVal <$> unOpenTerm (specMStack ?specMParams)
    curr_stk_empty <- liftTCM scConvertible False empty_stk curr_stk
    unOpenTerm $ if curr_stk_empty then trm else
      applyGlobalOpenTerm "Prelude.liftStackS"
      [specMEvType ?specMParams, specMStack ?specMParams, toArgType mtp, trm]

-- | Test if a monadification type @tp@ is pure, meaning @MT(tp)=tp@
monTypeIsPure :: MonType -> Bool
monTypeIsPure (MTyForall _ _ _) = False -- NOTE: this could potentially be true
monTypeIsPure (MTyArrow _ _) = False
monTypeIsPure (MTySeq _ _) = False
monTypeIsPure (MTyPair mtp1 mtp2) = monTypeIsPure mtp1 && monTypeIsPure mtp2
monTypeIsPure (MTyRecord fld_mtps) = all (monTypeIsPure . snd) fld_mtps
monTypeIsPure (MTyBase _ _) = True
monTypeIsPure (MTyNum _) = True

-- | Test if a monadification type @tp@ is semi-pure, meaning @SemiP(tp) = tp@,
-- where @SemiP@ is defined in the documentation for 'fromSemiPureTermFun' below
monTypeIsSemiPure :: MonType -> Bool
monTypeIsSemiPure (MTyForall _ k tp_f) =
  monTypeIsSemiPure $ tp_f $ MTyBase k $
  -- This dummy OpenTerm should never be inspected by the recursive call
  error "monTypeIsSemiPure"
monTypeIsSemiPure (MTyArrow tp_in tp_out) =
  monTypeIsPure tp_in && monTypeIsSemiPure tp_out
monTypeIsSemiPure (MTySeq _ _) = False
monTypeIsSemiPure (MTyPair mtp1 mtp2) =
  -- NOTE: functions in pairs are not semi-pure; only pure types in pairs are
  -- semi-pure
  monTypeIsPure mtp1 && monTypeIsPure mtp2
monTypeIsSemiPure (MTyRecord fld_mtps) =
  -- Same as pairs, record types are only semi-pure if they are pure
  all (monTypeIsPure . snd) fld_mtps
monTypeIsSemiPure (MTyBase _ _) = True
monTypeIsSemiPure (MTyNum _) = True

-- | Build a monadification term from a function on terms which, when viewed as
-- a lambda, is a "semi-pure" function of the given monadification type, meaning
-- it maps terms of argument type @MT(tp)@ to an output value of argument type;
-- i.e., it has type @SemiP(tp)@, defined as:
--
-- > SemiP(Pi x (sort 0) b) = Pi x (sort 0) SemiP(b)
-- > SemiP(Pi x Num b) = Pi x Num SemiP(b)
-- > SemiP(Pi _ a b) = MT(a) -> SemiP(b)
-- > SemiP(a) = MT(a)
fromSemiPureTermFun :: HasSpecMParams => MonType -> ([OpenTerm] -> OpenTerm) ->
                       ArgMonTerm
fromSemiPureTermFun (MTyForall x k body) f =
  ForallMonTerm x k $ \tp ->
  ArgMonTerm $ fromSemiPureTermFun (body tp) (f . (toArgType tp:))
fromSemiPureTermFun (MTyArrow t1 t2) f =
  FunMonTerm "_" t1 t2 $ \x ->
  ArgMonTerm $ fromSemiPureTermFun t2 (f . (toArgTerm x:))
fromSemiPureTermFun tp f = BaseMonTerm tp (f [])

-- | Like 'fromSemiPureTermFun' but use a term rather than a term function
fromSemiPureTerm :: HasSpecMParams => MonType -> OpenTerm -> ArgMonTerm
fromSemiPureTerm mtp t = fromSemiPureTermFun mtp (applyOpenTermMulti t)

-- | Build a 'MonTerm' that 'fail's when converted to a term
failMonTerm :: HasSpecMParams => MonType -> String -> MonTerm
failMonTerm mtp str = fromArgTerm mtp (failOpenTerm str)

-- | Build an 'ArgMonTerm' that 'fail's when converted to a term
failArgMonTerm :: HasSpecMParams => MonType -> String -> ArgMonTerm
failArgMonTerm tp str = fromArgTerm tp (failOpenTerm str)

-- | Apply a monadified term to a type or term argument
applyMonTerm :: HasCallStack => MonTerm -> Either MonType ArgMonTerm -> MonTerm
applyMonTerm (ArgMonTerm (FunMonTerm _ _ _ f)) (Right arg) = f arg
applyMonTerm (ArgMonTerm (ForallMonTerm _ _ f)) (Left mtp) = f mtp
applyMonTerm (ArgMonTerm (FunMonTerm _ _ _ _)) (Left _) =
  error "applyMonTerm: application of term-level function to type-level argument"
applyMonTerm (ArgMonTerm (ForallMonTerm _ _ _)) (Right _) =
  error "applyMonTerm: application of type-level function to term-level argument"
applyMonTerm (ArgMonTerm (BaseMonTerm _ _)) _ =
  error "applyMonTerm: application of non-function base term"
applyMonTerm (CompMonTerm _ _) _ =
  error "applyMonTerm: application of computational term"

-- | Apply a monadified term to 0 or more arguments
applyMonTermMulti :: HasCallStack => MonTerm -> [Either MonType ArgMonTerm] ->
                     MonTerm
applyMonTermMulti = foldl applyMonTerm

-- | Build a 'MonTerm' from a global of a given argument type, applying it to
-- the current 'SpecMParams' if the 'Bool' flag is 'True' or lifting it using
-- @liftStackS@ if it is 'False' and the stack is non-empty
mkGlobalArgMonTerm :: HasSpecMParams => MonType -> Ident -> Bool -> ArgMonTerm
mkGlobalArgMonTerm tp ident params_p =
  (if params_p then id else liftCompStack) $
  fromArgTerm tp (if params_p
                  then applyGlobalOpenTerm ident (paramsToTerms ?specMParams)
                  else globalOpenTerm ident)

-- | Build a 'MonTerm' from a 'GlobalDef' of semi-pure type, applying it to
-- the current 'SpecMParams' if the 'Bool' flag is 'True'
mkSemiPureGlobalDefTerm :: HasSpecMParams => GlobalDef -> Bool -> ArgMonTerm
mkSemiPureGlobalDefTerm glob params_p =
  fromSemiPureTerm (monadifyType [] $ globalDefType glob)
  (if params_p
   then applyOpenTermMulti (globalDefOpenTerm glob) (paramsToTerms ?specMParams)
   else globalDefOpenTerm glob)

-- | Build a 'MonTerm' from a constructor with the given 'PrimName'
mkCtorArgMonTerm :: HasSpecMParams => PrimName Term -> ArgMonTerm
mkCtorArgMonTerm pn
  | not (isFirstOrderType (primType pn)) =
    failArgMonTerm (monadifyType [] $ primType pn)
    ("monadification failed: cannot handle constructor "
     ++ show (primName pn) ++ " with higher-order type")
mkCtorArgMonTerm pn =
  fromSemiPureTermFun (monadifyType [] $ primType pn) (ctorOpenTerm $ primName pn)


----------------------------------------------------------------------
-- * Monadification Environments and Contexts
----------------------------------------------------------------------

-- | A monadification macro is a function that inspects its first @N@ arguments
-- before deciding how to monadify itself
data MonMacro = MonMacro {
  macroNumArgs :: Int,
  macroApply :: GlobalDef -> [Term] -> MonadifyM MonTerm }

-- | Make a simple 'MonMacro' that inspects 0 arguments and just returns a term,
-- lifted with @liftStackS@ if the outer stack is non-empty
monMacro0 :: MonTerm -> MonMacro
monMacro0 mtrm = MonMacro 0 $ \_ _ -> usingSpecMParams $
  return $ liftCompStack mtrm

-- | Make a 'MonMacro' that maps a named global to a global of semi-pure type.
-- (See 'fromSemiPureTermFun'.) Because we can't get access to the type of the
-- global until we apply the macro, we monadify its type at macro application
-- time. The 'Bool' flag indicates whether the current 'SpecMParams' should also
-- be passed as the first two arguments to the "to" global.
semiPureGlobalMacro :: Ident -> Ident -> Bool -> MonMacro
semiPureGlobalMacro from to params_p =
  MonMacro 0 $ \glob args -> usingSpecMParams $
  if globalDefName glob == ModuleIdentifier from && args == [] then
    return $ ArgMonTerm $
    fromSemiPureTerm (monadifyType [] $ globalDefType glob)
    (if params_p then applyGlobalOpenTerm to (paramsToTerms ?specMParams)
     else globalOpenTerm to)
  else
    error ("Monadification macro for " ++ show from ++ " applied incorrectly")

-- | Make a 'MonMacro' that maps a named global to a global of argument type.
-- Because we can't get access to the type of the global until we apply the
-- macro, we monadify its type at macro application time. The 'Bool' flag
-- indicates whether the "to" global is polymorphic in the event type and
-- function stack; if so, the current 'SpecMParams' are passed as its first two
-- arguments, and otherwise the returned computation is lifted with
-- @liftStackS@ if the outer stack is non-empty.
argGlobalMacro :: NameInfo -> Ident -> Bool -> MonMacro
argGlobalMacro from to params_p =
  MonMacro 0 $ \glob args -> usingSpecMParams $
  if globalDefName glob == from && args == [] then
    return $ ArgMonTerm $
    mkGlobalArgMonTerm (monadifyType [] $ globalDefType glob) to params_p
  else
    error ("Monadification macro for " ++ show from ++ " applied incorrectly")

-- | An environment for monadification
data MonadifyEnv = MonadifyEnv {
  -- | How to monadify named functions
  monEnvMonTable :: Map NameInfo MonMacro,
  -- | The @EvType@ used for monadification
  monEnvEvType :: OpenTerm
  }

-- | Build a 'SpecMParams' with the empty funciton stack from a 'MonadifyEnv'
monEnvParams :: MonadifyEnv -> SpecMParams OpenTerm
monEnvParams env = paramsOfEvType (monEnvEvType env)

-- | Look up the monadification of a name in a 'MonadifyEnv'
monEnvLookup :: NameInfo -> MonadifyEnv -> Maybe MonMacro
monEnvLookup nmi env = Map.lookup nmi (monEnvMonTable env)

-- | Add a monadification for a name to a 'MonadifyEnv'
monEnvAdd :: NameInfo -> MonMacro -> MonadifyEnv -> MonadifyEnv
monEnvAdd nmi macro env =
  env { monEnvMonTable = Map.insert nmi macro (monEnvMonTable env) }

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

-- | A memoization table for monadifying terms: a map from 'TermIndex'es to
-- 'MonTerm's and, possibly, corresponding 'ArgMonTerm's. The latter are simply
-- the result of calling 'argifyMonTerm' on the former, but are only added when
-- needed (i.e. when 'memoArgMonTerm' is called, e.g. in 'monadifyArg').
type MonadifyMemoTable = IntMap (MonTerm, Maybe ArgMonTerm)

-- | The empty memoization table
emptyMemoTable :: MonadifyMemoTable
emptyMemoTable = IntMap.empty


----------------------------------------------------------------------
-- * The Monadification Monad
----------------------------------------------------------------------

-- | The read-only state of a monadification computation
data MonadifyROState = MonadifyROState {
  -- | The monadification environment
  monStEnv :: MonadifyEnv,
  -- | The monadification context 
  monStCtx :: MonadifyCtx,
  -- | The current @SpecM@ function stack
  monStStack :: OpenTerm,
  -- | The monadified return type of the top-level term being monadified
  monStTopRetType :: OpenTerm
}

-- | Get the monadification table from a 'MonadifyROState'
monStMonTable :: MonadifyROState -> Map NameInfo MonMacro
monStMonTable = monEnvMonTable . monStEnv

-- | The monad for monadifying SAW core terms
newtype MonadifyM a =
  MonadifyM { unMonadifyM ::
                ReaderT MonadifyROState (StateT MonadifyMemoTable
                                         (Cont MonTerm)) a }
  deriving (Functor, Applicative, Monad,
            MonadReader MonadifyROState, MonadState MonadifyMemoTable)

-- | Get the current 'SpecMParams' in a 'MonadifyM' computation
askSpecMParams :: MonadifyM (SpecMParams OpenTerm)
askSpecMParams =
  do st <- ask
     let ev = monEnvEvType $ monStEnv st
     let stack = monStStack st
     return (SpecMParams { specMEvType = ev, specMStack = stack })

-- | Run a 'MonadifyM' computation with the current 'SpecMParams'
usingSpecMParams :: (HasSpecMParams => MonadifyM a) -> MonadifyM a
usingSpecMParams m =
  do params <- askSpecMParams
     let ?specMParams = params in m

-- | Push a frame of recursive functions onto the current 'SpecMParams'
pushingSpecMParamsM :: [MonType] -> MonadifyM a -> MonadifyM a
pushingSpecMParamsM tps m =
  usingSpecMParams $
  local (\rost -> rost { monStStack = pushSpecMFrame tps (monStStack rost) }) m

instance Fail.MonadFail MonadifyM where
  fail str =
    usingSpecMParams $
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
     return $
       runMonadifyM (monStEnv ro_st) (monStCtx ro_st) (monStStack ro_st) ret_tp m

-- | Get the monadified return type of the top-level term being monadified
topRetType :: MonadifyM OpenTerm
topRetType = monStTopRetType <$> ask

-- | Run a monadification computation
--
-- FIXME: document the arguments
runMonadifyM :: MonadifyEnv -> MonadifyCtx -> OpenTerm ->
                OpenTerm -> MonadifyM MonTerm -> MonTerm
runMonadifyM env ctx stack top_ret_tp m =
  let ro_st = MonadifyROState env ctx stack top_ret_tp in
  runCont (evalStateT (runReaderT (unMonadifyM m) ro_st) emptyMemoTable) id

-- | Run a monadification computation using a mapping for identifiers that have
-- already been monadified and generate a SAW core term
runCompleteMonadifyM :: MonadIO m => SharedContext -> MonadifyEnv ->
                        Term -> MonadifyM MonTerm ->
                        m Term
runCompleteMonadifyM sc env top_ret_tp m =
  let ?specMParams = monEnvParams env in
  liftIO $ completeOpenTerm sc $ toCompTerm $
  runMonadifyM env [] emptyStackOpenTerm (toArgType $ monadifyType [] top_ret_tp) m

-- | Memoize a computation of the monadified term associated with a 'TermIndex'
memoMonTerm :: TermIndex -> MonadifyM MonTerm -> MonadifyM MonTerm
memoMonTerm i m =
  (IntMap.lookup i <$> get) >>= \case
  Just (mtm, _) ->
    return mtm
  Nothing ->
    do mtm <- m
       modify (IntMap.insert i (mtm, Nothing))
       return mtm

-- | Memoize a computation of the monadified term of argument type associated
-- with a 'TermIndex', using a memoized 'ArgTerm' directly if it exists or
-- applying 'argifyMonTerm' to a memoized 'MonTerm' (and memoizing the result)
-- if it exists
memoArgMonTerm :: TermIndex -> MonadifyM MonTerm -> MonadifyM ArgMonTerm
memoArgMonTerm i m =
  (IntMap.lookup i <$> get) >>= \case
  Just (_, Just argmtm) ->
    return argmtm
  Just (mtm, Nothing) ->
    do argmtm <- argifyMonTerm mtm
       modify (IntMap.insert i (mtm, Just argmtm))
       return argmtm
  Nothing ->
    do mtm <- m
       argmtm <- argifyMonTerm mtm
       modify (IntMap.insert i (mtm, Just argmtm))
       return argmtm

-- | Turn a 'MonTerm' of type @CompMT(tp)@ to a term of argument type @MT(tp)@
-- by inserting a monadic bind if the 'MonTerm' is computational
argifyMonTerm :: MonTerm -> MonadifyM ArgMonTerm
argifyMonTerm (ArgMonTerm mtrm) = return mtrm
argifyMonTerm (CompMonTerm mtp trm) =
  usingSpecMParams $
  do let tp = toArgType mtp
     top_ret_tp <- topRetType
     shiftMonadifyM $ \k ->
       CompMonTerm (mkMonType0 top_ret_tp) $
       applyOpenTermMulti (globalOpenTerm "Prelude.bindS")
       [specMEvType ?specMParams, specMStack ?specMParams, tp, top_ret_tp, trm,
        lambdaOpenTerm "x" tp (toCompTerm . k . fromArgTerm mtp)]

-- | Build a proof of @isFinite n@ by calling @assertFiniteS@ and binding the
-- result to an 'ArgMonTerm'
assertIsFinite :: HasSpecMParams => MonType -> MonadifyM ArgMonTerm
assertIsFinite (MTyNum n) =
  argifyMonTerm (CompMonTerm
                 (mkMonType0 (applyOpenTerm
                              (globalOpenTerm "CryptolM.isFinite") n))
                 (applyGlobalOpenTerm "CryptolM.assertFiniteS"
                  [specMEvType ?specMParams, specMStack ?specMParams, n]))
assertIsFinite _ =
  fail ("assertIsFinite applied to non-Num argument")


----------------------------------------------------------------------
-- * Monadification
----------------------------------------------------------------------

-- | Monadify a type in the context of the 'MonadifyM' monad
monadifyTypeM :: HasCallStack => Term -> MonadifyM MonType
monadifyTypeM tp =
  usingSpecMParams $
  do ctx <- monStCtx <$> ask
     return $ monadifyType (ctxToTypeCtx ctx) tp

-- | Monadify a term to a monadified term of argument type
monadifyArg :: HasCallStack => Maybe MonType -> Term -> MonadifyM ArgMonTerm
{-
monadifyArg _ t
  | trace ("Monadifying term of argument type: " ++ showTerm t) False
  = undefined
-}
monadifyArg mtp t@(STApp { stAppIndex = ix }) =
  memoArgMonTerm ix $ usingSpecMParams $ monadifyTerm' mtp t
monadifyArg mtp t =
  usingSpecMParams (monadifyTerm' mtp t) >>= argifyMonTerm

-- | Monadify a term to argument type and convert back to a term
monadifyArgTerm :: HasCallStack => Maybe MonType -> Term -> MonadifyM OpenTerm
monadifyArgTerm mtp t = usingSpecMParams (toArgTerm <$> monadifyArg mtp t)

-- | Monadify a term
monadifyTerm :: Maybe MonType -> Term -> MonadifyM MonTerm
{-
monadifyTerm _ t
  | trace ("Monadifying term: " ++ showTerm t) False
  = undefined
-}
monadifyTerm mtp t@(STApp { stAppIndex = ix }) =
  memoMonTerm ix $ usingSpecMParams $ monadifyTerm' mtp t
monadifyTerm mtp t =
  usingSpecMParams $ monadifyTerm' mtp t

-- | The main implementation of 'monadifyTerm', which monadifies a term given an
-- optional monadification type. The type must be given for introduction forms
-- (i.e.,, lambdas, pairs, and records), but is optional for elimination forms
-- (i.e., applications, projections, and also in this case variables). Note that
-- this means monadification will fail on terms with beta or tuple redexes.
monadifyTerm' :: HasCallStack => HasSpecMParams =>
                 Maybe MonType -> Term -> MonadifyM MonTerm
monadifyTerm' (Just mtp) t@(asLambda -> Just _) =
  ask >>= \(MonadifyROState { monStEnv = env,
                              monStCtx = ctx, monStStack = stack }) ->
  return $ monadifyLambdas env ctx stack mtp t
{-
monadifyTerm' (Just mtp@(MTyForall _ _ _)) t =
  ask >>= \ro_st ->
  get >>= \table ->
  return $ monadifyLambdas (monStEnv ro_st) table (monStCtx ro_st) mtp t
monadifyTerm' (Just mtp@(MTyArrow _ _)) t =
  ask >>= \ro_st ->
  get >>= \table ->
  return $ monadifyLambdas (monStEnv ro_st) table (monStCtx ro_st) mtp t
-}
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
monadifyTerm' (Just mtp@(MTySeq n mtp_elem)) (asFTermF ->
                                              Just (ArrayValue _ trms)) =
  do trms' <- traverse (monadifyArgTerm $ Just mtp_elem) trms
     return $ fromArgTerm mtp $
       applyOpenTermMulti (globalOpenTerm "CryptolM.seqToMseq")
       [specMEvType ?specMParams, specMStack ?specMParams,
        n, toArgType mtp_elem,
        flatOpenTerm $ ArrayValue (toArgType mtp_elem) trms']
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
monadifyTerm' _ (asTupleValue -> Just []) =
  return $ ArgMonTerm $
  fromSemiPureTerm (mkMonType0 unitTypeOpenTerm) unitOpenTerm
monadifyTerm' _ (asCtor -> Just (pn, args)) =
  monadifyApply (ArgMonTerm $ mkCtorArgMonTerm pn) args
monadifyTerm' _ (asApplyAll -> (asTypedGlobalDef -> Just glob, args)) =
  (Map.lookup (globalDefName glob) <$> monStMonTable <$> ask) >>= \case
  Just macro ->
    do let (macro_args, reg_args) = splitAt (macroNumArgs macro) args
       mtrm_f <- macroApply macro glob macro_args
       monadifyApply mtrm_f reg_args
  Nothing ->
    monadifyTypeM (globalDefType glob) >>= \glob_mtp ->
    if monTypeIsSemiPure glob_mtp then
      monadifyApply (ArgMonTerm $ fromSemiPureTerm glob_mtp $
                     globalDefOpenTerm glob) args
    else error ("Monadification failed: unhandled constant: "
                ++ globalDefString glob)
monadifyTerm' _ (asApp -> Just (f, arg)) =
  do mtrm_f <- monadifyTerm Nothing f
     monadifyApply mtrm_f [arg]
monadifyTerm' _ t =
  (monStCtx <$> ask) >>= \ctx ->
  fail ("Monadifiction failed: no case for term: " ++ ppTermInMonCtx ctx t)


-- | Monadify the application of a monadified term to a list of terms, using the
-- type of the already monadified to monadify the arguments
monadifyApply :: HasCallStack => MonTerm -> [Term] -> MonadifyM MonTerm
monadifyApply f (t : ts)
  | MTyArrow tp_in _ <- getMonType f =
    do mtrm <- monadifyArg (Just tp_in) t
       monadifyApply (applyMonTerm f (Right mtrm)) ts
monadifyApply f (t : ts)
  | MTyForall _ _ _ <- getMonType f =
    do mtp <- monadifyTypeM t
       monadifyApply (applyMonTerm f (Left mtp)) ts
monadifyApply _ (_:_) = fail "monadifyApply: application at incorrect type"
monadifyApply f [] = return f


-- | FIXME: documentation; get our type down to a base type before going into
-- the MonadifyM monad
monadifyLambdas :: HasCallStack => MonadifyEnv -> MonadifyCtx -> OpenTerm ->
                   MonType -> Term -> MonTerm
monadifyLambdas env ctx stack (MTyForall _ k tp_f) (asLambda ->
                                                    Just (x, x_tp, body)) =
  -- FIXME: check that monadifyKind x_tp == k
  ArgMonTerm $ ForallMonTerm x k $ \mtp ->
  monadifyLambdas env ((x,x_tp,Left mtp) : ctx) stack (tp_f mtp) body
monadifyLambdas env ctx stack (MTyArrow tp_in tp_out) (asLambda ->
                                                       Just (x, x_tp, body)) =
  -- FIXME: check that monadifyType x_tp == tp_in
  ArgMonTerm $ FunMonTerm x tp_in tp_out $ \arg ->
  monadifyLambdas env ((x,x_tp,Right (ArgMonTerm arg)) : ctx) stack tp_out body
monadifyLambdas env ctx stack tp t =
  monadifyEtaExpand env ctx stack tp tp t []

-- | FIXME: documentation
monadifyEtaExpand :: HasCallStack => MonadifyEnv -> MonadifyCtx -> OpenTerm ->
                     MonType -> MonType -> Term ->
                     [Either MonType ArgMonTerm] -> MonTerm
monadifyEtaExpand env ctx stack top_mtp (MTyForall x k tp_f) t args =
  ArgMonTerm $ ForallMonTerm x k $ \mtp ->
  monadifyEtaExpand env ctx stack top_mtp (tp_f mtp) t (args ++ [Left mtp])
monadifyEtaExpand env ctx stack top_mtp (MTyArrow tp_in tp_out) t args =
  ArgMonTerm $ FunMonTerm "_" tp_in tp_out $ \arg ->
  monadifyEtaExpand env ctx stack top_mtp tp_out t (args ++ [Right arg])
monadifyEtaExpand env ctx stack top_mtp mtp t args =
  let ?specMParams = (monEnvParams env) { specMStack = stack } in
  applyMonTermMulti
  (runMonadifyM env ctx stack (toArgType mtp) (monadifyTerm (Just top_mtp) t))
  args


----------------------------------------------------------------------
-- * Handling the Primitives
----------------------------------------------------------------------

-- | The macro for unsafeAssert, which checks the type of the objects being
-- compared and dispatches to the proper comparison function
unsafeAssertMacro :: MonMacro
unsafeAssertMacro = MonMacro 1 $ \_ ts ->
  usingSpecMParams $
  let numFunType =
        MTyForall "n" (MKType $ mkSort 0) $ \n ->
        MTyForall "m" (MKType $ mkSort 0) $ \m ->
        MTyBase (MKType $ mkSort 0) $
        dataTypeOpenTerm "Prelude.Eq"
        [dataTypeOpenTerm "Cryptol.Num" [],
         toArgType n, toArgType m] in
  case ts of
    [(asDataType -> Just (num, []))]
      | primName num == "Cryptol.Num" ->
        return $ ArgMonTerm $
        mkGlobalArgMonTerm numFunType "CryptolM.numAssertEqS" True
    _ ->
      fail "Monadification failed: unsafeAssert applied to non-Num type"

-- | The macro for if-then-else, which contains any binds in a branch to that
-- branch
iteMacro :: MonMacro
iteMacro = MonMacro 4 $ \_ args -> usingSpecMParams $
  do let (tp, cond, branch1, branch2) =
           case args of
             [t1, t2, t3, t4] -> (t1, t2, t3, t4)
             _ -> error "iteMacro: wrong number of arguments!"
     atrm_cond <- monadifyArg (Just boolMonType) cond
     mtp <- monadifyTypeM tp
     mtrm1 <- resetMonadifyM (toArgType mtp) $ monadifyTerm (Just mtp) branch1
     mtrm2 <- resetMonadifyM (toArgType mtp) $ monadifyTerm (Just mtp) branch2
     case (mtrm1, mtrm2) of
       (ArgMonTerm atrm1, ArgMonTerm atrm2) ->
         return $ fromArgTerm mtp $
         applyOpenTermMulti (globalOpenTerm "Prelude.ite")
         [toArgType mtp, toArgTerm atrm_cond, toArgTerm atrm1, toArgTerm atrm2]
       _ ->
         return $ fromCompTerm mtp $
         applyOpenTermMulti (globalOpenTerm "Prelude.ite")
         [toCompType mtp, toArgTerm atrm_cond,
          toCompTerm mtrm1, toCompTerm mtrm2]

-- | The macro for the either elimination function, which converts the
-- application @either a b c@ to @either a b (CompM c)@
eitherMacro :: MonMacro
eitherMacro = MonMacro 3 $ \_ args ->
  usingSpecMParams $
  do let (tp_a, tp_b, tp_c) =
           case args of
             [t1, t2, t3] -> (t1, t2, t3)
             _ -> error "eitherMacro: wrong number of arguments!"
     mtp_a <- monadifyTypeM tp_a
     mtp_b <- monadifyTypeM tp_b
     mtp_c <- monadifyTypeM tp_c
     let eith_app = applyGlobalOpenTerm "Prelude.either" [toArgType mtp_a,
                                                          toArgType mtp_b,
                                                          toCompType mtp_c]
     let tp_eith = dataTypeOpenTerm "Prelude.Either" [toArgType mtp_a,
                                                      toArgType mtp_b]
     return $ fromCompTerm (MTyArrow (MTyArrow mtp_a mtp_c)
                            (MTyArrow (MTyArrow mtp_b mtp_c)
                             (MTyArrow (mkMonType0 tp_eith) mtp_c))) eith_app

-- | The macro for uncurry, which converts the application @uncurry a b c@
-- to @uncurry a b (CompM c)@
uncurryMacro :: MonMacro
uncurryMacro = MonMacro 3 $ \_ args ->
  usingSpecMParams $
  do let (tp_a, tp_b, tp_c) =
           case args of
             [t1, t2, t3] -> (t1, t2, t3)
             _ -> error "uncurryMacro: wrong number of arguments!"
     mtp_a <- monadifyTypeM tp_a
     mtp_b <- monadifyTypeM tp_b
     mtp_c <- monadifyTypeM tp_c
     let unc_app = applyGlobalOpenTerm "Prelude.uncurry" [toArgType mtp_a,
                                                          toArgType mtp_b,
                                                          toCompType mtp_c]
     let tp_tup = pairTypeOpenTerm (toArgType mtp_a) (toArgType mtp_b)
     return $ fromCompTerm (MTyArrow (MTyArrow mtp_a (MTyArrow mtp_b mtp_c))
                            (MTyArrow (mkMonType0 tp_tup) mtp_c)) unc_app

-- | The macro for invariantHint, which converts @invariantHint a cond m@
-- to @invariantHint (CompM a) cond m@ and which contains any binds in the body
-- to the body
invariantHintMacro :: MonMacro
invariantHintMacro = MonMacro 3 $ \_ args -> usingSpecMParams $
  do let (tp, cond, m) =
           case args of
             [t1, t2, t3] -> (t1, t2, t3)
             _ -> error "invariantHintMacro: wrong number of arguments!"
     atrm_cond <- monadifyArg (Just boolMonType) cond
     mtp <- monadifyTypeM tp
     mtrm <- resetMonadifyM (toArgType mtp) $ monadifyTerm (Just mtp) m
     return $ fromCompTerm mtp $
       applyOpenTermMulti (globalOpenTerm "Prelude.invariantHint")
       [toCompType mtp, toArgTerm atrm_cond, toCompTerm mtrm]

-- | The macro for @asserting@ or @assuming@, which converts @asserting@ to
-- @assertingM@ or @assuming@ to @assumingM@ (depending on whether the given
-- 'Bool' is true or false, respectively) and which contains any binds in the
-- body to the body
assertingOrAssumingMacro :: Bool -> MonMacro
assertingOrAssumingMacro doAsserting = MonMacro 3 $ \_ args ->
  usingSpecMParams $
  do let (tp, cond, m) =
           case args of
             [t1, t2, t3] -> (t1, t2, t3)
             _ -> error "assertingOrAssumingMacro: wrong number of arguments!"
     atrm_cond <- monadifyArg (Just boolMonType) cond
     mtp <- monadifyTypeM tp
     mtrm <- resetMonadifyM (toArgType mtp) $ monadifyTerm (Just mtp) m
     params <- askSpecMParams
     let ident = if doAsserting then "Prelude.assertingS"
                                else "Prelude.assumingS"
     return $ fromCompTerm mtp $
       applyOpenTermMulti (globalOpenTerm ident)
       [specMEvType params, specMStack params,
        toArgType mtp, toArgTerm atrm_cond, toCompTerm mtrm]

-- | @finMacro b i j from to params_p@ makes a 'MonMacro' that maps a named
-- global @from@ whose @i@th through @(i+j-1)@th arguments are @Num@s, to a
-- named global @to@, which is of semi-pure type if and only if @b@ is 'True',
-- that takes an additional argument of type @isFinite n@ after each of the
-- aforementioned @Num@ arguments. The @params_p@ flag indicates whether the
-- current 'SpecMParams' should be passed as the first two arguments to @to@.
finMacro :: Bool -> Int -> Int -> Ident -> Ident -> Bool -> MonMacro
finMacro isSemiPure i j from to params_p =
  MonMacro (i+j) $ \glob args -> usingSpecMParams $
  do if globalDefName glob == ModuleIdentifier from && length args == i+j then
       return ()
       else error ("Monadification macro for " ++ show from ++
                   " applied incorrectly")
     let (init_args, fin_args) = splitAt i args
     -- Monadify the first @i@ args
     init_args_mtps <- mapM monadifyTypeM init_args
     let init_args_m = map toArgType init_args_mtps
     -- Monadify the @i@th through @(i+j-1)@th args and build proofs that they are finite
     fin_args_mtps <- mapM monadifyTypeM fin_args
     let fin_args_m = map toArgType fin_args_mtps
     fin_pfs <- mapM assertIsFinite fin_args_mtps
     -- Apply the type of @glob@ to the monadified arguments and apply @to@ to the
     -- monadified arguments along with the proofs that the latter arguments are finite
     let glob_tp = monadifyType [] $ globalDefType glob
     let glob_tp_app = foldl applyMonType glob_tp (map Left (init_args_mtps ++ fin_args_mtps))
     let to_app =
           applyOpenTermMulti (globalOpenTerm to)
           ((if params_p then (paramsToTerms ?specMParams ++) else id)
            init_args_m ++ concatMap (\(n,pf) -> [n, toArgTerm pf]) (zip fin_args_m fin_pfs))
     -- Finally, return the result as semi-pure dependent on @isSemiPure@
     return $ if isSemiPure
              then ArgMonTerm $ fromSemiPureTerm glob_tp_app to_app
              else ArgMonTerm $ (if params_p then id else liftCompStack)
                              $ fromArgTerm glob_tp_app to_app

-- | The macro for fix
--
-- FIXME: does not yet handle mutual recursion
fixMacro :: MonMacro
fixMacro = MonMacro 2 $ \_ args -> case args of
  [tp@(asPi -> Just _), f] ->
    do orig_params <- askSpecMParams
       mtp <- monadifyTypeM tp
       pushingSpecMParamsM [mtp] $ usingSpecMParams $ do
         amtrm_f <- monadifyArg (Just $ MTyArrow mtp mtp) f
         return $ fromCompTerm mtp $
           applyOpenTermMulti (globalOpenTerm "Prelude.multiArgFixS")
           [specMEvType orig_params, specMStack orig_params,
            lrtFromMonType mtp, toCompTerm amtrm_f]
  [(asRecordType -> Just _), _] ->
    fail "Monadification failed: cannot yet handle mutual recursion"
  _ -> error "fixMacro: malformed arguments!"

-- | A "macro mapping" maps a single pure identifier to a 'MonMacro' for it
type MacroMapping = (NameInfo, MonMacro)

-- | Build a 'MacroMapping' for an identifier to a semi-pure named function
mmSemiPure :: Ident -> Ident -> Bool -> MacroMapping
mmSemiPure from_id to_id params_p =
  (ModuleIdentifier from_id, semiPureGlobalMacro from_id to_id params_p)

-- | Build a 'MacroMapping' for an identifier to a semi-pure named function
-- whose @i@th through @(i+j-1)@th arguments are @Num@s that require
-- @isFinite@ proofs
mmSemiPureFin :: Int -> Int -> Ident -> Ident -> Bool -> MacroMapping
mmSemiPureFin i j from_id to_id params_p =
  (ModuleIdentifier from_id, finMacro True i j from_id to_id params_p)

-- | Build a 'MacroMapping' for an identifier to itself as a semi-pure function
mmSelf :: Ident -> MacroMapping
mmSelf self_id =
  (ModuleIdentifier self_id, semiPureGlobalMacro self_id self_id False)

-- | Build a 'MacroMapping' from an identifier to a function of argument type,
-- where the 'Bool' flag indicates whether the current 'SpecMArgs' should be
-- passed as additional arguments to the "to" identifier
mmArg :: Ident -> Ident -> Bool -> MacroMapping
mmArg from_id to_id params_p =
  (ModuleIdentifier from_id,
   argGlobalMacro (ModuleIdentifier from_id) to_id params_p)

-- | Build a 'MacroMapping' for an identifier to a function of argument type,
-- whose @i@th through @(i+j-1)@th arguments are @Num@s that require
-- @isFinite@ proofs, where the 'Bool' flag indicates whether the current
-- 'SpecMArgs' should be passed as additional arguments to the "to" identifier
mmArgFin :: Int -> Int -> Ident -> Ident -> Bool -> MacroMapping
mmArgFin i j from_id to_id params_p =
  (ModuleIdentifier from_id, finMacro False i j from_id to_id params_p)

-- | Build a 'MacroMapping' from an identifier and a custom 'MonMacro'
mmCustom :: Ident -> MonMacro -> MacroMapping
mmCustom from_id macro = (ModuleIdentifier from_id, macro)

-- | The default monadification environment
defaultMonEnv :: MonadifyEnv
defaultMonEnv = MonadifyEnv { monEnvMonTable = defaultMonTable,
                              monEnvEvType = globalOpenTerm "Prelude.VoidEv" }

-- | The default primitive monadification table
defaultMonTable :: Map NameInfo MonMacro
defaultMonTable =
  Map.fromList
  [
    -- Prelude functions
    mmCustom "Prelude.unsafeAssert" unsafeAssertMacro
  , mmCustom "Prelude.ite" iteMacro
  , mmCustom "Prelude.fix" fixMacro
  , mmCustom "Prelude.either" eitherMacro
  , mmCustom "Prelude.uncurry" uncurryMacro
  , mmCustom "Prelude.invariantHint" invariantHintMacro
  , mmCustom "Prelude.asserting" (assertingOrAssumingMacro True)
  , mmCustom "Prelude.assuming" (assertingOrAssumingMacro False)

    -- Top-level sequence functions
  , mmArg "Cryptol.seqMap" "CryptolM.seqMapM" True
  , mmSemiPure "Cryptol.seq_cong1" "CryptolM.mseq_cong1" True
  , mmArg "Cryptol.eListSel" "CryptolM.eListSelM" True

    -- List comprehensions
  , mmArg "Cryptol.from" "CryptolM.fromM" True
  , mmArg "Cryptol.mlet" "CryptolM.mletM" True
  , mmArg "Cryptol.seqZip" "CryptolM.seqZipM" True
  , mmSemiPure "Cryptol.seqZipSame" "CryptolM.seqZipSameM" True

    -- PEq constraints
  , mmSemiPureFin 0 1 "Cryptol.PEqSeq" "CryptolM.PEqMSeq" True
  , mmSemiPureFin 0 1 "Cryptol.PEqSeqBool" "CryptolM.PEqMSeqBool" True

    -- PCmp constraints
  , mmSemiPureFin 0 1 "Cryptol.PCmpSeq" "CryptolM.PCmpMSeq" True
  , mmSemiPureFin 0 1 "Cryptol.PCmpSeqBool" "CryptolM.PCmpMSeqBool" True

    -- PSignedCmp constraints
  , mmSemiPureFin 0 1 "Cryptol.PSignedCmpSeq" "CryptolM.PSignedCmpMSeq" True
  , mmSemiPureFin 0 1 "Cryptol.PSignedCmpSeqBool" "CryptolM.PSignedCmpMSeqBool" True

    -- PZero constraints
  , mmSemiPureFin 0 1 "Cryptol.PZeroSeq" "CryptolM.PZeroMSeq" True

    -- PLogic constraints
  , mmSemiPure "Cryptol.PLogicSeq" "CryptolM.PLogicMSeq" True
  , mmSemiPureFin 0 1 "Cryptol.PLogicSeqBool" "CryptolM.PLogicMSeqBool" True

    -- PRing constraints
  , mmSemiPure "Cryptol.PRingSeq" "CryptolM.PRingMSeq" True
  , mmSemiPureFin 0 1 "Cryptol.PRingSeqBool" "CryptolM.PRingMSeqBool" True

    -- PIntegral constraints
  , mmSemiPureFin 0 1 "Cryptol.PIntegeralSeqBool" "CryptolM.PIntegeralMSeqBool" True

    -- PLiteral constraints
  , mmSemiPureFin 0 1 "Cryptol.PLiteralSeqBool" "CryptolM.PLiteralSeqBoolM" True

    -- The Cryptol Literal primitives
  , mmSelf "Cryptol.ecNumber"
  , mmSelf "Cryptol.ecFromZ"

    -- The Ring primitives
  , mmSelf "Cryptol.ecPlus"
  , mmSelf "Cryptol.ecMinus"
  , mmSelf "Cryptol.ecMul"
  , mmSelf "Cryptol.ecNeg"
  , mmSelf "Cryptol.ecToInteger"

    -- The comparison primitives
  , mmSelf "Cryptol.ecEq"
  , mmSelf "Cryptol.ecNotEq"
  , mmSelf "Cryptol.ecLt"
  , mmSelf "Cryptol.ecLtEq"
  , mmSelf "Cryptol.ecGt"
  , mmSelf "Cryptol.ecGtEq"

    -- Sequences
  , mmSemiPure "Cryptol.ecShiftL" "CryptolM.ecShiftLM" True
  , mmSemiPure "Cryptol.ecShiftR" "CryptolM.ecShiftRM" True
  , mmSemiPure "Cryptol.ecSShiftR" "CryptolM.ecSShiftRM" True
  , mmSemiPureFin 0 1 "Cryptol.ecRotL" "CryptolM.ecRotLM" True
  , mmSemiPureFin 0 1 "Cryptol.ecRotR" "CryptolM.ecRotRM" True
  , mmSemiPureFin 0 1 "Cryptol.ecCat" "CryptolM.ecCatM" True
  , mmArg "Cryptol.ecTake" "CryptolM.ecTakeM" True
  , mmSemiPureFin 0 1 "Cryptol.ecDrop" "CryptolM.ecDropM" True
  , mmSemiPureFin 0 1 "Cryptol.ecDrop" "CryptolM.ecDropM" True
  , mmSemiPureFin 1 1 "Cryptol.ecJoin" "CryptolM.ecJoinM" True
  , mmSemiPureFin 1 1 "Cryptol.ecSplit" "CryptolM.ecSplitM" True
  , mmSemiPureFin 0 1 "Cryptol.ecReverse" "CryptolM.ecReverseM" True
  , mmSemiPure "Cryptol.ecTranspose" "CryptolM.ecTransposeM" True
  , mmArg "Cryptol.ecAt" "CryptolM.ecAtM" True
  , mmArg "Cryptol.ecUpdate" "CryptolM.ecUpdateM" True
  , mmArgFin 0 1 "Cryptol.ecAtBack" "CryptolM.ecAtBackM" True
  , mmSemiPureFin 0 2 "Cryptol.ecFromTo" "CryptolM.ecFromToM" True
  , mmSemiPureFin 0 1 "Cryptol.ecFromToLessThan" "CryptolM.ecFromToLessThanM" True
  , mmSemiPureFin 4 1 "Cryptol.ecFromThenTo" "CryptolM.ecFromThenToM" True
  , mmSemiPure "Cryptol.ecInfFrom" "CryptolM.ecInfFromM" True
  , mmSemiPure "Cryptol.ecInfFromThen" "CryptolM.ecInfFromThenM" True
  , mmArg "Cryptol.ecError" "CryptolM.ecErrorM" True
  ]


----------------------------------------------------------------------
-- * Top-Level Entrypoints
----------------------------------------------------------------------

-- | Ensure that the @CryptolM@ module is loaded
ensureCryptolMLoaded :: SharedContext -> IO ()
ensureCryptolMLoaded sc =
  scModuleIsLoaded sc (mkModuleName ["CryptolM"]) >>= \is_loaded ->
  if is_loaded then return () else
    scLoadSpecMModule sc >> scLoadCryptolMModule sc

-- | Monadify a type to its argument type and complete it to a 'Term',
-- additionally quantifying over the event type and function stack if the
-- supplied 'Bool' is 'True'
monadifyCompleteArgType :: SharedContext -> MonadifyEnv -> Term -> Bool ->
                           IO Term
monadifyCompleteArgType sc env tp poly_p =
  completeOpenTerm sc $
  if poly_p then
    -- Parameter polymorphism means pi-quantification over E and stack
    (piOpenTerm "E" (dataTypeOpenTerm "Prelude.EvType" []) $ \e ->
      piOpenTerm "stack" (globalOpenTerm "Prelude.FunStack") $ \st ->
      let ?specMParams = SpecMParams { specMEvType = e, specMStack = st } in
      -- NOTE: even though E and stack are free variables here, they are not
      -- free in tp, which is a closed term, so we do not list them in the
      -- MonadifyTypeCtx argument of monadifyTypeArgType
      monadifyTypeArgType [] tp)
  else
    let ?specMParams = monEnvParams env in monadifyTypeArgType [] tp

-- | Monadify a term of the specified type to a 'MonTerm' and then complete that
-- 'MonTerm' to a SAW core 'Term', or 'fail' if this is not possible
monadifyCompleteTerm :: SharedContext -> MonadifyEnv -> Term -> Term -> IO Term
monadifyCompleteTerm sc env trm tp =
  runCompleteMonadifyM sc env tp $ usingSpecMParams $
  monadifyTerm (Just $ monadifyType [] tp) trm

-- | Convert a name of a definition to the name of its monadified version
monadifyName :: NameInfo -> IO NameInfo
monadifyName (ModuleIdentifier ident) =
  return $ ModuleIdentifier $ mkIdent (identModule ident) $
  T.append (identBaseName ident) (T.pack "M")
monadifyName (ImportedName uri aliases) =
  do frag <- URI.mkFragment (T.pack "M")
     let aliases' = concatMap (\a -> [a, T.append a (T.pack "#M")]) aliases
     return $ ImportedName (uri { URI.uriFragment = Just frag }) aliases'

-- | The implementation of 'monadifyNamedTerm' in the @StateT MonadifyEnv IO@ monad
monadifyNamedTermH :: SharedContext -> NameInfo -> Maybe Term -> Term ->
                      StateT MonadifyEnv IO MonTerm
monadifyNamedTermH sc nmi maybe_trm tp =
  trace ("Monadifying " ++ T.unpack (toAbsoluteName nmi)) $
  get >>= \env -> let ?specMParams = monEnvParams env in
  do let mtp = monadifyType [] tp
     nmi' <- lift $ monadifyName nmi
     comp_tp <- lift $ completeOpenTerm sc $ toCompType mtp
     const_trm <-
       case maybe_trm of
         Just trm ->
          --  trace ("" ++ ppTermInMonCtx env trm ++ "\n\n") $
           do trm' <- monadifyTermInEnvH sc trm tp
              lift $ scConstant' sc nmi' trm' comp_tp
         Nothing -> lift $ scOpaqueConstant sc nmi' comp_tp
     return $ fromCompTerm mtp $ closedOpenTerm const_trm

-- | Monadify a 'Term' of the specified type with an optional body, bind the
-- result to a fresh SAW core constant generated from the supplied name, and
-- then convert that constant back to a 'MonTerm'. Like 'monadifyTermInEnv',
-- this function also monadifies all constants the body contains, and adds
-- the monadifications of those constants to the monadification environment.
monadifyNamedTerm :: SharedContext -> MonadifyEnv ->
                     NameInfo -> Maybe Term -> Term ->
                     IO (MonTerm, MonadifyEnv)
monadifyNamedTerm sc env nmi maybe_trm tp =
  flip runStateT env $ monadifyNamedTermH sc nmi maybe_trm tp

-- | The implementation of 'monadifyTermInEnv' in the @StateT MonadifyEnv IO@ monad
monadifyTermInEnvH :: SharedContext -> Term -> Term ->
                      StateT MonadifyEnv IO Term
monadifyTermInEnvH sc top_trm top_tp =
  do lift $ ensureCryptolMLoaded sc
     let const_infos =
           map snd $ Map.toAscList $ getConstantSet top_trm
     forM_ const_infos $ \(nmi,tp,maybe_body) ->
       get >>= \env ->
       if isPreludeName nmi ||
          Map.member nmi (monEnvMonTable env) then return () else
         do mtrm <- monadifyNamedTermH sc nmi maybe_body tp
            modify $ monEnvAdd nmi (monMacro0 mtrm)
     env <- get
     lift $ monadifyCompleteTerm sc env top_trm top_tp
  where preludeModules = mkModuleName <$> [["Prelude"], ["Cryptol"]]
        isPreludeName = \case
          ModuleIdentifier ident -> identModule ident `elem` preludeModules
          _ -> False

-- | Monadify a term with the specified type along with all constants it
-- contains, adding the monadifications of those constants to the monadification
-- environment
monadifyTermInEnv :: SharedContext -> MonadifyEnv ->
                     Term -> Term -> IO (Term, MonadifyEnv)
monadifyTermInEnv sc top_env top_trm top_tp =
  flip runStateT top_env $ monadifyTermInEnvH sc top_trm top_tp

-- | The implementation of 'monadifyCryptolModule' in the @StateT MonadifyEnv IO@ monad
monadifyCryptolModuleH :: SharedContext -> Env -> CryptolModule ->
                          StateT MonadifyEnv IO CryptolModule
monadifyCryptolModuleH sc cry_env (CryptolModule tysyns top_tts) =
  fmap (CryptolModule tysyns) $ flip mapM top_tts $ \top_tt ->
    do let top_tm = ttTerm top_tt
       top_tp <- lift $ ttTypeAsTerm sc cry_env top_tt
       tm <- monadifyTermInEnvH sc top_tm top_tp
       tm' <- lift $ mkTypedTerm sc tm
       return tm'

-- | Monadify each term in the given 'CryptolModule' along with all constants each
-- contains, returning a new module which each term monadified, and adding the
-- monadifications of all encountered constants to the monadification environment
monadifyCryptolModule :: SharedContext -> Env -> MonadifyEnv ->
                         CryptolModule -> IO (CryptolModule, MonadifyEnv)
monadifyCryptolModule sc cry_env top_env cry_mod =
  flip runStateT top_env $ monadifyCryptolModuleH sc cry_env cry_mod
