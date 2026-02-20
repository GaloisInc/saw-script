{- |
Given a constant of type `T`, construct an uninterpreted
constant with that type.  The type `T` is *not* limited to What4 BaseTypes or
FirstOrderTypes, and we support polymorphic and function types.
Note that this is used for both uninterpreted functions and when we create
symbolic variables.

The Algorithm for Uninterpreted Functions
=========================================

Our strategy is to generate a separate uninterpreted function for each
base type that is mentioned in the result of the original uninterpreted
function.  If we need more than one value of a type, then we return an
*array* of values, and the actual results of the original function are
obtained by selecting elements of this array.

For example, consider a function `f: [16] -> ([4][8],Bool)`.
A call `f x` will be translated like this:

  f_bv8:  [16] -> Array [2] [8]   // Uninterpreted
  f_bool: [16] -> Bool            // Uninterpreted
  w8s   = f_bv8 x                 // This has some auto-generated name
  bools = f_bool x                // This has some auto-generated name

Value for `f x`:
  ([ w8s ! 0, w8s ! 1, w8s ! 2, w8s ! 3 ], bools)

The reason we do this is to reduce the size of terms in examples like this:

  g: [1024][8] -> [1024][8]

`g` becomes a function of 1024 [8] arguments.  With the naive translation
we'd end up with:

  g_0 a0 .. a1023
  g_1 a0 .. a1023
  ..
  g_1023 a0 .. a1023

Note that this has 1024 * 1024 terms.  With the array translation, we
should end up with:

  arr = g_u8 a0 .. a0123
  el0 = arr @ 0
  el1 = arr @ 1
  ..
  el1023 = arr @ 1023

This is of size 1024 + 1024, which is much smaller.


Handling Functions and Polymorphism (UnintApp, SymFnCache)
==========================================================

When working with a function type (`Pi`), we don't generate uninterpreted
functions immediately.  Instead, we generate a Haskell function that collects
the arguments and only generates the uninterpreted function when they are
all available (see `VFun`) (i.e., the first time the uninterpreted function
is called).   Once the functions are generated they are stored in a cache
(see `SymFnCache`), so that future calls to the same function do not generate
new uninterpreted symbols, but reuse the old ones.  This is not an optimization,
but is crucial for the correct behavior of the algorithm.

The `UnintApp` type is used to collect the arguments to a function, and also
compute the root name for the function.   For ordinary (non-dependent)
function applications we just collect the arguments in the `UnintApp`.  However,
for dependent applications (e.g., to handle a size polymorphic function),
we instead modify the root name of the function.  This means that different
size instantiations of the functions end up with different uninterpreted
function instances.   Here's an example:

sum : {n} (fin n) => [n][8] -> [8]
xs: [16][8]
ys: [32][8]

`sum xs` will result in something like this:

sum_16_bv8: [8] -> [8] ..  [8] -> [8]     /* Has 16 arguments */
sum_16_bv8 (xs @ 0) (xs @ 1) .. (xs @ 15)

otoh, `sum ys` will result in something like this:
sum_32_bv8: [8] -> [8] ..  [8] -> [8]     /* Has 32 arguments */
sum_32_bv8 (ys @ 0) (ys @ 1) .. (ys @ 31)

See `applyUnintApp` for the full details.


Reinterpreting Terms Back Back to SAW Core (ArgTerm)
====================================================

Also we have two cases to consider:
  1. When translating to the solver (`parseUninterpreted`)
  2. When doing symbolic simulation for SAW (`parseUninterpretedSAW`).

The difference between the two is that in case (2) we need to also be able
to go back from the symbolic expressions to a semantically equivalent SAW
Core term.  To do this, we need to provide interpretations for all the functions
that were left as uninterpreted during the original translation.  For example,
we'd need to register the following interpretations for the examples above:

f_bv8 x = [ tup1 @ 0, tup1 @ 1, tup1 @ 2, tup1 @ 3 ]
  where tup1 = (f x).0

f_bool x = (f x).1

g_u8 x0 x1 .. x1023 = [ fx @ 0, fx @ f1, ... fx @ 1023 ]
  where fx = f [ x0, x1 .., x1023 ]

Note 1: the sharing in this examples (the `where` clause) happens
automatically due to sharing inherent in SAW Core terms.

Note 2: we also need to reconstruct the arguments to the original functions
from their components before calling (e.g., as in `g_u8`).

We use the type `ArgTerm` to help us create the interpretation.  The
constructors in `ArgTerm` are used to reassemble the arguments to the original
function out of their pieces (e.g., put together the 1024 parameters into
a single vector), while the selectors are used to connect a part of the
result of the original function, to the relevant uninterpreted bit.

Note 3: Since this code is used for making symbolic variables as well as
uninterpreted functions, there's a special case for terms that started as
SAW Core *variables* rather than SAW Core *constant*, and don't have any
arguments---these use `bindSAWTerm` instead of `sawRegisterSymFunInterp`.
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
module SAWCoreWhat4.Uninterp (
  parseUninterpreted,
  parseUninterpretedSAW,
  mkUnintApp,
  SymFnCache
) where


import Data.Bits
import Data.IORef
import Data.List (intercalate)
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Vector as V
import qualified Data.BitVector.Sized as BV

import Data.Traversable as T
import Control.Monad ((<=<), foldM, unless)
import Control.Monad.State as ST (MonadState(..), evalStateT, get, put, StateT(..), lift)
import Numeric.Natural (Natural)

-- saw-core
import SAWCore.SharedTerm
import SAWCore.Simulator.Value
import SAWCore.Module (ResolvedName(..), ctorName, dtCtors, lookupVarIndexInMap)
import SAWCore.Term.Functor (FieldName)

-- what4
import qualified What4.Expr.Builder as B
import           What4.Interface(SymExpr,SymFnWrapper(..),IsSymExprBuilder)
import qualified What4.Interface as W
import           What4.BaseTypes
import           What4.SFloat (SFloat(..))
import           What4.SWord (SWord(..))

-- parameterized-utils
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.Map (MapF)
import qualified Data.Parameterized.Map as MapF
import Data.Parameterized.Context (Assignment)
import Data.Parameterized.Some

-- saw-core
import SAWCore.Name (toAbsoluteName, toQualName)

-- saw-core-what4
import SAWCoreWhat4.Common
import SAWCoreWhat4.PosNat
import SAWCoreWhat4.Panic
import SAWCoreWhat4.ReturnTrip


-- | Uninterpreted function results for each base type.
type UnintState sym = MapF BaseTypeRepr (Arr sym)

-- | Uninterpreted function results for a particular base type.
-- The length of the lists should match the @UnintCount tc@ for the type.
data Arr sym tc = forall args res. Arr {
  arrFn :: W.SymFn sym args res,
  -- ^ The uninterpreted function name.

  arrIndexWidth :: !Natural,
  -- ^ How many bits to use for the array index.

  arrSymExprs  :: [SymExpr sym tc],
  -- ^ Available symbolic expressions

  arrFromSym   :: [ArgTerm]
  -- ^ How to map `n`-th symbolic expression back into a SAW Core term.
  -- Note that these are in reverse order---every time we take a thing
  -- from `arrSymExprs`, we cons a new thing onto here.
}

-- | Indicates if we need to map What4 terms back to SAW.
data ReturnTrip sym =
    NoReturnTrip sym
    -- ^ No need to reinterpret terms back into SAW Core.

  | forall n st fs. (sym ~ B.ExprBuilder n st fs ) =>
    DoReturnTrip sym Bool (SAWCoreState n) SharedContext ArgTerm
    -- ^ We should reinterpret terms back into SAW Core.
    -- The boolean flag indicates that this is a symbolic variable
    -- (instead of constant), which has special handling without arguments.

withSym :: IsSymExprBuilder sym => ReturnTrip sym -> (sym -> a) -> a
withSym xs k =
  case xs of
    NoReturnTrip sym -> k sym
    DoReturnTrip sym _ _ _ _ -> k sym

mapArgTerm :: (ArgTerm -> ArgTerm) -> ReturnTrip sym -> ReturnTrip sym
mapArgTerm f saw =
  case saw of
    NoReturnTrip sym -> NoReturnTrip sym
    DoReturnTrip sym isVar st sc t -> DoReturnTrip sym isVar st sc (f t)



-- | Generate a call to an uninterpreted function, without reinterpreting
-- back into SAW Core.
parseUninterpreted ::
  forall sym.
  (IsSymExprBuilder sym) =>
  sym                         {- ^ How to make symbolic expressions -} ->
  IORef (SymFnCache sym)      {- ^ Cache of known uninterpreted functions -} ->
  UnintApp (SymExpr sym)      {- ^ Name of function and its arguments -} ->
  TValue (What4 sym)          {- ^ Type of the function's result -} ->
  IO (SValue sym)             {- ^ The symbolic value for the call to the uninterpreted function -}
parseUninterpreted sym a b c = parseUninterpretedTop (NoReturnTrip sym) a b c

-- | Generate a call to an uninterpreted function, and also register mapping
-- back into SAW Core.
parseUninterpretedSAW ::
  forall n st fs.
  B.ExprBuilder n st fs     {- ^ How to make symbolic expressions -} ->
  SAWCoreState n            {- ^ Register interpretations for terms here -} ->
  SharedContext             {- ^ Use this to build SAW Core terms -} ->
  IORef (SymFnCache (B.ExprBuilder n st fs)) {- ^ Cache of known uninterpreted functions -} ->
  Bool                      {- ^ Is the original term a variable (True), or constant (False) -} ->
  Term                      {- ^ Original term -} ->
  UnintApp (SymExpr (B.ExprBuilder n st fs)) {- ^ Type of the function's result -} ->
  TValue (What4 (B.ExprBuilder n st fs)) {- ^ Type of the function's result. -} ->
  IO (SValue (B.ExprBuilder n st fs))
parseUninterpretedSAW sym st sc ref isVar term app t =
  parseUninterpretedTop (DoReturnTrip sym isVar st sc (ArgTermConst term)) ref app t

parseUninterpretedTop ::
  forall sym.
  (IsSymExprBuilder sym) =>
  ReturnTrip sym ->
  IORef (SymFnCache sym)      {- ^ Cache of known uninterpreted functions -} ->
  UnintApp (SymExpr sym)      {- ^ Name of function and its arguments -} ->
  TValue (What4 sym)          {- ^ Type of the function's result -} ->
  IO (SValue sym)             {- ^ The symbolic value for the call to the uninterpreted function -}

-- This case deals with symbolic variable with no parameters.  The round
-- trip for these works differently (see `mkUninterpreted`),
-- and since they have no arguments, we don't need to do the array caching.
parseUninterpretedTop rt@(DoReturnTrip _ True _ _ _) ref app@(UnintApp _ _ argTys) ty =
  case testEquality Ctx.empty argTys of
    Just Refl -> evalStateT (parseUninterpreted' rt ref app ty) MapF.empty
    Nothing   -> fail "At present, we do not support symbolic variables with parameters"

parseUninterpretedTop saw ref app ty =
  do
    count <-
      withSym saw (\sym ->
      MapF.traverseWithKey (mkUnint sym ref app) (countUninterpreted 1 MapF.empty ty))
    (val,st) <- runStateT (parseUninterpreted' saw ref app ty) count
    case saw of
      NoReturnTrip _ -> pure ()
      DoReturnTrip sym _ sawSt sc _ -> MapF.traverseWithKey_ register st
        where
        register :: BaseTypeRepr t -> Arr sym t -> IO ()
        register k (Arr fn ixW _ vs) =
          do
            elTy <- baseSCType sym sc k
            sawRegisterSymFunInterp sawSt fn $ \sc' ts ->
              do
                terms <- mapM (\ate -> reconstructArgTerm ate sc' ts) (reverse vs)
                case terms of
                  [t] -> pure (UninterpOne t)
                  _   -> pure (UninterpMany ixW elTy (V.fromList terms))

    pure val


-- | Track how many uninterpreted results we need for each base type.
newtype UnintCount (tc :: BaseType) = UnintCount Natural

-- | Count how many uninterpreted symbols we need to represent a value
-- of the given type.  Note that this function should match exactly what
-- is needed by `parseUninterpreted'`.
countUninterpreted ::
  IsSymExprBuilder sym =>
  Natural -> MapF BaseTypeRepr UnintCount -> TValue (What4 sym) -> MapF BaseTypeRepr UnintCount
countUninterpreted scale count ty =
  case ty of
    VPiType {}      -> count
    VBoolType       -> add BaseBoolRepr count
    VIntType        -> add BaseIntegerRepr count
    VIntModType {}  -> add BaseIntegerRepr count
    VRationalType   -> add BaseIntegerRepr (add BaseIntegerRepr count)
    VFloatType e p  ->
      case (someNat e, someNat p) of
        (Just (Some e'), Just (Some p'))
          | Just LeqProof <- testLeq (knownNat @2) e'
          , Just LeqProof <- testLeq (knownNat @2) p' ->
             add (BaseFloatRepr (FloatingPointPrecisionRepr e' p')) count
        _ -> count
    VVecType n VBoolType ->
      case somePosNat n of
        Just (Some (PosNat w)) -> add (BaseBVRepr w) count
        _                      -> count

    VVecType n et ->
      if n == 0 then count else countUninterpreted (n * scale) count et

    VArrayType ity ety
      | Just (Some idx_repr) <- valueAsBaseType ity
      , Just (Some elm_repr) <- valueAsBaseType ety
      -> add (BaseArrayRepr (Ctx.Empty Ctx.:> idx_repr) elm_repr) count

    VDataType (ModuleIdentifier "Prelude.UnitType") [] [] -> count

    VDataType (ModuleIdentifier "Prelude.PairType") [TValue ty1, TValue ty2] [] ->
      countUninterpreted scale (countUninterpreted scale count ty1) ty2

    VDataType (ModuleIdentifier "Prelude.RecordType")
      [VString _fname, TValue ty1, TValue ty2] [] ->
      countUninterpreted scale (countUninterpreted scale count ty1) ty2

    _ -> count
  where
  add ::
    BaseTypeRepr tc ->
    MapF BaseTypeRepr UnintCount ->
    MapF BaseTypeRepr UnintCount
  add bt =
    MapF.insertWith
      (\(UnintCount x) (UnintCount y) -> UnintCount (x + y))
      bt (UnintCount scale)





-- | Generate the uninterpreted functions.
mkUnint ::
  forall sym tc.
  (IsSymExprBuilder sym) =>
  sym                         {- ^ How to make symbolic expressions -} ->
  IORef (SymFnCache sym)      {- ^ Cache of known uninterpreted functions -} ->
  UnintApp (SymExpr sym)      {- ^ Name of function and its arguments -} ->
  BaseTypeRepr tc             {- ^ Type of value -} ->
  UnintCount tc               {- ^ How many values we need -} ->
  IO (Arr sym tc)
mkUnint sym ref (UnintApp nm args tys) ret (UnintCount tot)
  | let lim = tot - 1
  , let wn = width lim
  , Just (Some w) <- someNat wn =
    case isZeroOrGT1 w of

      -- We need only a single symbolic value (i.e., 0-bit index)
      Left Refl ->
        do
          fn <- mkSymFn sym ref (nm ++ suff ret) tys ret
          el <- W.applySymFn sym fn args
          pure (Arr { arrFn = fn, arrIndexWidth = wn, arrSymExprs = [el], arrFromSym = [] })

      -- We need multiple symbolic values of this type, result is array
      Right LeqProof ->
        do
          fn <- mkSymFn sym ref (nm ++ suff ret) tys (BaseArrayRepr (Ctx.singleton (BaseBVRepr w)) ret)
          arr <- W.applySymFn sym fn args
          els <- forM [ 0 .. lim ] $ \i ->
            do
              ind <- W.bvLit sym w (BV.mkBV w (fromIntegral i))
              W.arrayLookup sym arr (Ctx.singleton ind)
          pure (Arr { arrFn = fn, arrIndexWidth = wn, arrSymExprs = els, arrFromSym = [] })

  | otherwise =
    panic "parseUninterpreted" ["`someNat` returned `Nothing` for `Natural`"]

  where
  -- | Compute the number of bits required to represent the given integer,
  -- used to index the array of uninterpreted values.
  width :: Natural -> Natural
  width x = go 0 x
    where
    go s 0 = s
    go s n = let s' = s + 1 in s' `seq` go s' (n `shiftR` 1)

  -- Type suffixes for uninterpreted functions of each base type.
  suff :: BaseTypeRepr a -> String
  suff t =
    case t of
      BaseBoolRepr -> "_bool"
      BaseIntegerRepr -> "_int"
      BaseRealRepr -> "_real"
      BaseComplexRepr -> "_complex"
      BaseBVRepr w -> "_bv" ++ show w
      BaseFloatRepr (FloatingPointPrecisionRepr x y) -> "_float_" ++ show x ++ "_" ++ show y
      BaseStringRepr w -> "_str" ++ strw
        where strw = case w of
                       Char8Repr -> "8"
                       Char16Repr -> "16"
                       UnicodeRepr -> "U"
      BaseArrayRepr i e -> "_fun" ++ suff_asgn i ++ "_to" ++ suff e
      BaseStructRepr flds -> "_struct" ++ suff_asgn flds ++ "_end"

  suff_asgn i = intercalate "_and" (V.toList (Ctx.toVector i suff))



parseUninterpreted' ::
  forall sym.
  (IsSymExprBuilder sym) =>
  ReturnTrip sym ->
  IORef (SymFnCache sym) ->
  UnintApp (SymExpr sym) ->
  TValue (What4 sym) ->
  StateT (UnintState sym) IO (SValue sym)
parseUninterpreted' saw ref app ty =
  case ty of
    VPiType t1 body ->
      pure $ VFun $ \x ->
        do
          x'   <- force x
          app' <- withSym saw (\sym -> applyUnintApp sym app x')
          t2   <- applyPiBody body (ready x')

          saw' <-
            case saw of
              NoReturnTrip sym -> pure (NoReturnTrip sym)
              DoReturnTrip sym isVar st sc trm ->
                do newArg <- mkArgTerm sc t1 x'
                   let newTerm = ArgTermApply trm newArg
                   pure (DoReturnTrip sym isVar st sc newTerm)

          parseUninterpretedTop saw' ref app' t2

    VBoolType
      -> VBool <$> mkUninterpreted BaseBoolRepr saw

    VIntType
      -> VInt <$> mkUninterpreted BaseIntegerRepr saw

    VIntModType n
      -> VIntMod n <$> mkUninterpreted BaseIntegerRepr (mapArgTerm (ArgTermFromIntMod n) saw)

    VRationalType ->
      do
        -- See:
        -- https://github.com/GaloisInc/saw-script/issues/3206
        -- https://github.com/GaloisInc/what4/issues/364
        -- Note that the `bad` would only matter if we use a rational in the
        -- result of an uninterpreted function, and we need to import the
        -- resulting What4 term back into What4
        let bad = ArgTermErr ("Rationals in the results of uninterpreted functions are unsupported")
        numer <- mkUninterpreted BaseIntegerRepr (mapArgTerm (\_ -> bad) saw)
        -- TODO(#2433): Assert that the denominator is non-zero.
        denom <- mkUninterpreted BaseIntegerRepr (mapArgTerm (\_ -> bad) saw)
        pure $ VRational numer denom

    VFloatType e p
      | Just (Some e') <- someNat e
      , Just (Some p') <- someNat p
      , Just LeqProof <- testLeq (knownNat @2) e'
      , Just LeqProof <- testLeq (knownNat @2) p'
      -> (VFloat . SFloat) <$>
           mkUninterpreted (BaseFloatRepr (FloatingPointPrecisionRepr e' p')) saw

    VVecType n VBoolType ->
      case somePosNat n of
        Just (Some (PosNat w)) -> VWord . DBV <$> mkUninterpreted (BaseBVRepr w) saw
        _                      -> pure (VWord ZBV)

    VVecType n et ->
      VVector <$>
      case saw of
        NoReturnTrip _ -> V.replicateM (fromIntegral n) (ready <$> parseUninterpreted' saw ref app et)
        DoReturnTrip sym isVar st sc arg ->
          do
            elTy <- lift (termOfTValue sc et)
            V.generateM (fromIntegral n) (\i ->
              do
                let newArg = ArgTermAt n elTy arg (fromIntegral i)
                el <- parseUninterpreted' (DoReturnTrip sym isVar st sc newArg) ref app et
                pure (ready el)
              )

    VArrayType ity ety
      | Just (Some idx_repr) <- valueAsBaseType ity
      , Just (Some elm_repr) <- valueAsBaseType ety
      -> (VArray . SArray) <$>
          mkUninterpreted (BaseArrayRepr (Ctx.Empty Ctx.:> idx_repr) elm_repr) saw

    VDataType (ModuleIdentifier "Prelude.UnitType") [] []
      -> pure vUnit

    VDataType (ModuleIdentifier "Prelude.PairType") [TValue ty1, TValue ty2] []
      -> do x1 <- parseUninterpreted' (mapArgTerm ArgTermPairLeft saw) ref app ty1
            x2 <- parseUninterpreted' (mapArgTerm ArgTermPairRight saw) ref app ty2
            pure (vPair (ready x1) (ready x2))

    VDataType (ModuleIdentifier "Prelude.EmptyType") [] []
      -> pure vEmptyRecord
    VDataType (ModuleIdentifier "Prelude.RecordType")
      [VString fname, TValue ty1, TValue ty2] []
      -> do x1 <- parseUninterpreted' (mapArgTerm (`ArgTermRecordSelect` fname) saw) ref app ty1
            x2 <- parseUninterpreted' saw ref app ty2
            pure (vRecordValue (ready x1) (ready x2))

    _ -> fail $ "could not create uninterpreted symbol of type " ++ show ty
  where

  -- Get the next symbolic term of this type, and also record its interpretation
  -- back into SAW Core (if we need to do so).
  mkUninterpreted :: BaseTypeRepr t -> ReturnTrip sym -> StateT (UnintState sym) IO (SymExpr sym t)
  mkUninterpreted tyr argTerm =
    do
      mp <- get
      case MapF.lookup tyr mp of

        -- This happens when we are translating a symbolic variable with
        -- no arguments (see `parseUninterpretedTop`, first case)
        Nothing
          | DoReturnTrip sym True st sc arg <- saw ->
            lift (bindSAWTerm sym st tyr =<< reconstructArgTerm arg sc [])

        Just (Arr fn w (x : xs) atms) ->
          do
            let newTerm =
                  case argTerm of
                    NoReturnTrip _     -> []
                    DoReturnTrip _ _ _ _ t -> t : atms
            put (MapF.insert tyr (Arr fn w xs newTerm) mp)
            pure x

        _ -> panic "mkUninterpreted" ["Not enough uninterpreted results"]



--------------------------------------------------------------------------------
-- Symbolic function and its arguments.

-- | A value of type @UnintApp f@ represents an uninterpreted function
-- with the given 'String' name, applied to a list of argument values
-- paired with a representation of their types. The context of
-- argument types is existentially quantified.
data UnintApp f =
  forall args. UnintApp String (Assignment f args) (Assignment BaseTypeRepr args)

-- | Extract the string from an 'UnintApp'.
stringOfUnintApp :: UnintApp f -> String
stringOfUnintApp (UnintApp s _ _) = s

-- | Make an 'UnintApp' with the given name and no arguments.
mkUnintApp :: String -> UnintApp f
mkUnintApp nm = UnintApp nm Ctx.empty Ctx.empty

-- | Add a suffix to the function name of an 'UnintApp'.  This is used
-- to modify the function name for different polymorphic instantiations,
-- for example.
suffixUnintApp :: String -> UnintApp f -> UnintApp f
suffixUnintApp s (UnintApp nm args tys) = UnintApp (nm ++ s) args tys

-- | Extend an 'UnintApp' with an additional argument.
extendUnintApp :: UnintApp f -> f ty -> BaseTypeRepr ty -> UnintApp f
extendUnintApp (UnintApp nm xs tys) x ty =
  UnintApp nm (Ctx.extend xs x) (Ctx.extend tys ty)

-- | Flatten an 'SValue' to a sequence of components, each of which is
-- a symbolic value of a base type (e.g. word or boolean), and add
-- them to the list of arguments of the given 'UnintApp'. If the
-- 'SValue' contains any values built from data constructors, then
-- encode them as suffixes on the function name of the 'UnintApp'.
applyUnintApp ::
  forall sym.
  (W.IsExprBuilder sym) =>
  sym ->
  UnintApp (SymExpr sym) ->
  SValue sym ->
  IO (UnintApp (SymExpr sym))
applyUnintApp sym app0 v =
  case v of
    VVector xv                -> foldM (applyUnintApp sym) app0 =<< traverse force xv
    VBool sb                  -> return (extendUnintApp app0 sb BaseBoolRepr)
    VInt si                   -> return (extendUnintApp app0 si BaseIntegerRepr)
    VIntMod 0 si              -> return (extendUnintApp app0 si BaseIntegerRepr)
    VIntMod n si              -> do n' <- W.intLit sym (toInteger n)
                                    si' <- W.intMod sym si n'
                                    return (extendUnintApp app0 si' BaseIntegerRepr)
    VRational numer denom     -> do app1 <- applyUnintApp sym app0 (VInt numer)
                                    app2 <- applyUnintApp sym app1 (VInt denom)
                                    pure app2
    VFloat (SFloat sf)        -> return (extendUnintApp app0 sf (W.exprType sf))
    VWord (DBV sw)            -> return (extendUnintApp app0 sw (W.exprType sw))
    VArray (SArray sa)        -> return (extendUnintApp app0 sa (W.exprType sa))
    VWord ZBV                 -> return app0
    VCtorApp 0 _ []           -> return app0
    VCtorApp 0 _ [x, y]       -> do app1 <- applyUnintApp sym app0 =<< force x
                                    app2 <- applyUnintApp sym app1 =<< force y
                                    return app2
    VCtorApp n _ xs           -> foldM (applyUnintApp sym) app' =<< traverse force xs
                                   where app' = suffixUnintApp ("_" ++ show n) app0
    VNat n                    -> return (suffixUnintApp ("_" ++ show n) app0)
    VBVToNat w v'             -> applyUnintApp sym app' v'
                                   where app' = suffixUnintApp ("_" ++ show w) app0
    TValue (suffixTValue -> Just s)
                              -> return (suffixUnintApp s app0)
    VFun {} ->
      fail $
      "Cannot create uninterpreted higher-order function " ++
      show (stringOfUnintApp app0)
    _ ->
      fail $
      "Cannot create uninterpreted function " ++
      show (stringOfUnintApp app0) ++
      " with argument " ++ show v




--------------------------------------------------------------------------------
-- `ArgTerms` are used to remember the mappings between low-level symbolic
-- terms and SAW core terms.


-- | An 'ArgTerm' is a description of how to reassemble a saw-core
-- term from a list of the atomic components it is composed of.
data ArgTerm
  = ArgTermVar
  | ArgTermBVZero -- ^ scBvNat 0 0
  | ArgTermToIntMod Natural ArgTerm -- ^ toIntMod n x
  | ArgTermFromIntMod Natural ArgTerm -- ^ fromIntMod n x
  | ArgTermRational ArgTerm ArgTerm -- ^ numerator, denominator
  | ArgTermVector Term [ArgTerm] -- ^ element type, elements
  | ArgTermUnit
  | ArgTermPair ArgTerm ArgTerm
  | ArgTermEmpty
  | ArgTermRecord FieldName ArgTerm ArgTerm
  | ArgTermRecordSelect ArgTerm FieldName
  | ArgTermConst Term
  | ArgTermApply ArgTerm ArgTerm
  | ArgTermAt Natural Term ArgTerm Natural
    -- ^ length, element type, list, index
  | ArgTermPairLeft ArgTerm
  | ArgTermPairRight ArgTerm
  | ArgTermBVToNat Natural ArgTerm
  | ArgTermErr String
    deriving Show

-- | Reassemble a saw-core term from an 'ArgTerm' and a list of parts.
-- The length of the list should be equal to the number of
-- 'ArgTermVar' constructors in the 'ArgTerm'.
reconstructArgTerm :: ArgTerm -> SharedContext -> [Term] -> IO Term
reconstructArgTerm atrm sc ts =
  do (t, unused) <- parse atrm ts
     unless (null unused) $ fail "reconstructArgTerm: too many function arguments"
     return t
  where
    parse :: ArgTerm -> [Term] -> IO (Term, [Term])
    parse at ts0 =
      case at of
        ArgTermVar ->
          case ts0 of
            x : ts1 -> return (x, ts1)
            [] -> fail "reconstructArgTerm: too few function arguments"
        ArgTermBVZero ->
          do z <- scNat sc 0
             x <- scBvNat sc z z
             return (x, ts0)
        ArgTermToIntMod n at1 ->
          do n' <- scNat sc n
             (x1, ts1) <- parse at1 ts0
             x <- scToIntMod sc n' x1
             pure (x, ts1)
        ArgTermFromIntMod n at1 ->
          do n' <- scNat sc n
             (x1, ts1) <- parse at1 ts0
             x <- scFromIntMod sc n' x1
             pure (x, ts1)
        ArgTermRational numer denom ->
          do (numer', ts1) <- parse numer ts0
             (denom', ts2) <- parse denom ts1
             rat <- scRational sc numer' denom'
             pure (rat, ts2)
        ArgTermVector ty ats ->
          do (xs, ts1) <- parseList ats ts0
             x <- scVectorReduced sc ty xs
             return (x, ts1)
        ArgTermUnit ->
          do x <- scUnitValue sc
             return (x, ts0)
        ArgTermPair at1 at2 ->
          do (x1, ts1) <- parse at1 ts0
             (x2, ts2) <- parse at2 ts1
             x <- scPairValue sc x1 x2
             return (x, ts2)
        ArgTermEmpty ->
          do x <- scRecordValue sc []
             pure (x, ts0)
        ArgTermRecord fname at1 at2 ->
          do s <- scString sc fname
             (x1, ts1) <- parse at1 ts0
             (x2, ts2) <- parse at2 ts1
             ty1 <- scTypeOf sc x1
             ty2 <- scTypeOf sc x2
             x <- scGlobalApply sc "Prelude.RecordValue" [s, ty1, ty2, x1, x2]
             pure (x, ts2)
        ArgTermRecordSelect at1 fname ->
          do (x1, ts1) <- parse at1 ts0
             x <- scRecordSelect sc x1 fname
             pure (x, ts1)
        ArgTermConst x ->
          do return (x, ts0)
        ArgTermApply at1 at2 ->
          do (x1, ts1) <- parse at1 ts0
             (x2, ts2) <- parse at2 ts1
             x <- scApply sc x1 x2
             return (x, ts2)
        ArgTermAt n ty at1 i ->
          do n' <- scNat sc n
             (x1, ts1) <- parse at1 ts0
             i' <- scNat sc i
             x <- scAt sc n' ty x1 i'
             return (x, ts1)
        ArgTermPairLeft at1 ->
          do (x1, ts1) <- parse at1 ts0
             x <- scPairLeft sc x1
             return (x, ts1)
        ArgTermPairRight at1 ->
          do (x1, ts1) <- parse at1 ts0
             x <- scPairRight sc x1
             return (x, ts1)
        ArgTermBVToNat w at1 ->
          do (x1, ts1) <- parse at1 ts0
             x <- scBvToNat sc w x1
             pure (x, ts1)
        ArgTermErr msg -> fail msg

    parseList :: [ArgTerm] -> [Term] -> IO ([Term], [Term])
    parseList [] ts0 = return ([], ts0)
    parseList (at : ats) ts0 =
      do (x, ts1) <- parse at ts0
         (xs, ts2) <- parseList ats ts1
         return (x : xs, ts2)

-- | Given a type and value encoded as 'SValue's, construct an
-- 'ArgTerm' that builds a term of that type from local variables with
-- base types. The number of 'ArgTermVar' constructors should match
-- the number of arguments appended by 'applyUnintApp'.
mkArgTerm :: forall sym. SharedContext -> TValue (What4 sym) -> SValue sym -> IO ArgTerm
mkArgTerm sc ty val =
  case (ty, val) of
    (VBoolType, VBool _) -> return ArgTermVar
    (VIntType, VInt _)   -> return ArgTermVar
    (_, VWord ZBV)       -> return ArgTermBVZero     -- 0-width bitvector is a constant
    (_, VWord (DBV _))   -> return ArgTermVar
    (_, VFloat{})        -> return ArgTermVar
    (_, VArray{})        -> return ArgTermVar
    (VIntModType n, VIntMod _ _) -> pure (ArgTermToIntMod n ArgTermVar)
    (VRationalType, VRational numer denom) ->
      do numer' <- mkArgTerm @sym sc VIntType (VInt numer)
         denom' <- mkArgTerm @sym sc VIntType (VInt denom)
         pure (ArgTermRational numer' denom')

    (VVecType _ ety, VVector vv) ->
      do vs <- traverse force (V.toList vv)
         xs <- traverse (mkArgTerm sc ety) vs
         ety' <- termOfTValue sc ety
         return (ArgTermVector ety' xs)

    (VDataType (ModuleIdentifier "Prelude.UnitType") [] [],
     VCtorApp 0 _ [])
                         -> return ArgTermUnit
    (VDataType (ModuleIdentifier "Prelude.PairType") [TValue ty1, TValue ty2] [],
     VCtorApp 0 _ [v1, v2]) ->
      do x1 <- mkArgTerm sc ty1 =<< force v1
         x2 <- mkArgTerm sc ty2 =<< force v2
         return (ArgTermPair x1 x2)

    (VDataType (ModuleIdentifier "Prelude.EmptyType") [] [],
     VCtorApp 0 _ []) ->
      pure ArgTermEmpty
    (VDataType _nm [VString fname, TValue ty1, TValue ty2] [],
     VCtorApp 0 _ [v1, v2]) ->
      do x1 <- mkArgTerm sc ty1 =<< force v1
         x2 <- mkArgTerm sc ty2 =<< force v2
         pure (ArgTermRecord fname x1 x2)

    (VDataType nmi ps _, VCtorApp n _ vv) ->
      do mvi <- scResolveQualName sc (toQualName nmi)
         vi <-
           case mvi of
             Just vi -> pure vi
             Nothing -> panic "mkArgTerm" ["Data type name not found: " <> toAbsoluteName nmi]
         mm <- scGetModuleMap sc
         dt <-
           case lookupVarIndexInMap vi mm of
             Just (ResolvedDataType dt) -> pure dt
             _ -> panic "mkArgTerm" ["Data type not found: " <> toAbsoluteName nmi]
         let ctor = dtCtors dt !! n
         ps' <- traverse (termOfSValue sc) ps
         vv' <- traverse (termOfSValue sc <=< force) vv
         x   <- scConstApply sc (ctorName ctor) (ps' ++ vv')
         return (ArgTermConst x)

    (_, TValue tval) ->
      do x <- termOfTValue sc tval
         pure (ArgTermConst x)

    (_, VNat n) ->
      do x <- scNat sc n
         pure (ArgTermConst x)

    (_, VBVToNat w v) ->
      do let w' = fromIntegral w -- FIXME: make w :: Natural to avoid fromIntegral
         x <- mkArgTerm sc (VVecType w' VBoolType) v
         pure (ArgTermBVToNat w' x)

    _ -> fail $ "could not create uninterpreted function argument of type " ++ show ty



--------------------------------------------------------------------------------
-- Uninterpreted function cache

type SymFnCache sym =
  Map W.SolverSymbol (MapF (Assignment BaseTypeRepr) (SymFnWrapper sym))

lookupSymFn ::
  W.SolverSymbol -> Assignment BaseTypeRepr args -> BaseTypeRepr ty ->
  SymFnCache sym -> Maybe (W.SymFn sym args ty)
lookupSymFn s args ty cache =
  do m <- Map.lookup s cache
     SymFnWrapper fn <- MapF.lookup (Ctx.extend args ty) m
     return fn

insertSymFn ::
  W.SolverSymbol -> Assignment BaseTypeRepr args -> BaseTypeRepr ty ->
  W.SymFn sym args ty -> SymFnCache sym -> SymFnCache sym
insertSymFn s args ty fn = Map.alter upd s
  where
    upd Nothing = Just (MapF.singleton (Ctx.extend args ty) (SymFnWrapper fn))
    upd (Just m) = Just (MapF.insert (Ctx.extend args ty) (SymFnWrapper fn) m)

mkSymFn ::
  forall sym args ret. (IsSymExprBuilder sym) =>
  sym -> IORef (SymFnCache sym) ->
  String -> Assignment BaseTypeRepr args -> BaseTypeRepr ret ->
  IO (W.SymFn sym args ret)
mkSymFn sym ref nm args ret =
  do let s = W.safeSymbol nm
     cache <- readIORef ref
     case lookupSymFn s args ret cache of
       Just fn -> pure fn
       Nothing ->
         do fn <- W.freshTotalUninterpFn sym s args ret
            writeIORef ref (insertSymFn s args ret fn cache)
            pure fn
--------------------------------------------------------------------------------

