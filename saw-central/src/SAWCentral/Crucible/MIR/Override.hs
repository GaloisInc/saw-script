{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

-- | Override matching and application for MIR.
module SAWCentral.Crucible.MIR.Override
  ( OverrideMatcher
  , OverrideMatcher'(..)
  , runOverrideMatcher

  , setupValueSub
  , osAsserts
  , termSub

  , learnCond
  , matchArg
  , methodSpecHandler
  , decodeMIRVal
  ) where

import qualified Control.Applicative as Applicative
import qualified Control.Exception as X
import Control.Lens
import Control.Monad (filterM, forM, forM_, unless, zipWithM)
import Control.Monad.IO.Class (MonadIO(..))
import Control.Monad.Trans.Maybe (MaybeT(..))
import qualified Data.BitVector.Sized as BV
import Data.Either (partitionEithers)
import qualified Data.Text as Text
import qualified Data.Foldable as F
import qualified Data.Functor.Product as Functor
import qualified Data.IntMap as IntMap
import Data.IntMap (IntMap)
import Data.IORef (IORef, modifyIORef)
import Data.List (tails)
import qualified Data.List.NonEmpty as NE
import qualified Data.Map as Map
import Data.Maybe (catMaybes)
import qualified Data.Parameterized.Classes as PC
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.Some (Some(..))
import qualified Data.Parameterized.TraversableFC as FC
import Data.Proxy (Proxy(..))
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Vector as V
import Data.Void (absurd)
import qualified Prettyprinter as PP

import qualified Cryptol.TypeCheck.AST as Cryptol
import qualified Cryptol.Eval.Type as Cryptol (TValue(..), evalType)
import qualified Lang.Crucible.Backend as Crucible
import qualified Lang.Crucible.FunctionHandle as Crucible
import qualified Lang.Crucible.Simulator as Crucible
import qualified Lang.Crucible.Types as Crucible
import qualified Mir.DefId as Mir
import qualified Mir.FancyMuxTree as Mir
import qualified Mir.Generator as Mir
import qualified Mir.Intrinsics as Mir
import Mir.Intrinsics (MIR)
import qualified Mir.Mir as Mir
import qualified Mir.TransTy as Mir
import qualified What4.Expr as W4
import qualified What4.Interface as W4
import qualified What4.LabeledPred as W4
import qualified What4.Partial as W4
import qualified What4.ProgramLoc as W4

import SAWCore.SharedTerm
import SAWCoreWhat4.ReturnTrip (saw_ctx, toSC)
import CryptolSAWCore.TypedTerm

import SAWCentral.Crucible.Common
import qualified SAWCentral.Crucible.Common.MethodSpec as MS
import SAWCentral.Crucible.Common.MethodSpec (AllocIndex(..))
import qualified SAWCentral.Crucible.Common.Override as Ov (getSymInterface)
import SAWCentral.Crucible.Common.Override hiding (getSymInterface)
import SAWCentral.Crucible.MIR.MethodSpecIR
import SAWCentral.Crucible.MIR.ResolveSetupValue
import SAWCentral.Crucible.MIR.TypeShape
import SAWCentral.Options
import SAWCentral.Panic (panic)
import SAWCentral.Utils (bullets, handleException)

-- A few convenient synonyms
type SetupValue = MS.SetupValue MIR
type CrucibleMethodSpecIR = MS.CrucibleMethodSpecIR MIR
type StateSpec = MS.StateSpec MIR
type SetupCondition = MS.SetupCondition MIR

assertTermEqualities ::
  SharedContext ->
  MIRCrucibleContext ->
  OverrideMatcher MIR md ()
assertTermEqualities sc cc = do
  let sym = cc ^. mccSym
  let assertTermEquality (cond, t, md, e) = do
        p <- instantiateExtResolveSAWPred sc cc t
        p' <- liftIO $ W4.impliesPred sym cond p
        addAssert p' md e
  F.traverse_ assertTermEquality =<< OM (use termEqs)

-- | Assign the given reference value to the given allocation index in
-- the current substitution. If there is already a binding for this
-- index, then add a reference-equality constraint.
assignVar ::
  MIRCrucibleContext {- ^ context for interacting with Crucible -} ->
  MS.ConditionMetadata ->
  AllocIndex {- ^ variable index -} ->
  Some (MirPointer Sym) {- ^ concrete value -} ->
  OverrideMatcher MIR w ()

assignVar cc md var sref@(Some ref) =
  do old <- OM (setupValueSub . at var <<.= Just sref)
     let loc = MS.conditionLoc md
     F.for_ old $ \(Some ref') ->
       do p <- liftIO (equalRefsPred cc ref ref')
          addAssert p md (Crucible.SimError loc (Crucible.AssertFailureSimError "equality of aliased references" ""))

-- | When a specification is used as a composition override, this function
-- checks that the postconditions of the specification fully specify (via
-- @mir_points_to@ statements) the values of all local mutable allocations
-- (which are declared in the preconditions via @mir_alloc_mut@) and all
-- mutable static items. If not, this function will raise an appropriate error
-- message. See @Note [MIR compositional verification and mutable allocations]@.
checkMutableAllocPostconds ::
  Options ->
  SharedContext ->
  MIRCrucibleContext ->
  CrucibleMethodSpecIR ->
  OverrideMatcher MIR md ()
checkMutableAllocPostconds opts sc cc cs = do
  sub <- use setupValueSub

  -- Gather all of the references used in `mir_points_to` statements in the
  -- postconditions. This corresponds to step (1) of the plan in
  -- Note [MIR compositional verification and mutable allocations]
  postRefs <- Set.fromList <$>
    traverse
      (\(MirPointsTo _cond ref _val) -> do
        MIRVal refShp refVal <-
          resolveSetupValueMIR opts cc sc cs ref
        case testRefShape refShp of
          Just IsRefShape{} ->
            pure $ MirReferenceMuxConcrete refVal
          Nothing ->
            panic "checkMutableAllocPostconds" [
                "Unexpected non-reference type:",
                "   " <> Text.pack (show $ PP.pretty $ shapeMirTy refShp)
            ])
      (cs ^. MS.csPostState ^. MS.csPointsTos)

  -- Check if a `mir_alloc_mut`-computed allocation isn't used in a
  -- `mir_points_to` statement in the postconditions, and if so, error.
  -- This corresponds to step (2) of the plan in
  -- Note [MIR compositional verification and mutable allocations]
  let mutAllocSpecs =
        Map.filter (\(Some mas) -> view isMut mas) $
        cs ^. MS.csPreState . MS.csAllocs
  let mutAllocRefs =
        map
          (\(Some mp, Some spec) ->
            ( MirReferenceMuxConcrete $ mp ^. mpRef
            , spec ^. maConditionMetadata
            ))
          (Map.elems (Map.intersectionWith (,) sub mutAllocSpecs))
  F.for_ mutAllocRefs $ \(mutAllocRef, cond) ->
    unless (Set.member mutAllocRef postRefs) $
      fail $ underspecified_mut_alloc_err cond

  -- Check if a mutable static isn't used in a `mir_points_to` statement in the
  -- postconditions, and if so, error.
  -- This corresponds to step (3) of the plan in
  -- Note [MIR compositional verification and mutable allocations]
  let mutStatics =
        Map.filter (view Mir.sMutable) $
        col ^. Mir.statics
  let mutStaticRefs =
        map
        (\(mutStaticDid, (_, Mir.StaticVar gv)) ->
          ( mutStaticDid
          , MirReferenceMuxConcrete $ staticRefMux sym gv
          ))
        (Map.toList
          (Map.intersectionWith
            (,) mutStatics (colState ^. Mir.staticMap)))
  F.for_ mutStaticRefs $ \(mutStaticDid, mutStaticRef) ->
    unless (Set.member mutStaticRef postRefs) $
      fail $ underspecified_mut_static_err mutStaticDid
  where
    sym      = cc ^. mccSym
    colState = cc ^. mccRustModule . Mir.rmCS
    col      = colState ^. Mir.collection

    underspecified_mut_alloc_err ::
      MS.ConditionMetadata -> String
    underspecified_mut_alloc_err cond =
      concat
        [ "State of memory allocated in precondition (at "
        , show $ W4.plSourceLoc $ MS.conditionLoc cond
        , ") not described in postcondition"
        ]

    underspecified_mut_static_err ::
      Mir.DefId -> String
    underspecified_mut_static_err did =
      concat
        [ "State of mutable static variable \""
        , show did
        , "\" not described in postcondition"
        ]

-- | A newtype around 'Mir.MirReferenceMux' that allows comparing values that
-- are known to be fully concrete.
-- See @Note [MIR compositional verification and mutable allocations]@.
newtype MirReferenceMuxConcrete =
  MirReferenceMuxConcrete (Mir.MirReferenceMux Sym)

instance Eq MirReferenceMuxConcrete where
  x == y = compare x y == EQ

instance Ord MirReferenceMuxConcrete where
  compare (MirReferenceMuxConcrete x) (MirReferenceMuxConcrete y) =
    cmpRefMuxConcretely Proxy x y

-- | Compare two 'Mir.MirReferenceMux' values that are known to be concrete.
-- In particular, this assumes that the underlying 'Mir.FancyMuxTree' in each
-- value has exactly one leaf with a 'W4.Pred' that concretely evaluates to
-- 'W4.truePred'. If this is not the case, this function will panic.
-- See @Note [MIR compositional verification and mutable allocations]@.
cmpRefMuxConcretely ::
  forall sym proxy.
  Crucible.IsSymInterface sym =>
  proxy sym ->
  Mir.MirReferenceMux sym ->
  Mir.MirReferenceMux sym ->
  Ordering
cmpRefMuxConcretely sym (Mir.MirReferenceMux fmt1) (Mir.MirReferenceMux fmt2) =
  cmpRefConcretely sym
    (fancyMuxTreeConcrete fmt1) (fancyMuxTreeConcrete fmt2)
  where
    fancyMuxTreeConcrete :: Mir.FancyMuxTree sym a -> a
    fancyMuxTreeConcrete fmt =
      case Mir.viewFancyMuxTree fmt of
        [(x, p)] ->
          if Just True == W4.asConstantPred p
          then x
          else panic "cmpRefMuxConcretely" [
                   "FancyMuxTree leaf with symbolic predicate",
                   "   " <> Text.pack (show $ W4.printSymExpr p)
               ]
        [] ->
          panic "cmpRefMuxConcretely" ["FancyMuxTree with no leaves"]
        (_:_) ->
          panic "cmpRefMuxConcretely" ["FancyMuxTree with multiple leaves"]

-- | Compare two 'Mir.MirReference' values that are known to be concrete.
-- See @Note [MIR compositional verification and mutable allocations]@.
cmpRefConcretely ::
  Crucible.IsSymInterface sym =>
  proxy sym ->
  Mir.MirReference sym ->
  Mir.MirReference sym ->
  Ordering
cmpRefConcretely sym (Mir.MirReference (tpr1 :: Crucible.TypeRepr tp1) r1 p1) (Mir.MirReference (tpr2 :: Crucible.TypeRepr tp2) r2 p2) =
  PC.toOrdering @tp1 @tp2 $
    PC.compareF tpr1 tpr2 <<>> cmpRootConcretely r1 r2 <<>> cmpPathConcretely sym p1 p2
cmpRefConcretely sym (Mir.MirReference_Integer i1) (Mir.MirReference_Integer i2) =
  PC.toOrdering @Mir.SizeBits @Mir.SizeBits $
    cmpSymBVConcretely sym i1 i2
cmpRefConcretely _ (Mir.MirReference _ _ _) (Mir.MirReference_Integer _) =
  LT
cmpRefConcretely _ (Mir.MirReference_Integer _) (Mir.MirReference _ _ _) =
  GT

-- | Compare two 'Mir.MirReferenceRoot' values that are known to be concrete.
-- Like the 'Mir.refRootEq' function, this will panic if it attempts to compare
-- 'Mir.GlobalVar_RefRoot' values, which should not be possible with the way
-- that SAW is currently set up.
-- See @Note [MIR compositional verification and mutable allocations]@.
cmpRootConcretely ::
  Mir.MirReferenceRoot sym tp1 ->
  Mir.MirReferenceRoot sym tp2 ->
  PC.OrderingF tp1 tp2

-- RefCell_RefRoot
cmpRootConcretely (Mir.RefCell_RefRoot rc1) (Mir.RefCell_RefRoot rc2) =
  PC.compareF rc1 rc2

cmpRootConcretely (Mir.RefCell_RefRoot _) _ = PC.LTF
cmpRootConcretely _ (Mir.RefCell_RefRoot _) = PC.GTF

-- GlobalVar_RefRoot
cmpRootConcretely (Mir.GlobalVar_RefRoot gv1) (Mir.GlobalVar_RefRoot gv2) =
  PC.compareF gv1 gv2
cmpRootConcretely (Mir.GlobalVar_RefRoot _) _ = PC.LTF
cmpRootConcretely _ (Mir.GlobalVar_RefRoot _) = PC.GTF

-- Const_RefRoot
cmpRootConcretely (Mir.Const_RefRoot _ _) (Mir.Const_RefRoot _ _) =
  panic "cmpRootConcretely" ["Cannot compare Const_RefRoots"]

-- | Compare two 'Mir.MirReferencePath' values that are known to be concete.
-- See @Note [MIR compositional verification and mutable allocations]@.
cmpPathConcretely ::
  Crucible.IsSymInterface sym =>
  proxy sym ->
  Mir.MirReferencePath sym tp tp1 ->
  Mir.MirReferencePath sym tp tp2 ->
  PC.OrderingF tp1 tp2

-- Empty_RefPath
cmpPathConcretely _ Mir.Empty_RefPath Mir.Empty_RefPath = PC.EQF
cmpPathConcretely _ Mir.Empty_RefPath _ = PC.LTF
cmpPathConcretely _ _ Mir.Empty_RefPath = PC.GTF

-- Field_RefPath
cmpPathConcretely sym (Mir.Field_RefPath ctx1 p1 idx1) (Mir.Field_RefPath ctx2 p2 idx2) =
  PC.compareF ctx1 ctx2 <<>>
  PC.compareF idx1 idx2 <<>>
  cmpPathConcretely sym p1 p2 <<>>
  PC.EQF
cmpPathConcretely _ (Mir.Field_RefPath _ _ _) _ = PC.LTF
cmpPathConcretely _ _ (Mir.Field_RefPath _ _ _) = PC.GTF

-- Variant_RefPath
cmpPathConcretely sym (Mir.Variant_RefPath discrTp1 ctx1 p1 idx1) (Mir.Variant_RefPath discrTp2 ctx2 p2 idx2) =
  PC.compareF discrTp1 discrTp2 <<>>
  PC.compareF ctx1 ctx2 <<>>
  PC.compareF idx1 idx2 <<>>
  cmpPathConcretely sym p1 p2 <<>>
  PC.EQF
cmpPathConcretely _ (Mir.Variant_RefPath _ _ _ _) _ = PC.LTF
cmpPathConcretely _ _ (Mir.Variant_RefPath _ _ _ _) = PC.GTF

-- Index_RefPath
cmpPathConcretely sym (Mir.Index_RefPath tpr1 p1 i1) (Mir.Index_RefPath tpr2 p2 i2) =
  PC.compareF tpr1 tpr2 <<>>
  cmpPathConcretely sym p1 p2 <<>>
  cmpSymBVConcretely sym i1 i2 <<>>
  PC.EQF
cmpPathConcretely _ (Mir.Index_RefPath _ _ _) _ = PC.LTF
cmpPathConcretely _ _ (Mir.Index_RefPath _ _ _) = PC.GTF

-- Just_RefPath
cmpPathConcretely sym (Mir.Just_RefPath tpr1 p1) (Mir.Just_RefPath tpr2 p2) =
  PC.compareF tpr1 tpr2 <<>>
  cmpPathConcretely sym p1 p2 <<>>
  PC.EQF
cmpPathConcretely _ (Mir.Just_RefPath _ _) _ = PC.LTF
cmpPathConcretely _ _ (Mir.Just_RefPath _ _) = PC.GTF

-- VectorAsMirVector_RefPath
cmpPathConcretely sym (Mir.VectorAsMirVector_RefPath tpr1 p1) (Mir.VectorAsMirVector_RefPath tpr2 p2) =
  PC.compareF tpr1 tpr2 <<>>
  cmpPathConcretely sym p1 p2 <<>>
  PC.EQF
cmpPathConcretely _ (Mir.VectorAsMirVector_RefPath _ _) _ = PC.LTF
cmpPathConcretely _ _ (Mir.VectorAsMirVector_RefPath _ _) = PC.GTF

-- ArrayAsMirVector_RefPath
cmpPathConcretely sym (Mir.ArrayAsMirVector_RefPath tpr1 p1) (Mir.ArrayAsMirVector_RefPath tpr2 p2) =
  PC.compareF tpr1 tpr2 <<>>
  cmpPathConcretely sym p1 p2 <<>>
  PC.EQF
cmpPathConcretely _ (Mir.ArrayAsMirVector_RefPath _ _) _ = PC.LTF
cmpPathConcretely _ _ (Mir.ArrayAsMirVector_RefPath _ _) = PC.GTF

-- AgElem_RefPath
cmpPathConcretely sym (Mir.AgElem_RefPath off1 sz1 tpr1 p1) (Mir.AgElem_RefPath off2 sz2 tpr2 p2) =
  PC.compareF off1 off2 <<>>
  PC.fromOrdering (compare sz1 sz2) <<>>
  PC.compareF tpr1 tpr2 <<>>
  cmpPathConcretely sym p1 p2 <<>>
  PC.EQF

-- | Compare two 'W4.SymBV' values that are known to be concrete. If they are
-- not concrete, this function will panic.
-- See @Note [MIR compositional verification and mutable allocations]@.
cmpSymBVConcretely ::
  Crucible.IsSymInterface sym =>
  proxy sym ->
  W4.SymBV sym w ->
  W4.SymBV sym w ->
  PC.OrderingF w w
cmpSymBVConcretely _ symBV1 symBV2
  | Just bv1 <- W4.asBV symBV1
  , Just bv2 <- W4.asBV symBV2
  = PC.fromOrdering $ compare bv1 bv2
  | otherwise
  = panic "cmpSymBVConcretely" [
        "SymBV not concrete",
        "symBV1: " <> Text.pack (show $ W4.printSymExpr symBV1),
        "symBV2: " <> Text.pack (show $ W4.printSymExpr symBV2)
    ]

-- | An infix version of 'PC.joinOrderingF' that is right associative, allowing
-- it to be chained together more easily. See
-- <https://github.com/GaloisInc/parameterized-utils/issues/157> for further
-- motivation.
infixr 6 <<>>
(<<>>) ::
  forall j k (a :: j) (b :: j) (c :: k) (d :: k).
  PC.OrderingF a b ->
  (a ~ b => PC.OrderingF c d) ->
  PC.OrderingF c d
(<<>>) = PC.joinOrderingF

{-
Note [MIR compositional verification and mutable allocations]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
When using compositional verification in the SAW MIR backend, we want to ensure
that any specifications that are used as compositional overrides properly
specify the values of local mutable allocations (i.e., things allocated with
mir_alloc_mut) and mutable static items (i.e., things declared with `static
mut`) in the postconditions of the specs. (See the "Compositional Verification"
section of the SAW manual for more discussion on why this is important.) This
is something that the SAW LLVM backend also must do, but the MIR backend
differs from how it accomplishes this in a number of key ways.

The main entrypoint to this check is the `checkMutableAllocPostconds` function,
which is roughly the MIR counterpart to the LLVM backend's
`SAWCentral.Crucible.LLVM.Override.invalidateMutableAllocs` function. The LLVM
function takes the approach of invalidating the underlying memory of
underspecified mutable allocations or global variables such that if they are
read from later, then a simulation-time error is thrown. The MIR memory model,
on the other hand, does not have a notion of memory invalidation that we can
readily use (see https://github.com/GaloisInc/crucible/issues/1109), so the SAW
MIR backend requires a slightly different approach.

The SAW MIR backend instead implements a stricter check: any specification used
as a compositional override *must* specify the values of all local mutable
allocations and the values of all mutable static items in the postconditions.
There are no exceptions to this rule: if you do not specify one, then SAW will
throw an error before simulation begins. This differs from the LLVM backend in
that you can get away with not specifying the value of a mutable allocation or
global variable in an overrides postconditions, provided that that value is
never read from during simulation.

In order to implement the necessary checks in the `checkMutableAllocPostconds`
function, we employ the following plan:

1. Compute all of the MirReferenceMux values corresponding to each
   mir_points_to statement in the postconditions of the compositional override
   and put them into a Set.

2. Gather all of the MirReferenceMux values corresponding to local mutable
   references that were allocated in the preconditions. If one of these
   values is not contained in the Set of things produced in step (1),
   then throw an error.

3. Gather all of the MirReferenceMux values corresponding to mutable static
   items that might be used in the program. If one of these values is not
   contained in the Set of things produced in step (1), then throw an error.

Using a Set turns this from an O(n) operation to an O(log n) one, which can be
important for specifications that have lots of mutable allocations or mutable
static items.

There is one wrinkle not mentioned in the plan above: how exactly do you put
MirReferenceMux values into a Set? Doing so would require MirReferenceMux to
have an Ord instance in order to use Set operations, and MirReferenceMux has no
such instance. Indeed, it's not clear how to define such an instance:
MirReferenceMux values can contain symbolic information in the general case,
which makes it tricky to return a definite True-or-False answer regarding
whether two values are equal.

Thankfully, it happens to be the case that all MirReferenceMux values that we
check in `checkMutableAllocPostconds` are concrete. Therefore, we can compare
MirReferenceMux values by concretizing the symbolic information whenever
necessary. The cmp*Concretely family of functions implements these concrete
comparisons. More precisely:

* The `cmpRefMuxConcretely` function checks that the FancyMuxTree in a
  MirReferenceMux consists of exactly one leaf with a Pred that concretely
  evaluates to truePred. (This must be the case if the FancyMuxTree is
  concrete.) The function then takes the MirReference values from the leaf
  of each FancyMuxTree and compares them using `cmpRefConcretely`.

* The `cmpRefConcretely` function is very close to the OrdSkel instance for
  MirReference, except that it concretizes SymBV values as necessary using
  the `cmpSymBVConcretely` function.

* We create a MirReferenceMuxConcrete newtype around MirReferenceMux, and
  we give MirReferenceMuxConcrete an Ord instance defined in terms of
  `cmpRefMuxConcretely`. We then put MirReferenceMuxConcrete values into
  the Set in step (1) of the plan above.

If there is symbolic information at any point in this process, then a panic is
thrown. If we ever add the ability to create symbolic MirReferenceMux values in
a specification (e.g., via a MIR equivalent of the llvm_fresh_pointer command),
then we will need to rethink this plan.
-}

computeReturnValue ::
  Options                     {- ^ saw script debug and print options     -} ->
  MIRCrucibleContext          {- ^ context of the crucible simulation     -} ->
  SharedContext               {- ^ context for generating saw terms       -} ->
  MS.CrucibleMethodSpecIR MIR {- ^ method specification                   -} ->
  Crucible.TypeRepr ret       {- ^ representation of function return type -} ->
  Maybe SetupValue            {- ^ optional symbolic return value         -} ->
  OverrideMatcher MIR md (Crucible.RegValue Sym ret)
                              {- ^ concrete return value                  -}
computeReturnValue opts cc sc spec ty mbVal =
  case mbVal of
    Nothing ->
      case ty of
        Crucible.UnitRepr -> return ()
        _ -> fail_
    Just val -> do
      MIRVal shp val' <- resolveSetupValueMIR opts cc sc spec val
      case W4.testEquality ty (shapeType shp) of
        Just Refl -> pure val'
        Nothing   -> fail_
  where
    fail_ = failure (spec ^. MS.csLoc) (BadReturnSpecification (Some ty))

decodeMIRVal :: Mir.Collection -> Mir.Ty -> Crucible.AnyValue Sym -> Maybe MIRVal
decodeMIRVal col ty (Crucible.AnyValue repr rv)
  | Some shp <- tyToShape col ty
  = case W4.testEquality repr (shapeType shp) of
      Just Refl -> Just (MIRVal shp rv)
      Nothing   -> Nothing

-- | Generate assertions that all of the memory allocations matched by
-- an override's precondition are disjoint.
enforceDisjointness ::
  MIRCrucibleContext -> W4.ProgramLoc -> StateSpec -> OverrideMatcher MIR w ()
enforceDisjointness cc loc ss =
  do let sym = cc^.mccSym
     sub <- OM (use setupValueSub)
     let mems = Map.elems $ Map.intersectionWith (,) (view MS.csAllocs ss) sub

     let md = MS.ConditionMetadata
              { MS.conditionLoc = loc
              , MS.conditionTags = mempty
              , MS.conditionType = "memory region disjointness"
              , MS.conditionContext = ""
              }
     -- Ensure that all regions are disjoint from each other.
     sequence_
        [ do c <- liftIO $ W4.notPred sym =<< equalRefsPred cc p q
             addAssert c md a

        | let a = Crucible.SimError loc $
                    Crucible.AssertFailureSimError "Memory regions not disjoint" ""
        , (_, Some p) : ps <- tails mems
        , (_, Some q)      <- ps
        ]

-- | Perform an allocation as indicated by a 'mir_alloc'
-- statement from the postcondition section.
executeAllocation ::
  Options ->
  MIRCrucibleContext ->
  (AllocIndex, Some MirAllocSpec) ->
  OverrideMatcher MIR w ()
executeAllocation opts cc (var, someAlloc@(Some alloc)) =
  do liftIO $ printOutLn opts Debug $ unwords ["executeAllocation:", show var, show alloc]
     globals <- OM (use overrideGlobals)
     (ptr, globals') <- liftIO $ doAlloc cc globals someAlloc
     OM (overrideGlobals .= globals')
     assignVar cc (alloc^.maConditionMetadata) var ptr

-- | Process a "points_to" statement from the postcondition section of
-- the CrucibleSetup block. First we compute the value indicated by
-- 'val', and then write it to the address indicated by 'ptr'.
executePointsTo ::
  Options ->
  SharedContext ->
  MIRCrucibleContext ->
  CrucibleMethodSpecIR ->
  MirPointsTo ->
  OverrideMatcher MIR w ()
executePointsTo _opts sc cc spec pt = do
  env <- OM (use setupValueSub)
  globals <- OM (use overrideGlobals)
  sub <- OM (use termSub)
  pt' <- liftIO $ instantiateMirPointsTo sc sub pt
  globals' <- liftIO $ doPointsTo spec cc env globals pt'
  OM (overrideGlobals .= globals')

-- execute a pre/post condition
executeCond ::
  Options ->
  SharedContext ->
  MIRCrucibleContext ->
  CrucibleMethodSpecIR ->
  StateSpec ->
  OverrideMatcher MIR RW ()
executeCond opts sc cc cs ss =
  do refreshTerms sc ss
     F.traverse_ (executeAllocation opts cc) (Map.assocs (ss ^. MS.csAllocs))
     checkMutableAllocPostconds opts sc cc cs
     F.traverse_ (executePointsTo opts sc cc cs) (ss ^. MS.csPointsTos)
     F.traverse_ (executeSetupCondition opts sc cc cs) (ss ^. MS.csConditions)

-- | Process a "mir_equal" statement from the postcondition
-- section of the CrucibleSetup block.
executeEqual ::
  Options                                          ->
  SharedContext                                    ->
  MIRCrucibleContext                               ->
  CrucibleMethodSpecIR                             ->
  MS.ConditionMetadata ->
  SetupValue       {- ^ first value to compare  -} ->
  SetupValue       {- ^ second value to compare -} ->
  OverrideMatcher MIR w ()
executeEqual opts sc cc spec md v1 v2 =
  do val1 <- resolveSetupValueMIR opts cc sc spec v1
     val2 <- resolveSetupValueMIR opts cc sc spec v2
     p <- liftIO (equalValsPred cc val1 val2)
     addAssume p md

-- | Process a "mir_postcond" statement from the postcondition
-- section of the CrucibleSetup block.
executePred ::
  SharedContext   ->
  MIRCrucibleContext ->
  MS.ConditionMetadata ->
  TypedTerm        {- ^ the term to assert as a postcondition -} ->
  OverrideMatcher MIR w ()
executePred sc cc md tt =
  do s <- OM (use termSub)
     t <- liftIO $ scInstantiateExt sc s (ttTerm tt)
     p <- liftIO $ resolveBoolTerm (cc ^. mccSym) t
     addAssume p md

-- | Update the simulator state based on the postconditions from the
-- procedure specification.
executeSetupCondition ::
  Options                    ->
  SharedContext              ->
  MIRCrucibleContext         ->
  CrucibleMethodSpecIR       ->
  SetupCondition             ->
  OverrideMatcher MIR RW ()
executeSetupCondition opts sc cc spec =
  \case
    MS.SetupCond_Equal md val1 val2 ->
      executeEqual opts sc cc spec md val1 val2
    MS.SetupCond_Pred md tm -> executePred sc cc md tm
    MS.SetupCond_Ghost md var val -> executeGhost sc md var val

handleSingleOverrideBranch :: forall rtp args ret.
  Options            {- ^ output/verbosity options                      -} ->
  SharedContext      {- ^ context for constructing SAW terms            -} ->
  MIRCrucibleContext {- ^ context for interacting with Crucible         -} ->
  W4.ProgramLoc      {- ^ Location of the call site for error reporting -} ->
  IORef MetadataMap ->
  Crucible.FnHandle args ret {- ^ the handle for this function -} ->
  OverrideWithPreconditions MIR ->
  Crucible.OverrideSim (SAWCruciblePersonality Sym) Sym MIR rtp args ret
     (Crucible.RegValue Sym ret)
handleSingleOverrideBranch opts sc cc call_loc mdMap h (OverrideWithPreconditions preconds cs st) =
  mccWithBackend cc $ \bak -> do
  let sym = backendGetSym bak
  let fnName = cs ^. MS.csMethod
  let retTy = Crucible.handleReturnType h

  liftIO $ printOutLn opts Info $ unwords
    [ "Found a single potential override for"
    , show fnName
    ]

  -- First assert the override preconditions
  liftIO $ forM_ preconds $ \(md,W4.LabeledPred p r) ->
    do (ann,p') <- W4.annotateTerm sym p
       let caller = unwords ["Override called from:", show (W4.plSourceLoc call_loc)]
       let md' = md{ MS.conditionContext = MS.conditionContext md ++ caller }
       modifyIORef mdMap (Map.insert ann md')
       Crucible.addAssertion bak (Crucible.LabeledPred p' r)

  g <- Crucible.readGlobals
  res <- liftIO $ runOverrideMatcher sym g
     (st^.setupValueSub)
     (st^.termSub)
     (st^.osFree)
     (st^.osLocation)
     (methodSpecHandler_poststate opts sc cc retTy cs)
  case res of
    Left (OF loc rsn)  ->
      -- TODO, better pretty printing for reasons
      liftIO
        $ Crucible.abortExecBecause
        $ Crucible.AssertionFailure
        $ Crucible.SimError loc
        $ Crucible.AssertFailureSimError "assumed false" (show rsn)
    Right (ret,st') ->
      do liftIO $ forM_ (st'^.osAssumes) $ \(_md,asum) ->
           Crucible.addAssumption bak
            $ Crucible.GenericAssumption (st^.osLocation) "override postcondition" asum
         Crucible.writeGlobals (st'^.overrideGlobals)
         Crucible.overrideReturn' (Crucible.RegEntry retTy ret)

handleOverrideBranches :: forall rtp args ret.
  Options            {- ^ output/verbosity options                      -} ->
  SharedContext      {- ^ context for constructing SAW terms            -} ->
  MIRCrucibleContext {- ^ context for interacting with Crucible         -} ->
  W4.ProgramLoc      {- ^ Location of the call site for error reporting -} ->
  NE.NonEmpty (MS.CrucibleMethodSpecIR MIR)
    {- ^ specification for current function override -} ->
  Crucible.FnHandle args ret {- ^ the handle for this function -} ->
  [OverrideWithPreconditions MIR] ->
  ([OverrideWithPreconditions MIR],[OverrideWithPreconditions MIR],[OverrideWithPreconditions MIR]) ->
  Crucible.OverrideSim (SAWCruciblePersonality Sym) Sym MIR rtp args ret
     (Crucible.RegValue Sym ret)

handleOverrideBranches opts sc cc call_loc css h branches (true, false, unknown) =
  mccWithBackend cc $ \bak -> do
  let sym = backendGetSym bak
  let fnName = show $ NE.head css ^. MS.csMethod
  Crucible.RegMap args <- Crucible.getOverrideArgs

  -- Collapse the preconditions to a single predicate
  branches' <- liftIO $ forM (true ++ unknown) $
    \(OverrideWithPreconditions preconds cs st) ->
      W4.andAllOf sym (folded . _2 . W4.labeledPred) preconds <&>
        \precond -> (precond, cs, st)

  -- Now use crucible's symbolic branching machinery to select between the branches.
  -- Essentially, we are doing an n-way if statement on the precondition predicates
  -- for each override, and selecting the first one whose preconditions hold.
  --
  -- Then, in the body of the branch, we run the poststate handler to update the
  -- memory state, compute return values and compute postcondition predicates.
  --
  -- For each override branch that doesn't fail outright, we assume the relevant
  -- postconditions, update the crucible global variable state, and return the
  -- computed return value.
  --
  -- We add a final default branch that simply fails unless some previous override
  -- branch has already succeeded.
  liftIO $ printOutLn opts Info $ unwords
    [ "Branching on"
    , show (length branches')
    , "override variants of"
    , fnName
    , "..."
    ]
  let retTy = Crucible.handleReturnType h
  res <- Crucible.regValue <$> Crucible.callOverride h
     (Crucible.mkOverride' "overrideBranches" retTy
       (Crucible.symbolicBranches Crucible.emptyRegMap $
         [ ( precond
           , do g <- Crucible.readGlobals
                res <- liftIO $ runOverrideMatcher sym g
                   (st^.setupValueSub)
                   (st^.termSub)
                   (st^.osFree)
                   (st^.osLocation)
                   (methodSpecHandler_poststate opts sc cc retTy cs)
                case res of
                  Left (OF loc rsn)  ->
                    -- TODO, better pretty printing for reasons
                    liftIO
                      $ Crucible.abortExecBecause
                      $ Crucible.AssertionFailure
                      $ Crucible.SimError loc
                      $ Crucible.AssertFailureSimError "assumed false" (show rsn)
                  Right (ret,st') ->
                    do liftIO $ forM_ (st'^.osAssumes) $ \(_md,asum) ->
                         Crucible.addAssumption bak
                          $ Crucible.GenericAssumption (st^.osLocation) "override postcondition" asum
                       Crucible.writeGlobals (st'^.overrideGlobals)
                       Crucible.overrideReturn' (Crucible.RegEntry retTy ret)
           , Just (W4.plSourceLoc (cs ^. MS.csLoc))
           )
         | (precond, cs, st) <- branches'
         ] ++
         [ let e prettyArgs symFalse unsat = show $ PP.vcat $ concat
                 [ [ PP.pretty $
                     "No override specification applies for " ++ fnName ++ "."
                   ]
                 , [ "Arguments:"
                   , bullets '-' prettyArgs
                   ]
                 , if | not (null false) ->
                        [ PP.vcat
                          [ PP.pretty (unwords
                              [ "The following overrides had some preconditions"
                              , "that failed concretely:"
                              ])
                          , bullets '-' (map ppConcreteFailure false)
                          ]
                        ]
                      -- See comment on ppSymbolicFailure: this needs more
                      -- examination to see if it's useful.
                      -- - | not (null symFalse) ->
                      --   [ PP.text (unwords
                      --       [ "The following overrides had some preconditions "
                      --       , "that failed symbolically:"
                      --       ]) PP.<$$> bullets '-' (map ppSymbolicFailure symFalse)
                      --   ]

                      -- Note that we only print these in case no override had
                      -- individually (concretely or symbolically) false
                      -- preconditions.
                      | not (null unsat) && null false && null symFalse ->
                        [ PP.vcat
                          [ PP.pretty (unwords
                            [ "The conjunction of these overrides' preconditions"
                            , "was unsatisfiable, meaning your override can never"
                            , "apply. You probably have unintentionally specified"
                            , "mutually exclusive/inconsistent preconditions."
                            ])
                          , bullets '-' (unsat ^.. each . owpMethodSpec . to MS.ppMethodSpec)
                          ]
                        ]
                      | null false && null symFalse ->
                        [ PP.pretty (unwords
                            [ "No overrides had any single concretely or"
                            , "symbolically failing preconditions."
                            ])
                        ]
                      | otherwise -> []
                 , if | simVerbose opts < 3 ->
                        [ PP.pretty $ unwords
                          [ "Run SAW with --sim-verbose=3 to see a description"
                          , "of each override."
                          ]
                        ]
                      | otherwise ->
                        [ PP.vcat
                          [ "Here are the descriptions of each override:"
                          , bullets '-'
                            (branches ^.. each . owpMethodSpec . to MS.ppMethodSpec)
                          ]
                        ]
                 ]
           in ( W4.truePred sym
              , liftIO $ do
                  -- Now that we're failing, do the additional work of figuring out
                  -- if any overrides had symbolically false preconditions
                  symFalse <- catMaybes <$> (forM unknown $ \owp ->
                    findFalsePreconditions bak owp <&>
                      \case
                        [] -> Nothing
                        ps -> Just (owp, ps))

                  prettyArgs <-
                    ppArgs sym cc (NE.head css) (Crucible.RegMap args)

                  unsat <-
                    filterM
                      (unsatPreconditions bak (owpPreconditions . each . _2 . W4.labeledPred))
                      branches

                  Crucible.addFailedAssertion bak
                    (Crucible.GenericSimError (e prettyArgs symFalse unsat))
              , Just (W4.plSourceLoc call_loc)
              )
         ]))
     (Crucible.RegMap args)
  liftIO $ printOutLn opts Info $ unwords ["Applied override!", fnName]
  return res

instantiateExtResolveSAWPred ::
  SharedContext ->
  MIRCrucibleContext ->
  Term ->
  OverrideMatcher MIR md (W4.Pred Sym)
instantiateExtResolveSAWPred sc cc cond = do
  sub <- OM (use termSub)
  liftIO $ resolveSAWPred cc =<< scInstantiateExt sc sub cond

-- | Map the given substitution over all 'SetupTerm' constructors in
-- the given 'MirPointsTo' value.
instantiateMirPointsTo ::
  SharedContext     ->
  IntMap Term       ->
  MirPointsTo       ->
  IO MirPointsTo
instantiateMirPointsTo sc s (MirPointsTo md reference target) =
  MirPointsTo md <$> instantiateSetupValue sc s reference
                 <*> instantiateMirPointsToTarget target
  where
    instantiateMirPointsToTarget (CrucibleMirCompPointsToTarget referents) =
      CrucibleMirCompPointsToTarget <$> traverse (instantiateSetupValue sc s) referents
    instantiateMirPointsToTarget (MirPointsToSingleTarget referent) =
      MirPointsToSingleTarget <$> instantiateSetupValue sc s referent
    instantiateMirPointsToTarget (MirPointsToMultiTarget referentArray) =
      MirPointsToMultiTarget <$> instantiateSetupValue sc s referentArray


-- | Map the given substitution over all 'SetupTerm' constructors in
-- the given 'SetupValue'.
instantiateSetupValue ::
  SharedContext     ->
  IntMap Term       ->
  SetupValue        ->
  IO SetupValue
instantiateSetupValue sc s v =
  case v of
    MS.SetupVar _                     -> return v
    MS.SetupTerm tt                   -> MS.SetupTerm <$> doTerm tt
    MS.SetupArray elemTy vs           -> MS.SetupArray elemTy <$> mapM (instantiateSetupValue sc s) vs
    MS.SetupStruct did vs             -> MS.SetupStruct did <$> mapM (instantiateSetupValue sc s) vs
    MS.SetupEnum enum_                -> MS.SetupEnum <$> instantiateSetupEnum enum_
    MS.SetupTuple x vs                -> MS.SetupTuple x <$> mapM (instantiateSetupValue sc s) vs
    MS.SetupSlice slice               -> MS.SetupSlice <$> instantiateSetupSlice slice
    MS.SetupNull empty                -> absurd empty
    MS.SetupGlobal _ _                -> return v
    MS.SetupElem m a i                -> MS.SetupElem m <$> instantiateSetupValue sc s a <*> pure i
    MS.SetupField _ _ _               -> return v
    MS.SetupCast _ _                  -> return v
    MS.SetupUnion empty _ _           -> absurd empty
    MS.SetupGlobalInitializer _ _     -> return v
    MS.SetupMux x c t f               -> MS.SetupMux x
                                           <$> doTerm c
                                           <*> instantiateSetupValue sc s t
                                           <*> instantiateSetupValue sc s f
  where
    doTerm (TypedTerm schema t) = TypedTerm schema <$> scInstantiateExt sc s t

    instantiateSetupEnum :: MirSetupEnum -> IO MirSetupEnum
    instantiateSetupEnum (MirSetupEnumVariant adt variant variantIdx vs) =
      MirSetupEnumVariant adt variant variantIdx <$>
      mapM (instantiateSetupValue sc s) vs
    instantiateSetupEnum (MirSetupEnumSymbolic adt discr variants) =
      MirSetupEnumSymbolic adt discr <$>
      mapM (mapM (instantiateSetupValue sc s)) variants

    instantiateSetupSlice :: MirSetupSlice -> IO MirSetupSlice
    instantiateSetupSlice (MirSetupSliceRaw ref len) =
      MirSetupSliceRaw
        <$> instantiateSetupValue sc s ref
        <*> instantiateSetupValue sc s len
    instantiateSetupSlice (MirSetupSlice sliceInfo arr) =
      MirSetupSlice sliceInfo <$> instantiateSetupValue sc s arr
    instantiateSetupSlice (MirSetupSliceRange sliceInfo arr start end) = do
      arr' <- instantiateSetupValue sc s arr
      pure $ MirSetupSliceRange sliceInfo arr' start end

-- learn pre/post condition
learnCond ::
  Options ->
  SharedContext ->
  MIRCrucibleContext ->
  CrucibleMethodSpecIR ->
  MS.PrePost ->
  StateSpec ->
  OverrideMatcher MIR w ()
learnCond opts sc cc cs prepost ss =
  do let loc = cs ^. MS.csLoc
     matchPointsTos opts sc cc cs prepost (ss ^. MS.csPointsTos)
     F.traverse_ (learnSetupCondition opts sc cc cs prepost) (ss ^. MS.csConditions)
     assertTermEqualities sc cc
     enforceDisjointness cc loc ss
     enforceCompleteSubstitution loc ss

-- | Process a "mir_equal" statement from the precondition
-- section of the CrucibleSetup block.
learnEqual ::
  Options                                          ->
  SharedContext                                    ->
  MIRCrucibleContext                               ->
  CrucibleMethodSpecIR                             ->
  MS.ConditionMetadata                             ->
  MS.PrePost                                       ->
  SetupValue       {- ^ first value to compare  -} ->
  SetupValue       {- ^ second value to compare -} ->
  OverrideMatcher MIR w ()
learnEqual opts sc cc spec md prepost v1 v2 =
  do val1 <- resolveSetupValueMIR opts cc sc spec v1
     val2 <- resolveSetupValueMIR opts cc sc spec v2
     p <- liftIO (equalValsPred cc val1 val2)
     let name = "equality " ++ MS.stateCond prepost
     let loc = MS.conditionLoc md
     addAssert p md (Crucible.SimError loc (Crucible.AssertFailureSimError name ""))

-- | Process a "points_to" statement from the precondition section of
-- the CrucibleSetup block. First, load the value from the address
-- indicated by 'ptr', and then match it against the pattern 'val'.
learnPointsTo ::
  Options                    ->
  SharedContext              ->
  MIRCrucibleContext         ->
  CrucibleMethodSpecIR       ->
  MS.PrePost                 ->
  MirPointsTo                ->
  OverrideMatcher MIR w ()
learnPointsTo opts sc cc spec prepost (MirPointsTo md reference target) =
  mccWithBackend cc $ \bak ->
  do let col = cc ^. mccRustModule . Mir.rmCS ^. Mir.collection
         sym = backendGetSym bak
     globals <- OM (use overrideGlobals)
     MIRVal referenceShp referenceVal <-
       resolveSetupValueMIR opts cc sc spec reference
     -- By the time we reach here, we have already checked (in mir_points_to)
     -- that we are in fact dealing with a reference value, so the call to
     -- `testRefShape` below should always succeed.
     IsRefShape _ referenceInnerMirTy _ referenceInnerTpr <-
       case testRefShape referenceShp of
         Just irs -> pure irs
         Nothing ->
           panic "learnPointsTo" [
               "Unexpected non-reference type:",
               "   " <> Text.pack (show $ PP.pretty $ shapeMirTy referenceShp)
           ]
     let innerShp = tyToShapeEq col referenceInnerMirTy referenceInnerTpr
     case target of
       CrucibleMirCompPointsToTarget {} ->
         panic "learnPointsTo"
           [ "CrucibleMirCompPointsToTarget not implemented in SAW"
           ]
       MirPointsToSingleTarget referent -> do
         v <- liftIO $ Mir.readMirRefIO bak globals iTypes
           referenceInnerTpr referenceVal
         matchArg opts sc cc spec prepost md (MIRVal innerShp v) referent
       MirPointsToMultiTarget referentArray -> do
         referentArrayMirTy <- typeOfSetupValueMIR cc spec referentArray
         case referentArrayMirTy of
           -- mir_points_to_multi should check that the RHS type is TyArray, so
           -- this case should always match.
           Mir.TyArray _ len -> do
             vs <- liftIO $ V.generateM len $ \i -> do
               i_sym <- usizeBvLit sym i
               referenceVal' <- Mir.mirRef_offsetIO bak iTypes referenceVal i_sym
               Mir.readMirRefIO bak globals iTypes referenceInnerTpr referenceVal'
             matchArg opts sc cc spec prepost md
               (MIRVal (ArrayShape referentArrayMirTy referenceInnerMirTy innerShp)
                       (Mir.MirVector_Vector vs))
               referentArray
           _ ->
             panic "learnPointsTo"
               [ "Unexpected non-array SetupValue as MirPointsToMultiTarget:"
               , Text.pack (show referentArray)
               ]
  where
    iTypes = cc ^. mccIntrinsicTypes

-- | Process a "mir_precond" statement from the precondition
-- section of the CrucibleSetup block.
learnPred ::
  SharedContext                                                       ->
  MIRCrucibleContext                                                  ->
  MS.ConditionMetadata                                                ->
  MS.PrePost                                                          ->
  Term             {- ^ the precondition to learn                  -} ->
  OverrideMatcher MIR w ()
learnPred sc cc md prepost t =
  do s <- OM (use termSub)
     u <- liftIO $ scInstantiateExt sc s t
     p <- liftIO $ resolveBoolTerm (cc ^. mccSym) u
     let loc = MS.conditionLoc md
     addAssert p md (Crucible.SimError loc (Crucible.AssertFailureSimError (MS.stateCond prepost) ""))

-- | Use the current state to learn about variable assignments based on
-- preconditions for a procedure specification.
learnSetupCondition ::
  Options                    ->
  SharedContext              ->
  MIRCrucibleContext         ->
  CrucibleMethodSpecIR       ->
  MS.PrePost                 ->
  SetupCondition             ->
  OverrideMatcher MIR w ()
learnSetupCondition opts sc cc spec prepost cond =
  case cond of
    MS.SetupCond_Equal md val1 val2 -> learnEqual opts sc cc spec md prepost val1 val2
    MS.SetupCond_Pred md tm         -> learnPred sc cc md prepost (ttTerm tm)
    MS.SetupCond_Ghost md var val   -> learnGhost sc md prepost var val

-- | Which part of a 'SetupValue' to match against.
newtype MatchProj
  -- | Match against the given index of the array 'SetupValue'.
  = MatchIndex Int

-- | Match the value of a function argument with a symbolic 'SetupValue'.
matchArg ::
  forall w.
  Options              {- ^ saw script print out opts -} ->
  SharedContext        {- ^ context for constructing SAW terms -} ->
  MIRCrucibleContext   {- ^ context for interacting with Crucible -} ->
  CrucibleMethodSpecIR {- ^ specification for current function override -} ->
  MS.PrePost ->
  MS.ConditionMetadata ->
  MIRVal               {- ^ concrete simulation value -} ->
  SetupValue           {- ^ expected specification value -} ->
  OverrideMatcher MIR w ()
matchArg opts sc cc cs prepost md = go False []
  where

  go ::
    -- The internal Bool argument is to keep track of whether the given
    -- SetupValue is inside a SetupCast. The SetupVar case uses different
    -- types depending on whether it is in a SetupCast or not, but the
    -- SetupCast case can't just do a recursive call with different types,
    -- since we don't know what the types should be until we get to the
    -- SetupVar. So instead we just pass along the fact that we are recursing
    -- inside a SetupCast.
    Bool ->
    -- Due to projection SetupValue constructors like SetupElem, which may be
    -- arbitrarily nested, we keep a stack of MatchProjs to track which part
    -- of the given SetupValue we are trying to match against. For instance,
    -- [MatchIndex 3, MatchIndex 7] means we are trying to match the MIRVal
    -- against index 7 of index 3 of the SetupValue.
    --
    -- At a high level, we are peeling off value projection SetupValue
    -- constructors from `expected` when we encounter them and pushing them onto
    -- the projStack as MatchProjs as we recurse. Eventually they have to all
    -- come off of the projStack, which is done in a few ways:
    -- * When we reach the base case of SetupTerm, we apply the MatchProjs to
    --   the SAWCore term.
    -- * When we reach a base case where the expected value is a MIRVal, such as
    --   SetupGlobalInitializer, we apply the MatchProjs to the MIRVal.
    -- * When we reach a SetupArray case, we can index into the SetupArray.
    -- * When we have a match failure, we reapply the projStack back onto
    --   `expected` as value projection SetupValue constructors, for the error
    --   message to make sense.
    [MatchProj] ->
    MIRVal ->
    SetupValue ->
    OverrideMatcher MIR w ()

  go inCast projStack actual expected
    | MS.SetupTerm expectedTT <- expected
    , TypedTermSchema (Cryptol.Forall [] [] tyexpr) <- ttType expectedTT
    , Right tval <- Cryptol.evalType mempty tyexpr
    = do sym <- Ov.getSymInterface
         (tval', expectedTerm') <-
           applyProjToTerm sym fail_ projStack tval (ttTerm expectedTT)
         realTerm <- valueToSC sym fail_ tval' actual
         matchTerm sc md prepost realTerm expectedTerm'

    | otherwise =
      mccWithBackend cc $ \bak -> do
      let sym = backendGetSym bak
      -- The top of the `projStack` represents the projection to apply to
      -- `expected`. So, for instance, if there is a case where
      -- `typeOfSetupValue expected` might be `Mir.TyArray`, then it should
      -- handle the possibility of the top of the `projStack` being
      -- `MatchIndex`, since it is valid to apply `SetupElem MirIndexIntoVal` on
      -- `expected`. On the other hand, for cases where `expected` can never be
      -- an array type, `projStack` should be matched to `[]`, so if the user
      -- attempted to index into it, the pattern match would fail and an error
      -- would be reported.
      case (projStack, actual, expected) of
        ([], MIRVal (RefShape refTy pointeeTy mutbl tpr) ref, MS.SetupVar var)
          | inCast ->
            -- When we have a cast, the type inside the Crucible reference may
            -- be different from the pointee type of the SetupValue in SAW after
            -- the cast. Here, we are creating a MirPointer, so we want to use
            -- the "true" type of the reference. This means pointeeTy and
            -- expectedTy are wrong, so we ignore those and instead look up the
            -- pointee type from the MirAllocSpec for this variable (i.e. the
            -- type given to the mir_alloc that created it).
            --
            -- See Note [Raw pointer casts] in
            -- SAWCentral.Crucible.MIR.Setup.Value for more info.
            case Map.lookup var tyenv of
              Just (Some ma) ->
                assignVar cc md var $
                  Some (MirPointer (ma^.maType) (ma^.maPtrKind) (ma^.maMutbl) (ma^.maMirType) ref)
              Nothing ->
                panic "matchArg" ["No MirAllocSpec for SetupVar " <> Text.pack (show var)]
          | otherwise ->
            assignVar cc md var (Some (MirPointer tpr (tyToPtrKind refTy) mutbl pointeeTy ref))

        ([], MIRVal (RefShape {}) _, MS.SetupCast _ v) ->
          -- Ideally we would pass the "true" type of the underlying reference
          -- here, instead of passing along the post-cast types unchanged, but
          -- we don't know the true type until we get to a SetupVar.
          go True [] actual v

        (_, _, MS.SetupArray _elemTy zs) ->
          case projStack of

            -- match an index of a SetupArray by just indexing into it
            MatchIndex i : restProjStack ->
              case zs ^? ix i of
                Just z -> go inCast restProjStack actual z
                Nothing -> fail_

            -- match arrays point-wise
            [] ->
              case actual of
                MIRVal (ArrayShape _ _ elemShp) xs
                  | Mir.MirVector_Vector xs' <- xs
                  , V.length xs' == length zs ->
                    sequence_
                      [ go inCast [] (MIRVal elemShp x) z
                      | (x, z) <- zip (V.toList xs') zs ]

                  | Mir.MirVector_PartialVector xs' <- xs
                  , V.length xs' == length zs ->
                    do let xs'' = V.map (readMaybeType sym "vector element" (shapeType elemShp)) xs'
                       sequence_
                         [ go inCast [] (MIRVal elemShp x) z
                         | (x, z) <- zip (V.toList xs'') zs ]

                _ -> fail_

        (_, _, MS.SetupElem mode z i) ->
          case mode of

            -- match value SetupElem by pushing MatchIndex onto the projection
            -- stack
            MirIndexIntoVal ->
              go inCast (MatchIndex i : projStack) actual z

            -- match reference SetupElem by getting the reference to the
            -- containing vector
            MirIndexIntoRef ->
              case actual of
                MIRVal (RefShape elemRefTy elemTy elemMutbl elemTpr) elemRef -> do
                  arrRefTy <- typeOfSetupValue cc tyenv nameEnv z
                  case tyToShape col arrRefTy of
                    Some arrRefShp@(RefShape _
                                             (Mir.TyArray elemTy' _)
                                             arrMutbl
                                             (Mir.MirVectorRepr elemTpr'))
                      | tyToPtrKind elemRefTy == tyToPtrKind arrRefTy
                      , checkCompatibleTys elemTy elemTy'
                      , elemMutbl == arrMutbl
                      , Just Refl <- W4.testEquality elemTpr elemTpr' -> do
                        -- get the reference to the containing vector and the
                        -- index of the current reference within it
                        Ctx.Empty Ctx.:> Crucible.RV arrRef
                                  Ctx.:> Crucible.RV i'_sym <-
                          liftIO $ Mir.mirRef_peelIndexIO bak iTypes elemRef
                        -- the index should be concrete
                        case fromInteger . BV.asUnsigned <$> W4.asBV i'_sym of
                          Just i'
                            -- make sure the expected and actual indices match
                            | i == i' ->
                              go inCast [] (MIRVal arrRefShp arrRef) z
                          _ -> fail_
                    _ -> fail_
                _ -> fail_

            MirIndexOffsetRef ->
              panic "matchArg" ["MirIndexOffsetRef not yet implemented"]

        -- match the underlying, non-zero-sized field of a repr(transparent)
        -- struct
        ([], MIRVal (TransparentShape _ shp) val, MS.SetupStruct adt zs)
          | Just i <- Mir.findReprTransparentField col adt
          , Just z <- zs ^? ix i ->
            go inCast [] (MIRVal shp val) z

        -- match the fields of a struct point-wise
        ([], MIRVal (StructShape _ _ xsFldShps) xs, MS.SetupStruct _ zs) ->
          matchFields sym xsFldShps xs zs

        -- In order to match an enum value, we first check to see if the
        -- expected value is a specific enum variant or a symbolic enum...
        ([],
         MIRVal (EnumShape _ _ variantShps _ discrShp)
                (Ctx.Empty
                  Ctx.:> Crucible.RV actualDiscr
                  Ctx.:> Crucible.RV variantAssn),
         MS.SetupEnum enum_) ->
            case enum_ of
              -- ...if the expected value is a specific enum variant, then we
              -- must:
              --
              -- - Ensure that the discriminant values match
              -- - Ensure that the predicate in the variant's VariantBranch
              --   holds. This should always succeed if the discriminant values
              --   match.
              -- - Match the fields of the VariantBranch's payload point-wise.
              MirSetupEnumVariant adt variant variantIdxInt zs -> do
                Some variantIdx <- pure $
                  variantIntIndex (adt ^. Mir.adtname) variantIdxInt (Ctx.size variantAssn)
                VariantShape xsFldShps <- pure $ variantShps Ctx.! variantIdx
                let Crucible.VB expectedVariant = variantAssn Ctx.! variantIdx

                -- Ensure that the discriminant values match.
                IsBVShape _ discrW <- pure $ testDiscriminantIsBV discrShp
                let discr = getEnumVariantDiscr variant
                expectedDiscr <- liftIO $
                  W4.bvLit sym discrW $ BV.mkBV discrW discr
                discrEq <- liftIO $
                  W4.bvEq sym expectedDiscr actualDiscr
                addAssert discrEq md =<< notEq

                case expectedVariant of
                  W4.PE xsPred xs -> do
                    -- Ensure that the variant is defined, i.e., that the
                    -- predicate in the underlying PartialExpr holds. Due to the
                    -- way that we construct specific enum values, this should
                    -- always hold if the discriminant values match, but we
                    -- check it anyway to be on the safe side.
                    addAssert xsPred md =<< notEq
                    -- Finally, ensure that the fields match point-wise.
                    matchFields sym xsFldShps xs zs
                  W4.Unassigned ->
                    -- If we see `Unassigned`, we immediately know that the
                    -- variant should not be defined. Because we know in advance
                    -- that this VariantBranch's predicate *should* hold, the
                    -- overall match will fail.
                    fail_

              -- ...if the expected value is a symbolic enum (see
              -- Note [Symbolic enums] in SAWCentral.Crucible.MIR.Setup.Value),
              -- then we employ a more general version of the
              -- `MirSetupEnumVariant` case above:
              --
              -- - Ensure that the discriminant values match
              -- - For each possible variant, match the fields of the
              --   VariantBranch's payload point-wise under the assumption that
              --   the VariantBranch's predicate holds.
              --
              -- The `MirSetupEnumVariant` case can be seen as a special case of
              -- this approach where we already know that one specific
              -- VariantBranch's predicate should hold, and the predicates in
              -- all other VariantBranches should be false.
              MirSetupEnumSymbolic _ expectedDiscr variantFlds -> do
                -- Ensure that the discriminant values match.
                go inCast [] (MIRVal discrShp actualDiscr) expectedDiscr

                sequence_ @_ @_ @()
                  [ case xPE of
                      W4.PE xsPred xs ->
                        -- For each variant, check that the fields of the
                        -- variant (xs) match point-wise under the assumption
                        -- that the VariantBranch's predicate (xsPred) holds.
                        withConditionalPred xsPred $
                          matchFields sym xsFldShps xs zs
                      W4.Unassigned ->
                        -- If we see `Unassigned`, then we immediately know that
                        -- the variant should not defined. We can skip checking
                        -- anything in this case, since we know that the fields
                        -- of the variant cannot match. (Note that we do not
                        -- fail outright, as it is still possible that other
                        -- variants might match.)
                        pure ()
                  | (Some (Functor.Pair (VariantShape xsFldShps) (Crucible.VB xPE)), zs) <-
                      zip
                        (FC.toListFC Some (Ctx.zipWith Functor.Pair variantShps variantAssn))
                        variantFlds
                  ]

        -- match the fields of a tuple point-wise
        ([], MIRVal (TupleShape (Mir.TyTuple _) _ xsFldShps) xs, MS.SetupTuple () zs) ->
          matchFields sym xsFldShps xs zs

        -- See Note [Matching slices in overrides]
        ([],
         MIRVal (SliceShape actualSliceRefTy@(Mir.TyRef _ _) actualElemTy actualMutbl actualElemTpr)
                (Ctx.Empty Ctx.:> Crucible.RV actualSliceRef Ctx.:> Crucible.RV actualSliceLenSym),
         MS.SetupSlice slice)
           | -- Currently, all slice lengths must be concrete, so the case below
             -- should always succeed.
             Just actualSliceLenBV <- W4.asBV actualSliceLenSym -> do
             let actualSliceLen :: Int
                 actualSliceLen = fromInteger $ BV.asUnsigned actualSliceLenBV

             let -- Retrieve the N in &[T; N], failing if the supplied type is
                 -- different.
                 arrRefTyLen :: Mir.Ty -> OverrideMatcher MIR w Int
                 arrRefTyLen (Mir.TyRef (Mir.TyArray _ len) _) = pure len
                 arrRefTyLen _ = fail_

             let -- Take the actual slice value's underlying reference, convert
                 -- it to an array reference value, and match it against the
                 -- expected array reference value. See
                 -- Note [Matching slices in overrides] for why we do this.
                 matchSlice :: Mir.Ty -> SetupValue -> OverrideMatcher MIR w ()
                 matchSlice expectedArrRefTy expectedArrRef = do
                   arrLen <- arrRefTyLen expectedArrRefTy
                   Ctx.Empty Ctx.:> Crucible.RV actualArrRef Ctx.:> _ <-
                     liftIO $ Mir.mirRef_peelIndexIO bak iTypes actualSliceRef
                   let actualArrTy = Mir.TyArray actualElemTy arrLen
                   let actualArrTpr = Mir.MirVectorRepr actualElemTpr
                   let actualArrRefTy = Mir.TyRef actualArrTy actualMutbl
                   let actualArrRefShp = RefShape actualArrRefTy actualArrTy actualMutbl actualArrTpr
                   go inCast []
                     (MIRVal actualArrRefShp actualArrRef)
                     expectedArrRef

             actualSliceInfo <- sliceRefTyToSliceInfo actualSliceRefTy
             case slice of
               MirSetupSliceRaw{} ->
                 panic "matchArg" ["SliceRaw not yet implemented"]
               MirSetupSlice expectedSliceInfo expectedArrRef -> do
                 -- Check that both the expected and actual values are the same
                 -- sort of slice.
                 matchSliceInfos expectedSliceInfo actualSliceInfo
                 -- Check that the length of the expected array reference value
                 -- matches that of the actual slice reference value.
                 expectedArrRefTy <- typeOfSetupValue cc tyenv nameEnv expectedArrRef
                 expectedSliceLen <- arrRefTyLen expectedArrRefTy
                 unless (expectedSliceLen == actualSliceLen) fail_
                 -- Match the reference values.
                 matchSlice expectedArrRefTy expectedArrRef
               MirSetupSliceRange expectedSliceInfo expectedArrRef expectedStart expectedEnd -> do
                 -- Check that both the expected and actual values are the same
                 -- sort of slice.
                 matchSliceInfos expectedSliceInfo actualSliceInfo
                 -- Check that the length of the range of the expected slice
                 -- reference value matches that of the actual slice reference
                 -- value. By this point, we have already checked (in
                 -- resolveSetupVal) that the length of the range is less than
                 -- or equal to the length of the expected slice reference's
                 -- underlying array, so there is no need to check it here.
                 expectedArrRefTy <- typeOfSetupValue cc tyenv nameEnv expectedArrRef
                 let expectedSliceLen = expectedEnd - expectedStart
                 unless (expectedSliceLen == actualSliceLen) fail_
                 -- Match the reference values.
                 matchSlice expectedArrRefTy expectedArrRef

        ([], MIRVal (RefShape (Mir.TyRef _ _) _ _ xTpr) x, MS.SetupGlobal () name) -> do
          static <- findStatic colState name
          Mir.StaticVar yGlobalVar <- findStaticVar colState (static ^. Mir.sName)
          let y = staticRefMux sym yGlobalVar
          case W4.testEquality xTpr (Crucible.globalType yGlobalVar) of
            Nothing -> fail_
            Just Refl -> do
              pred_ <- liftIO $
                Mir.mirRef_eqIO bak x y
              addAssert pred_ md =<< notEq
        (_, MIRVal actualShp _, MS.SetupGlobalInitializer () name) -> do
          static <- findStatic colState name
          staticInitMirVal <- findStaticInitializer cc static
          projRes <- runMaybeT $ applyProjToMIRVal sym projStack staticInitMirVal
          case projRes of
            Just staticInitMirVal'@(MIRVal expectedShp _)
              | checkCompatibleTys (shapeMirTy actualShp) (shapeMirTy expectedShp) -> do
                pred_ <- liftIO $ equalValsPred cc staticInitMirVal' actual
                addAssert pred_ md =<< notEq
            _ -> fail_
        (_, _, MS.SetupMux () c t f) -> do
          cPred <- liftIO $ resolveBoolTerm sym (ttTerm c)
          withConditionalPred cPred $
            go inCast projStack actual t
          cNegPred <- liftIO $ W4.notPred sym cPred
          withConditionalPred cNegPred $
            go inCast projStack actual f

        (_, _, MS.SetupNull empty)      -> absurd empty
        (_, _, MS.SetupUnion empty _ _) -> absurd empty

        _ -> fail_

    where

      colState = cc ^. mccRustModule . Mir.rmCS
      col      = colState ^. Mir.collection
      iTypes   = cc ^. mccIntrinsicTypes
      tyenv    = MS.csAllocations cs
      nameEnv  = MS.csTypeNames cs

      loc   = MS.conditionLoc md

      fail_ :: OverrideMatcher MIR w a
      fail_ = failure loc =<<
                mkStructuralMismatch opts cc sc cs actual
                  (reapplyProjToSetupValue projStack expected)

      -- Match the fields (point-wise) in a tuple, a struct, or enum variant.
      matchFields ::
        Sym ->
        Ctx.Assignment FieldShape ctx ->
        Ctx.Assignment (Crucible.RegValue' Sym) ctx ->
        [SetupValue] ->
        OverrideMatcher MIR w ()
      matchFields sym xsFldShps xs zs = do
        -- As a sanity check, first ensure that the number of fields matches
        -- what is expected.
        unless (Ctx.sizeInt (Ctx.size xs) == length zs) fail_
        -- Then match the fields point-wise.
        sequence_
          [ case xFldShp of
              ReqField shp ->
                go inCast [] (MIRVal shp x) z
              OptField shp -> do
                let x' = readMaybeType sym "field" (shapeType shp) x
                go inCast [] (MIRVal shp x') z
          | (Some (Functor.Pair xFldShp (Crucible.RV x)), z) <-
              zip (FC.toListFC Some (Ctx.zipWith Functor.Pair xsFldShps xs))
                  zs ]

      -- Check that both the expected and actual values are the same sort of
      -- slice. We don't want to accidentally mix up a &[u8] value with a &str
      -- value, as both have the same crucible-mir representation.
      matchSliceInfos :: MirSliceInfo -> MirSliceInfo -> OverrideMatcher MIR w ()
      matchSliceInfos expectedSliceInfo actualSliceInfo =
        unless (expectedSliceInfo == actualSliceInfo) fail_

      notEq = notEqual prepost opts loc cc sc cs
        (reapplyProjToSetupValue projStack expected)
        actual

{-
Note [Matching slices in overrides]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Matching slice references in overrides is surprisingly tricky. Suppose we have
expected and actual slice reference values, both of type &[T]. At a high level,
we need to check two things:

1. The lengths of the expected and actual slices are the same.
2. The underlying references (of type `*const T`) are the same.

(1) is fairly straightforward, but (2) is easy to mess up. It's tempting to
just call `matchArg` on the underlying references, but don't do this! These
reference values are derived from array references, which are of type &[T; N],
but calling matchArg on something of type `*const T` will associate the
reference's AllocIndex to something that points to a value of type T, not a
value of type [T; N]. This leads to disaster later when checking mir_points_to
statements for that reference value in the precondition of the override, as it
will incorrectly require the right-hand side to be of type T, not [T; N]. (See
#2045 for an example of this actually happening.)

Instead, we want to call `matchArg` on the *array reference value* associated
with a slice, not the raw reference value itself. To do this, we take the raw
reference value and use mirRef_peelIndexIO, a crucible-mir memory model
operation which "peels back" the indexing operation that raw slice references
use, thereby turning a `*const T` value into a `&[T; N]` value. It's a bit
indirect, but it avoids needing to plumb around the original array reference
value alongside the slice's raw reference value.

We do something similar for &str slices, as crucible-mir backs them with an
array reference value of type &[u8; N].

This assumes that all slice reference values passed to an override were derived
from crucible-mir's indexing operations, as this is crucial for
mirRef_peelIndexIO to work. This is currently the case on every example we have
tried, but if we encounter an example that breaks this assumption, then we will
need to rethink this approach.
-}

-- | For each points-to statement read the memory value through the
-- given pointer (lhs) and match the value against the given pattern
-- (rhs).  Statements are processed in dependency order: a points-to
-- statement cannot be executed until bindings for any/all lhs
-- variables exist.
matchPointsTos ::
  Options          {- ^ saw script print out opts -} ->
  SharedContext    {- ^ term construction context -} ->
  MIRCrucibleContext  {- ^ simulator context     -}  ->
  CrucibleMethodSpecIR                               ->
  MS.PrePost                                         ->
  [MirPointsTo]       {- ^ points-tos                -} ->
  OverrideMatcher MIR w ()
matchPointsTos opts sc cc spec prepost = go False []
  where
    go ::
      Bool       {- progress indicator -} ->
      [MirPointsTo] {- delayed conditions -} ->
      [MirPointsTo] {- queued conditions  -} ->
      OverrideMatcher MIR w ()

    -- all conditions processed, success
    go _ [] [] = return ()

    -- not all conditions processed, no progress, failure
    go False delayed [] = failure (spec ^. MS.csLoc) (AmbiguousPointsTos delayed)

    -- not all conditions processed, progress made, resume delayed conditions
    go True delayed [] = go False [] delayed

    -- progress the next points-to in the work queue
    go progress delayed (c:cs) =
      do ready <- checkPointsTo c
         if ready then
           do learnPointsTo opts sc cc spec prepost c
              go True delayed cs
         else
           do go progress (c:delayed) cs

    -- determine if a precondition is ready to be checked
    checkPointsTo :: MirPointsTo -> OverrideMatcher MIR w Bool
    checkPointsTo (MirPointsTo _ ref _) = checkSetupValue ref

    checkSetupValue :: SetupValue -> OverrideMatcher MIR w Bool
    checkSetupValue v =
      do m <- OM (use setupValueSub)
         return (all (`Map.member` m) (setupVars v))

    -- Compute the set of variable identifiers in a 'SetupValue'
    setupVars :: SetupValue -> Set AllocIndex
    setupVars v =
      case v of
        MS.SetupVar i                     -> Set.singleton i
        MS.SetupStruct _ xs               -> foldMap setupVars xs
        MS.SetupEnum enum_                -> setupEnum enum_
        MS.SetupTuple _ xs                -> foldMap setupVars xs
        MS.SetupSlice slice               -> setupSlice slice
        MS.SetupArray _ xs                -> foldMap setupVars xs
        MS.SetupElem _ x _                -> setupVars x
        MS.SetupField _ x _               -> setupVars x
        MS.SetupTerm _                    -> Set.empty
        MS.SetupGlobal _ _                -> Set.empty
        MS.SetupGlobalInitializer _ _     -> Set.empty
        MS.SetupCast _ x                  -> setupVars x
        MS.SetupUnion empty _ _           -> absurd empty
        MS.SetupNull empty                -> absurd empty
        MS.SetupMux _ _ t f               -> setupVars t <> setupVars f

    -- Compute the set of variable identifiers in a 'MirSetupEnum'
    setupEnum :: MirSetupEnum -> Set AllocIndex
    setupEnum (MirSetupEnumVariant _ _ _ xs) =
      foldMap setupVars xs
    setupEnum (MirSetupEnumSymbolic _ _ variants) =
      foldMap (foldMap setupVars) variants

    -- Compute the set of variable identifiers in a 'MirSetupSlice'
    setupSlice :: MirSetupSlice -> Set AllocIndex
    setupSlice (MirSetupSliceRaw ref len) =
      setupVars ref <> setupVars len
    setupSlice (MirSetupSlice _sliceInfo arr) =
      setupVars arr
    setupSlice (MirSetupSliceRange _sliceInfo arr _start _end) =
      setupVars arr

-- | This function is responsible for implementing the \"override\" behavior
--   of method specifications.  The main work done in this function to manage
--   the process of selecting between several possible different override
--   specifications that could apply.  We want a proof to succeed if _any_
--   choice of method spec allows the proof to go through, which is a slightly
--   awkward thing to fit into the symbolic simulation framework.
--
--   The main work of determining the preconditions, postconditions, memory
--   updates and return value for a single specification is done by
--   the @methodSpecHandler_prestate@ and @methodSpecHandler_poststate@ functions.
--
--   In a first phase, we attempt to apply the precondition portion of each of
--   the given method specifications.  Each of them that might apply generate
--   a substitution for the setup variables and a collection of preconditions
--   that guard the specification.  We use these preconditions to compute
--   a multiway symbolic branch, one for each override which might apply.
--
--   In the body of each of the individual branches, we compute the postcondition
--   actions of the corresponding method specification.  This will update memory
--   and compute function return values, in addition to assuming postcondition
--   predicates.
methodSpecHandler ::
  forall rtp args ret.
  (?singleOverrideSpecialCase :: Bool) =>
  Options            {- ^ output/verbosity options                     -} ->
  SharedContext      {- ^ context for constructing SAW terms           -} ->
  MIRCrucibleContext {- ^ context for interacting with Crucible        -} ->
  IORef MetadataMap ->
  NE.NonEmpty (MS.CrucibleMethodSpecIR MIR)
    {- ^ specification for current function override  -} ->
  Crucible.FnHandle args ret {- ^ the handle for this function -} ->
  Crucible.OverrideSim (SAWCruciblePersonality Sym) Sym MIR rtp args ret
     (Crucible.RegValue Sym ret)
methodSpecHandler opts sc cc mdMap css h =
  mccWithBackend cc $ \bak -> do
  let sym = backendGetSym bak
  let fnName = NE.head css ^. MS.csMethod
  call_loc <- liftIO $ W4.getCurrentProgramLoc sym
  liftIO $ printOutLn opts Info $ unwords
    [ "Matching"
    , show (length css)
    , "overrides of "
    , show fnName
    , "..."
    ]
  Crucible.RegMap args <- Crucible.getOverrideArgs

  -- First, run the precondition matcher phase.  Collect together a list of the results.
  -- For each override, this will either be an error message, or a matcher state and
  -- a method spec.
  prestates <-
    do g0 <- Crucible.readGlobals
       forM css $ \cs -> liftIO $
         let initialFree = Set.fromList (map (ecVarIndex . tecExt)
                                           (view (MS.csPreState . MS.csFreshVars) cs))
          in runOverrideMatcher sym g0 Map.empty IntMap.empty initialFree (view MS.csLoc cs)
                      (do methodSpecHandler_prestate opts sc cc args cs
                          return cs)

  -- Print a failure message if all overrides failed to match.  Otherwise, collect
  -- all the override states that might apply, and compute the conjunction of all
  -- the preconditions.  We'll use these to perform symbolic branches between the
  -- various overrides.
  branches <-
    let prettyError methodSpec failureReason = do
          prettyArgs <- liftIO $ ppArgs sym cc methodSpec (Crucible.RegMap args)
          pure $
            PP.vcat
            [ MS.ppMethodSpec methodSpec
            , "Arguments:"
            , bullets '-' prettyArgs
            , ppOverrideFailure failureReason
            ]
    in
      case partitionEithers (F.toList prestates) of
          (errs, []) -> do
            msgs <-
              mapM (\(cs, err) ->
                      ("*" PP.<>) . PP.indent 2 <$> prettyError cs err)
                   (zip (F.toList css) errs)
            fail $ show $
              PP.vcat ["All overrides failed during structural matching:", PP.vcat msgs]
          (_, ss) -> liftIO $
            forM ss $ \(cs,st) ->
              return (OverrideWithPreconditions (st^.osAsserts) cs st)

  -- Now we do a second phase of simple compatibility checking: we check to see
  -- if any of the preconditions of the various overrides are concretely false.
  -- If so, there's no use in branching on them with @symbolicBranches@.
  (true, false, unknown) <- liftIO $ partitionOWPsConcrete sym branches

  -- Check if there is only a single override branch that might apply at this
  -- point.  If so, commit to it and handle that case specially. If there is
  -- more than one (or zero) branches that might apply, go to the general case.
  case true ++ unknown of
    [singleBranch] | ?singleOverrideSpecialCase ->
         handleSingleOverrideBranch opts sc cc call_loc mdMap h singleBranch
    _ -> handleOverrideBranches opts sc cc call_loc css h branches (true, false, unknown)

-- | Use a method spec to override the behavior of a function.
--   This function computes the post-state portion of the override,
--   which involves writing values into memory, computing the return value,
--   and computing postcondition predicates.
methodSpecHandler_poststate ::
  forall ret.
  Options                  {- ^ output/verbosity options                     -} ->
  SharedContext            {- ^ context for constructing SAW terms           -} ->
  MIRCrucibleContext       {- ^ context for interacting with Crucible        -} ->
  Crucible.TypeRepr ret    {- ^ type representation of function return value -} ->
  CrucibleMethodSpecIR     {- ^ specification for current function override  -} ->
  OverrideMatcher MIR RW (Crucible.RegValue Sym ret)
methodSpecHandler_poststate opts sc cc retTy cs =
  do executeCond opts sc cc cs (cs ^. MS.csPostState)
     computeReturnValue opts cc sc cs retTy (cs ^. MS.csRetValue)

-- | Use a method spec to override the behavior of a function.
--   This function computes the pre-state portion of the override,
--   which involves reading values from arguments and memory and computing
--   substitutions for the setup value variables, and computing precondition
--   predicates.
methodSpecHandler_prestate ::
  forall ctx w.
  Options                  {- ^ output/verbosity options                     -} ->
  SharedContext            {- ^ context for constructing SAW terms           -} ->
  MIRCrucibleContext       {- ^ context for interacting with Crucible        -} ->
  Ctx.Assignment (Crucible.RegEntry Sym) ctx
                           {- ^ the arguments to the function -} ->
  CrucibleMethodSpecIR     {- ^ specification for current function override  -} ->
  OverrideMatcher MIR w ()
methodSpecHandler_prestate opts sc cc args cs =
  do let expectedArgTypes = Map.elems (cs ^. MS.csArgBindings)
     let col = cc ^. mccRustModule ^. Mir.rmCS ^. Mir.collection
     let aux ::
           (Mir.Ty, SetupValue) -> Crucible.AnyValue Sym ->
           IO (MIRVal, SetupValue)
         aux (argTy, setupVal) val =
           case decodeMIRVal col argTy val of
             Just val' -> return (val', setupVal)
             Nothing -> fail "unexpected type"

     -- todo: fail if list lengths mismatch
     xs <- liftIO (zipWithM aux expectedArgTypes (assignmentToList args))

     let md = MS.ConditionMetadata
              { MS.conditionLoc = cs ^. MS.csLoc
              , MS.conditionTags = mempty
              , MS.conditionType = "formal argument matching"
              , MS.conditionContext = ""
              }

     sequence_ [ matchArg opts sc cc cs MS.PreState md x z | (x, z) <- xs]

     learnCond opts sc cc cs MS.PreState (cs ^. MS.csPreState)

-- | Try to translate the spec\'s 'SetupValue' into a 'MIRVal', pretty-print
--   the 'MIRVal'.
mkStructuralMismatch ::
  Options              {- ^ output/verbosity options -} ->
  MIRCrucibleContext ->
  SharedContext {- ^ context for constructing SAW terms -} ->
  CrucibleMethodSpecIR {- ^ for name and typing environments -} ->
  MIRVal {- ^ the value from the simulator -} ->
  SetupValue {- ^ the value from the spec -} ->
  OverrideMatcher MIR w (OverrideFailureReason MIR)
mkStructuralMismatch _opts cc _sc spec mirVal@(MIRVal shp _) setupval = do
  let sym = cc^.mccSym
  setupTy <- typeOfSetupValueMIR cc spec setupval
  pure $ StructuralMismatch
            (ppMIRVal sym mirVal)
            (MS.ppSetupValue setupval)
            (Just setupTy)
            (shapeMirTy shp)

-- | Create an error stating that the 'MIRVal' was not equal to the 'SetupValue'
notEqual ::
  MS.PrePost ->
  Options                     {- ^ output/verbosity options -} ->
  W4.ProgramLoc               {- ^ where is the assertion from? -} ->
  MIRCrucibleContext ->
  SharedContext               {- ^ context for constructing SAW terms -} ->
  MS.CrucibleMethodSpecIR MIR {- ^ for name and typing environments -} ->
  SetupValue                  {- ^ the value from the spec -} ->
  MIRVal                      {- ^ the value from the simulator -} ->
  OverrideMatcher MIR w Crucible.SimError
notEqual cond opts loc cc sc spec expected actual = do
  sym <- Ov.getSymInterface
  let prettyMIRVal = ppMIRVal sym actual
  prettySetupMIRVal <- ppSetupValueAsMIRVal opts cc sc spec expected
  let msg = unlines
        [ "Equality " ++ MS.stateCond cond
        , "Expected value (as a SAW value): "
        , show (MS.ppSetupValue expected)
        , "Expected value (as a Crucible value): "
        , show prettySetupMIRVal
        , "Actual value: "
        , show prettyMIRVal
        ]
  pure $ Crucible.SimError loc $ Crucible.AssertFailureSimError msg ""

-- | Pretty-print the arguments passed to an override
ppArgs ::
  forall args ann.
  Sym ->
  MIRCrucibleContext          {- ^ context for interacting with Crucible        -} ->
  MS.CrucibleMethodSpecIR MIR {- ^ specification for current function override  -} ->
  Crucible.RegMap Sym args    {- ^ arguments from the simulator                 -} ->
  IO [PP.Doc ann]
ppArgs sym cc cs (Crucible.RegMap args) = do
  let expectedArgTypes = map fst (Map.elems (cs ^. MS.csArgBindings))
  let col = cc ^. mccRustModule ^. Mir.rmCS ^. Mir.collection
  let aux memTy (Crucible.AnyValue tyrep val) =
        MIRVal (tyToShapeEq col memTy tyrep) val
  let vals = zipWith aux expectedArgTypes (assignmentToList args)
  pure $ map (ppMIRVal sym) vals

-- | Resolve a 'SetupValue' into a 'MIRVal' and pretty-print it
ppSetupValueAsMIRVal ::
  Options              {- ^ output/verbosity options -} ->
  MIRCrucibleContext ->
  SharedContext {- ^ context for constructing SAW terms -} ->
  MS.CrucibleMethodSpecIR MIR {- ^ for name and typing environments -} ->
  SetupValue ->
  OverrideMatcher MIR w (PP.Doc ann)
ppSetupValueAsMIRVal opts cc sc spec setupval = do
  sym <- Ov.getSymInterface
  mirVal <- resolveSetupValueMIR opts cc sc spec setupval
  pure $ ppMIRVal sym mirVal

resolveSetupValueMIR ::
  Options              ->
  MIRCrucibleContext   ->
  SharedContext        ->
  CrucibleMethodSpecIR ->
  SetupValue           ->
  OverrideMatcher MIR w MIRVal
resolveSetupValueMIR opts cc sc spec sval =
  do m <- OM (use setupValueSub)
     s <- OM (use termSub)
     let tyenv = MS.csAllocations spec
         nameEnv = MS.csTypeNames spec
     sval' <- liftIO $ instantiateSetupValue sc s sval
     liftIO $ resolveSetupVal cc m tyenv nameEnv sval' `X.catch` handleException opts

typeOfSetupValueMIR ::
  MIRCrucibleContext   ->
  CrucibleMethodSpecIR ->
  SetupValue           ->
  OverrideMatcher MIR w Mir.Ty
typeOfSetupValueMIR cc spec sval =
  do let tyenv = MS.csAllocations spec
         nameEnv = MS.csTypeNames spec
     liftIO $ typeOfSetupValue cc tyenv nameEnv sval

valueToSC ::
  forall w.
  Sym ->
  (forall a. OverrideMatcher MIR w a) {- ^ what to do on failure -} ->
  Cryptol.TValue ->
  MIRVal ->
  OverrideMatcher MIR w Term
valueToSC sym fail_ tval (MIRVal shp val) =
  case (tval, shp) of
    (Cryptol.TVBit, PrimShape _ W4.BaseBoolRepr) ->
      liftIO (toSC sym st val)
    (Cryptol.TVSeq n Cryptol.TVBit, PrimShape _ (W4.BaseBVRepr w))
      |  n == 8, Just _ <- W4.testEquality w (W4.knownNat @8)
      -> liftIO (toSC sym st val)
      |  n == 16, Just _ <- W4.testEquality w (W4.knownNat @16)
      -> liftIO (toSC sym st val)
      |  n == 32, Just _ <- W4.testEquality w (W4.knownNat @32)
      -> liftIO (toSC sym st val)
      |  n == 64, Just _ <- W4.testEquality w (W4.knownNat @64)
      -> liftIO (toSC sym st val)
      |  n == 128, Just _ <- W4.testEquality w (W4.knownNat @128)
      -> liftIO (toSC sym st val)
    (Cryptol.TVTuple [], UnitShape _) ->
      liftIO (scUnitValue sc)
    (Cryptol.TVTuple tys, TupleShape _ _ flds)
      |  length tys == Ctx.sizeInt (Ctx.size flds)
      -> do terms <-
              traverse
                fieldToSC
                (zip tys (FC.toListFC Some (Ctx.zipWith Functor.Pair flds val)))
            liftIO (scTupleReduced sc terms)
    (Cryptol.TVSeq n cryty, ArrayShape _ _ arrShp)
      |  Mir.MirVector_Vector vals <- val
      ,  toInteger (V.length vals) == n
      -> do terms <- V.toList <$>
              traverse (\v -> valueToSC sym fail_ cryty (MIRVal arrShp v)) vals
            t <- shapeToTerm sc arrShp
            liftIO (scVectorReduced sc t terms)
      |  Mir.MirVector_PartialVector vals <- val
      ,  toInteger (V.length vals) == n
      -> do let vals' = V.toList $
                        V.map (readMaybeType sym "vector element" (shapeType arrShp)) vals
            terms <-
              traverse (\v -> valueToSC sym fail_ cryty (MIRVal arrShp v)) vals'
            t <- shapeToTerm sc arrShp
            liftIO (scVectorReduced sc t terms)
      |  Mir.MirVector_Array{} <- val
      -> fail "valueToSC: Symbolic arrays not supported"
    _ ->
      fail_
  where
    st = sym ^. W4.userState
    sc = saw_ctx st

    fieldToSC ::
         (Cryptol.TValue, Some (Functor.Product FieldShape (Crucible.RegValue' Sym)))
      -> OverrideMatcher MIR w Term
    fieldToSC (ty, Some (Functor.Pair fldShp (Crucible.RV tm))) = do
      mirVal <-
        case fldShp of
          ReqField shp' ->
            pure $ MIRVal shp' tm
          OptField shp' ->
            pure $ MIRVal shp'
                 $ readMaybeType sym "field" (shapeType shp') tm
      valueToSC sym fail_ ty mirVal

-- | Apply a stack of projections to a 'Term'.
applyProjToTerm ::
  Sym ->
  (forall a. OverrideMatcher MIR w a) {- ^ what to do on failure -} ->
  [MatchProj] {- ^ stack of projections -} ->
  Cryptol.TValue {- ^ Cryptol type of the term argument -} ->
  Term ->
  OverrideMatcher MIR w (Cryptol.TValue, Term)
    -- ^ result term and its Cryptol type
applyProjToTerm sym fail_ projStack tp term =
  case projStack of
    [] -> pure (tp, term)
    MatchIndex i : restProjStack ->
      case tp of
        Cryptol.TVSeq sz elemTp
          | i >= 0 && fromIntegral i < sz -> do
            doIndex <- liftIO $ indexSeqTerm sym (sz, elemTp) term
            term' <- liftIO $ doIndex i
            applyProjToTerm sym fail_ restProjStack elemTp term'
        _ -> fail_

-- | Apply a stack of projections to a 'MIRVal'.
applyProjToMIRVal ::
  MonadIO m =>
  Sym ->
  [MatchProj] {- ^ stack of projections -} ->
  MIRVal ->
  MaybeT m MIRVal
applyProjToMIRVal _ [] mv = pure mv
applyProjToMIRVal sym (MatchIndex i : projStack) (MIRVal shp vec) =
  case shp of
    ArrayShape _ _ elemShp ->
      applyProjToMIRVal sym projStack =<< indexMirVector sym i elemShp vec
    _ ->
      Applicative.empty

-- | Apply a stack of projections to a 'SetupValue'. Does not actually extract
-- anything from the given 'SetupValue', but rather just applies projection
-- 'SetupValue' constructors to it.
reapplyProjToSetupValue ::
  [MatchProj] {- ^ stack of projections -}->
  SetupValue ->
  SetupValue
reapplyProjToSetupValue = flip (foldl projToCtor)
  where
    projToCtor sv (MatchIndex i) = MS.SetupElem MirIndexIntoVal sv i
