{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

-- | Override matching and application for MIR.
module SAWScript.Crucible.MIR.Override
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

import qualified Control.Exception as X
import Control.Lens
import Control.Monad (filterM, forM, forM_, unless, zipWithM)
import Control.Monad.IO.Class (MonadIO(..))
import qualified Data.BitVector.Sized as BV
import Data.Either (partitionEithers)
import qualified Data.Foldable as F
import qualified Data.Functor.Product as Functor
import Data.IORef (IORef, modifyIORef)
import Data.List (tails)
import qualified Data.List.NonEmpty as NE
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Maybe (catMaybes, isJust)
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
import qualified What4.ProgramLoc as W4

import Verifier.SAW.SharedTerm
import Verifier.SAW.Simulator.What4.ReturnTrip (saw_ctx, toSC)
import Verifier.SAW.TypedTerm

import SAWScript.Crucible.Common
import qualified SAWScript.Crucible.Common.MethodSpec as MS
import SAWScript.Crucible.Common.MethodSpec (AllocIndex(..))
import qualified SAWScript.Crucible.Common.Override as Ov (getSymInterface)
import SAWScript.Crucible.Common.Override hiding (getSymInterface)
import SAWScript.Crucible.MIR.MethodSpecIR
import SAWScript.Crucible.MIR.ResolveSetupValue
import SAWScript.Crucible.MIR.TypeShape
import SAWScript.Options
import SAWScript.Panic (panic)
import SAWScript.Utils (bullets, handleException)

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
  let assertTermEquality (t, md, e) = do
        p <- instantiateExtResolveSAWPred sc cc t
        addAssert p md e
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
            pure $ Some $ MirReferenceMuxConcrete refVal
          Nothing ->
            panic "checkMutableAllocPostconds"
                  [ "Unexpected non-reference type:"
                  , show $ PP.pretty $ shapeMirTy refShp
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
            ( Some $ MirReferenceMuxConcrete $ mp ^. mpRef
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
          , Some $ MirReferenceMuxConcrete $ staticRefMux sym gv
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
newtype MirReferenceMuxConcrete tp =
  MirReferenceMuxConcrete (Mir.MirReferenceMux Sym tp)

instance W4.TestEquality MirReferenceMuxConcrete where
  testEquality x y = PC.orderingF_refl (PC.compareF x y)

instance PC.EqF MirReferenceMuxConcrete where
  eqF x y = isJust (W4.testEquality x y)

instance PC.OrdF MirReferenceMuxConcrete where
  compareF (MirReferenceMuxConcrete x) (MirReferenceMuxConcrete y) =
    cmpRefMuxConcretely Proxy x y

-- | Compare two 'Mir.MirReferenceMux' values that are known to be concrete.
-- In particular, this assumes that the underlying 'Mir.FancyMuxTree' in each
-- value has exactly one leaf with a 'W4.Pred' that concretely evaluates to
-- 'W4.truePred'. If this is not the case, this function will panic.
-- See @Note [MIR compositional verification and mutable allocations]@.
cmpRefMuxConcretely ::
  forall sym tp1 tp2 proxy.
  Crucible.IsSymInterface sym =>
  proxy sym ->
  Mir.MirReferenceMux sym tp1 ->
  Mir.MirReferenceMux sym tp2 ->
  PC.OrderingF tp1 tp2
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
          else panic "cmpRefMuxConcretely"
                     [ "FancyMuxTree leaf with symbolic predicate"
                     , show $ W4.printSymExpr p
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
  Mir.MirReference sym tp1 ->
  Mir.MirReference sym tp2 ->
  PC.OrderingF tp1 tp2
cmpRefConcretely sym (Mir.MirReference r1 p1) (Mir.MirReference r2 p2) =
  cmpRootConcretely r1 r2 <<>> cmpPathConcretely sym p1 p2
cmpRefConcretely sym (Mir.MirReference_Integer tpr1 i1) (Mir.MirReference_Integer tpr2 i2) =
  PC.compareF tpr1 tpr2 <<>> cmpSymBVConcretely sym i1 i2 <<>> PC.EQF
cmpRefConcretely _ (Mir.MirReference _ _) (Mir.MirReference_Integer _ _) =
  PC.LTF
cmpRefConcretely _ (Mir.MirReference_Integer _ _) (Mir.MirReference _ _) =
  PC.GTF

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

-- Any_RefPath
cmpPathConcretely sym (Mir.Any_RefPath tpr1 p1) (Mir.Any_RefPath tpr2 p2) =
  PC.compareF tpr1 tpr2 <<>>
  cmpPathConcretely sym p1 p2 <<>>
  PC.EQF
cmpPathConcretely _ (Mir.Any_RefPath _ _) _ = PC.LTF
cmpPathConcretely _ _ (Mir.Any_RefPath _ _) = PC.GTF

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
  = panic "cmpSymBVConcretely"
          [ "SymBV not concrete"
          , show $ W4.printSymExpr symBV1
          , show $ W4.printSymExpr symBV2
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
`SAWScript.Crucible.LLVM.Override.invalidateMutableAllocs` function. The LLVM
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
`MirReferenceMux tp` values (where each `tp` can potentially be different) into
the same Set? At a first approximation, we actually put `Some MirReferenceMux`
values, which lets us ignore the `tp` parameter. But that's still not the full
story, since that would require MirReferenceMux to have an OrdF instance in
order to use Set operations, and MirReferenceMux has no such instance. Indeed,
it's not clear how to define such an instance: MirReferenceMux values can
contain symbolic information in the general case, which makes it tricky to
return a definite True-or-False answer regarding whether two values are equal.

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
  we give MirReferenceMuxConcrete an OrdF instance defined in terms of
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
  Map VarIndex Term ->
  MirPointsTo       ->
  IO MirPointsTo
instantiateMirPointsTo sc s (MirPointsTo md reference referents) =
  MirPointsTo md <$> instantiateSetupValue sc s reference
                 <*> traverse (instantiateSetupValue sc s) referents

-- | Map the given substitution over all 'SetupTerm' constructors in
-- the given 'SetupValue'.
instantiateSetupValue ::
  SharedContext     ->
  Map VarIndex Term ->
  SetupValue        ->
  IO SetupValue
instantiateSetupValue sc s v =
  case v of
    MS.SetupVar _                     -> return v
    MS.SetupTerm tt                   -> MS.SetupTerm <$> doTerm tt
    MS.SetupArray elemTy vs           -> MS.SetupArray elemTy <$> mapM (instantiateSetupValue sc s) vs
    MS.SetupStruct did vs             -> MS.SetupStruct did <$> mapM (instantiateSetupValue sc s) vs
    MS.SetupTuple x vs                -> MS.SetupTuple x <$> mapM (instantiateSetupValue sc s) vs
    MS.SetupSlice slice               -> MS.SetupSlice <$> instantiateSetupSlice slice
    MS.SetupNull empty                -> absurd empty
    MS.SetupGlobal _ _                -> return v
    MS.SetupElem _ _ _                -> return v
    MS.SetupField _ _ _               -> return v
    MS.SetupCast empty _              -> absurd empty
    MS.SetupUnion empty _ _           -> absurd empty
    MS.SetupGlobalInitializer _ _     -> return v
  where
    doTerm (TypedTerm schema t) = TypedTerm schema <$> scInstantiateExt sc s t

    instantiateSetupSlice :: MirSetupSlice -> IO MirSetupSlice
    instantiateSetupSlice (MirSetupSliceRaw ref len) =
      MirSetupSliceRaw
        <$> instantiateSetupValue sc s ref
        <*> instantiateSetupValue sc s len
    instantiateSetupSlice (MirSetupSlice arr) =
      MirSetupSlice <$> instantiateSetupValue sc s arr
    instantiateSetupSlice (MirSetupSliceRange arr start end) = do
      arr' <- instantiateSetupValue sc s arr
      pure $ MirSetupSliceRange arr' start end

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
learnPointsTo opts sc cc spec prepost (MirPointsTo md reference referents) =
  mccWithBackend cc $ \bak ->
  do let col = cc ^. mccRustModule . Mir.rmCS ^. Mir.collection
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
           panic "learnPointsTo"
                 [ "Unexpected non-reference type:"
                 , show $ PP.pretty $ shapeMirTy referenceShp
                 ]
     let innerShp = tyToShapeEq col referenceInnerMirTy referenceInnerTpr
     referentVal <- firstPointsToReferent referents
     v <- liftIO $ Mir.readMirRefIO bak globals iTypes
       referenceInnerTpr referenceVal
     matchArg opts sc cc spec prepost md (MIRVal innerShp v)
       referenceInnerMirTy referentVal
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

-- | Match the value of a function argument with a symbolic 'SetupValue'.
matchArg ::
  Options          {- ^ saw script print out opts -} ->
  SharedContext      {- ^ context for constructing SAW terms    -} ->
  MIRCrucibleContext    {- ^ context for interacting with Crucible -} ->
  CrucibleMethodSpecIR {- ^ specification for current function override  -} ->
  MS.PrePost                                                          ->
  MS.ConditionMetadata ->
  MIRVal             {- ^ concrete simulation value             -} ->
  Mir.Ty             {- ^ expected memory type                  -} ->
  SetupValue         {- ^ expected specification value          -} ->
  OverrideMatcher MIR w ()

matchArg opts sc cc cs prepost md actual expectedTy expected@(MS.SetupTerm expectedTT)
  | TypedTermSchema (Cryptol.Forall [] [] tyexpr) <- ttType expectedTT
  , Right tval <- Cryptol.evalType mempty tyexpr
  = do sym <- Ov.getSymInterface
       failMsg  <- mkStructuralMismatch opts cc sc cs actual expected expectedTy
       realTerm <- valueToSC sym md failMsg tval actual
       matchTerm sc md prepost realTerm (ttTerm expectedTT)

matchArg opts sc cc cs prepost md actual expectedTy expected =
  mccWithBackend cc $ \bak -> do
  let sym = backendGetSym bak
  case (actual, expectedTy, expected) of
    (MIRVal (RefShape _refTy pointeeTy mutbl tpr) ref, _, MS.SetupVar var) ->
      do assignVar cc md var (Some (MirPointer tpr mutbl pointeeTy ref))

    -- match arrays point-wise
    (MIRVal (ArrayShape _ _ elemShp) xs, Mir.TyArray y _len, MS.SetupArray _elemTy zs)
      | Mir.MirVector_Vector xs' <- xs
      , V.length xs' == length zs ->
        sequence_
          [ matchArg opts sc cc cs prepost md (MIRVal elemShp x) y z
          | (x, z) <- zip (V.toList xs') zs ]

      | Mir.MirVector_PartialVector xs' <- xs
      , V.length xs' == length zs ->
        do let xs'' = V.map (readMaybeType sym "vector element" (shapeType elemShp)) xs'
           sequence_
             [ matchArg opts sc cc cs prepost md (MIRVal elemShp x) y z
             | (x, z) <- zip (V.toList xs'') zs ]

    -- match the underlying field of a repr(transparent) struct
    (MIRVal (TransparentShape _ shp) val, _, MS.SetupStruct adt [z])
      | Just y <- Mir.reprTransparentFieldTy col adt ->
        matchArg opts sc cc cs prepost md (MIRVal shp val) y z

    -- match the fields of a struct point-wise
    (MIRVal (StructShape _ _ xsFldShps) (Crucible.AnyValue tpr@(Crucible.StructRepr _) xs),
     Mir.TyAdt _ _ _,
     MS.SetupStruct adt zs)
      | Ctx.sizeInt (Ctx.size xs) == length zs
      , let xsTpr = Crucible.StructRepr (FC.fmapFC fieldShapeType xsFldShps)
      , Just Refl <- W4.testEquality tpr xsTpr ->
        case adt of
          Mir.Adt _ Mir.Struct [v] _ _ _ _ ->
            let ys = v ^.. Mir.vfields . each . Mir.fty in
            sequence_
              [ case xFldShp of
                  ReqField shp ->
                    matchArg opts sc cc cs prepost md (MIRVal shp x) y z
                  OptField shp -> do
                    let x' = readMaybeType sym "field" (shapeType shp) x
                    matchArg opts sc cc cs prepost md (MIRVal shp x') y z
              | (Some (Functor.Pair xFldShp (Crucible.RV x)), y, z) <-
                  zip3 (FC.toListFC Some (Ctx.zipWith Functor.Pair xsFldShps xs))
                       ys
                       zs ]
          Mir.Adt _ ak _ _ _ _ _ ->
            panic "matchArg" ["AdtKind " ++ show ak ++ " not yet implemented"]

    -- match the fields of a tuple point-wise
    (MIRVal (TupleShape _ _ xsFldShps) xs, Mir.TyTuple ys, MS.SetupTuple () zs) ->
      sequence_
        [ case xFldShp of
            ReqField shp ->
              matchArg opts sc cc cs prepost md (MIRVal shp x) y z
            OptField shp -> do
              let x' = readMaybeType sym "field" (shapeType shp) x
              matchArg opts sc cc cs prepost md (MIRVal shp x') y z
        | (Some (Functor.Pair xFldShp (Crucible.RV x)), y, z) <-
            zip3 (FC.toListFC Some (Ctx.zipWith Functor.Pair xsFldShps xs))
                 ys
                 zs
        ]

    -- Match the parts of a slice point-wise
    (MIRVal (SliceShape _ actualElemTy actualMutbl actualElemTpr)
            (Ctx.Empty Ctx.:> Crucible.RV actualRef Ctx.:> Crucible.RV actualLen),
     Mir.TyRef (Mir.TySlice expectedElemTy) expectedMutbl,
     MS.SetupSlice slice) ->
      case slice of
        MirSetupSliceRaw{} ->
          panic "matchArg" ["SliceRaw not yet implemented"]

        MirSetupSlice expectedRef -> do
          actualRefTy <- typeOfSetupValue cc tyenv nameEnv expectedRef
          case actualRefTy of
            Mir.TyRef (Mir.TyArray _ expectedLen) _
              |  Just actualLenBV <- W4.asBV actualLen
              ,  BV.asUnsigned actualLenBV == toInteger expectedLen
              -> do let (actualRefShp, _actualLenShp) =
                          sliceShapeParts actualElemTy actualMutbl actualElemTpr
                    matchArg opts sc cc cs prepost md
                      (MIRVal actualRefShp actualRef)
                      (Mir.TyRef expectedElemTy expectedMutbl)
                      expectedRef

            _ -> fail_

        MirSetupSliceRange expectedRef expectedStart expectedEnd
          |  Just actualLenBV <- W4.asBV actualLen
          ,  BV.asUnsigned actualLenBV == toInteger (expectedEnd - expectedStart)
          -> do startBV <- liftIO $
                  W4.bvLit sym W4.knownNat $
                  BV.mkBV W4.knownNat $
                  toInteger expectedStart
                actualRef' <- liftIO $
                  Mir.mirRef_offsetIO bak iTypes actualElemTpr actualRef startBV
                let (actualRefShp, _actualLenShp) =
                      sliceShapeParts actualElemTy actualMutbl actualElemTpr
                matchArg opts sc cc cs prepost md
                  (MIRVal actualRefShp actualRef')
                  (Mir.TyRef expectedElemTy expectedMutbl)
                  expectedRef

          |  otherwise
          -> fail_

    (MIRVal (RefShape _ _ _ xTpr) x, Mir.TyRef _ _, MS.SetupGlobal () name) -> do
      static <- findStatic colState name
      Mir.StaticVar yGlobalVar <- findStaticVar colState (static ^. Mir.sName)
      let y = staticRefMux sym yGlobalVar
      case W4.testEquality xTpr (Crucible.globalType yGlobalVar) of
        Nothing -> fail_
        Just Refl -> do
          pred_ <- liftIO $
            Mir.mirRef_eqIO bak x y
          addAssert pred_ md =<< notEq
    (_, _, MS.SetupGlobalInitializer () name) -> do
      static <- findStatic colState name
      let staticTy = static ^. Mir.sTy
      unless (checkCompatibleTys expectedTy staticTy) fail_
      staticInitMirVal <- findStaticInitializer cc static
      pred_ <- liftIO $ equalValsPred cc staticInitMirVal actual
      addAssert pred_ md =<< notEq

    (_, _, MS.SetupNull empty)                -> absurd empty
    (_, _, MS.SetupCast empty _)              -> absurd empty
    (_, _, MS.SetupUnion empty _ _)           -> absurd empty

    _ -> fail_
  where
    colState = cc ^. mccRustModule . Mir.rmCS
    col      = colState ^. Mir.collection
    iTypes   = cc ^. mccIntrinsicTypes
    tyenv    = MS.csAllocations cs
    nameEnv  = MS.csTypeNames cs

    loc   = MS.conditionLoc md
    fail_ = failure loc =<<
              mkStructuralMismatch opts cc sc cs actual expected expectedTy
    notEq = notEqual prepost opts loc cc sc cs expected actual

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
        MS.SetupTuple _ xs                -> foldMap setupVars xs
        MS.SetupSlice slice               -> setupSlice slice
        MS.SetupArray _ xs                -> foldMap setupVars xs
        MS.SetupElem _ x _                -> setupVars x
        MS.SetupField _ x _               -> setupVars x
        MS.SetupTerm _                    -> Set.empty
        MS.SetupGlobal _ _                -> Set.empty
        MS.SetupGlobalInitializer _ _     -> Set.empty
        MS.SetupCast empty _              -> absurd empty
        MS.SetupUnion empty _ _           -> absurd empty
        MS.SetupNull empty                -> absurd empty

    -- Compute the set of variable identifiers in a 'MirSetupSlice'
    setupSlice :: MirSetupSlice -> Set AllocIndex
    setupSlice (MirSetupSliceRaw ref len) =
      setupVars ref <> setupVars len
    setupSlice (MirSetupSlice arr) =
      setupVars arr
    setupSlice (MirSetupSliceRange arr _start _end) =
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
          in runOverrideMatcher sym g0 Map.empty Map.empty initialFree (view MS.csLoc cs)
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
           IO (MIRVal, Mir.Ty, SetupValue)
         aux (argTy, setupVal) val =
           case decodeMIRVal col argTy val of
             Just val' -> return (val', argTy, setupVal)
             Nothing -> fail "unexpected type"

     -- todo: fail if list lengths mismatch
     xs <- liftIO (zipWithM aux expectedArgTypes (assignmentToList args))

     let md = MS.ConditionMetadata
              { MS.conditionLoc = cs ^. MS.csLoc
              , MS.conditionTags = mempty
              , MS.conditionType = "formal argument matching"
              , MS.conditionContext = ""
              }

     sequence_ [ matchArg opts sc cc cs MS.PreState md x y z | (x, y, z) <- xs]

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
  Mir.Ty     {- ^ the expected type -} ->
  OverrideMatcher MIR w (OverrideFailureReason MIR)
mkStructuralMismatch _opts cc _sc spec mirVal setupval mty = do
  let sym = cc^.mccSym
  setupTy <- typeOfSetupValueMIR cc spec setupval
  pure $ StructuralMismatch
            (ppMIRVal sym mirVal)
            (MS.ppSetupValue setupval)
            (Just setupTy)
            mty

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
  Sym ->
  MS.ConditionMetadata ->
  OverrideFailureReason MIR ->
  Cryptol.TValue ->
  MIRVal ->
  OverrideMatcher MIR w Term
valueToSC sym md failMsg tval (MIRVal shp val) =
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
              traverse (\v -> valueToSC sym md failMsg cryty (MIRVal arrShp v)) vals
            t <- shapeToTerm sc arrShp
            liftIO (scVectorReduced sc t terms)
      |  Mir.MirVector_PartialVector vals <- val
      ,  toInteger (V.length vals) == n
      -> do let vals' = V.toList $
                        V.map (readMaybeType sym "vector element" (shapeType arrShp)) vals
            terms <-
              traverse (\v -> valueToSC sym md failMsg cryty (MIRVal arrShp v)) vals'
            t <- shapeToTerm sc arrShp
            liftIO (scVectorReduced sc t terms)
      |  Mir.MirVector_Array{} <- val
      -> fail "valueToSC: Symbolic arrays not supported"
    _ ->
      failure (MS.conditionLoc md) failMsg
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
      valueToSC sym md failMsg ty mirVal
