{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeApplications #-}

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
  , decodeMIRVal
  , firstPointsToReferent
  ) where

import qualified Control.Exception as X
import Control.Lens
import Control.Monad.IO.Class (MonadIO(..))
import Data.Foldable (for_, traverse_)
import qualified Data.Functor.Product as Functor
import Data.List (tails)
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.Some (Some(..))
import qualified Data.Parameterized.TraversableFC as FC
import qualified Data.Set as Set
import qualified Data.Vector as V
import Data.Void (absurd)
import qualified Prettyprinter as PP

import qualified Cryptol.TypeCheck.AST as Cryptol
import qualified Cryptol.Eval.Type as Cryptol (TValue(..), evalType)
import qualified Lang.Crucible.Backend as Crucible
import qualified Lang.Crucible.Simulator as Crucible
import qualified Lang.Crucible.Types as Crucible
import qualified Mir.Generator as Mir
import qualified Mir.Intrinsics as Mir
import Mir.Intrinsics (MIR)
import qualified Mir.Mir as Mir
import qualified What4.Expr as W4
import qualified What4.Interface as W4
import qualified What4.Partial as W4
import qualified What4.ProgramLoc as W4

import Verifier.SAW.Prelude (scEq)
import Verifier.SAW.SharedTerm
import Verifier.SAW.Simulator.What4.ReturnTrip (saw_ctx, toSC)
import Verifier.SAW.TypedAST
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
import SAWScript.Utils (handleException)

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
  traverse_ assertTermEquality =<< OM (use termEqs)

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
     for_ old $ \(Some ref') ->
       do p <- liftIO (equalRefsPred cc ref ref')
          addAssert p md (Crucible.SimError loc (Crucible.AssertFailureSimError "equality of aliased references" ""))

assignTerm ::
  SharedContext      {- ^ context for constructing SAW terms    -} ->
  MIRCrucibleContext    {- ^ context for interacting with Crucible -} ->
  MS.ConditionMetadata ->
  MS.PrePost                                                          ->
  VarIndex {- ^ external constant index -} ->
  Term     {- ^ value                   -} ->
  OverrideMatcher MIR w ()

assignTerm sc cc md prepost var val =
  do mb <- OM (use (termSub . at var))
     case mb of
       Nothing -> OM (termSub . at var ?= val)
       Just old ->
         matchTerm sc cc md prepost val old

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

-- | @mir_points_to@ always creates a 'MirPointsTo' value with exactly one
-- referent on the right-hand side. As a result, this function should never
-- fail.
firstPointsToReferent ::
  MonadFail m => [MS.SetupValue MIR] -> m (MS.SetupValue MIR)
firstPointsToReferent referents =
  case referents of
    [referent] -> pure referent
    _ -> fail $
      "Unexpected mir_points_to statement with " ++ show (length referents) ++
      " referent(s)"

instantiateExtResolveSAWPred ::
  SharedContext ->
  MIRCrucibleContext ->
  Term ->
  OverrideMatcher MIR md (W4.Pred Sym)
instantiateExtResolveSAWPred sc cc cond = do
  sub <- OM (use termSub)
  liftIO $ resolveSAWPred cc =<< scInstantiateExt sc sub cond

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
    MS.SetupNull empty                -> absurd empty
    MS.SetupGlobal empty _            -> absurd empty
    MS.SetupStruct _ _                -> return v
    MS.SetupTuple x vs                -> MS.SetupTuple x <$> mapM (instantiateSetupValue sc s) vs
    MS.SetupArray elemTy vs           -> MS.SetupArray elemTy <$> mapM (instantiateSetupValue sc s) vs
    MS.SetupElem _ _ _                -> return v
    MS.SetupField _ _ _               -> return v
    MS.SetupCast empty _              -> absurd empty
    MS.SetupUnion empty _ _           -> absurd empty
    MS.SetupGlobalInitializer empty _ -> absurd empty
  where
    doTerm (TypedTerm schema t) = TypedTerm schema <$> scInstantiateExt sc s t

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
     traverse_ (learnSetupCondition opts sc cc cs prepost) (ss ^. MS.csConditions)
     assertTermEqualities sc cc
     enforceDisjointness cc loc ss
     enforceCompleteSubstitution loc ss

-- | Process a "crucible_equal" statement from the precondition
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
learnPointsTo opts sc cc spec prepost (MirPointsTo md allocIdx referents) =
  mccWithBackend cc $ \bak ->
  do let col = cc ^. mccRustModule . Mir.rmCS ^. Mir.collection
     globals <- OM (use overrideGlobals)
     Some mp <- resolveAllocIndexMIR allocIdx
     let mpMirTy = mp^.mpMirType
     let mpTpr = tyToShapeEq col mpMirTy (mp^.mpType)
     val <- firstPointsToReferent referents
     v <- liftIO $ Mir.readMirRefIO bak globals Mir.mirIntrinsicTypes (mp^.mpType) (mp^.mpRef)
     matchArg opts sc cc spec prepost md (MIRVal mpTpr v) mpMirTy val

-- | Process a "crucible_precond" statement from the precondition
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
learnSetupCondition opts sc cc spec prepost (MS.SetupCond_Equal md val1 val2)  = learnEqual opts sc cc spec md prepost val1 val2
learnSetupCondition _opts sc cc _    prepost (MS.SetupCond_Pred md tm)         = learnPred sc cc md prepost (ttTerm tm)
learnSetupCondition _opts _ _ _ _ (MS.SetupCond_Ghost empty _ _ _) = absurd empty

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
       matchTerm sc cc md prepost realTerm (ttTerm expectedTT)

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
        do xs'' <- liftIO $
             traverse (readMaybeType sym "vector element" (shapeType elemShp)) xs'
           sequence_
             [ matchArg opts sc cc cs prepost md (MIRVal elemShp x) y z
             | (x, z) <- zip (V.toList xs'') zs ]

    -- match the fields of a tuple point-wise
    (MIRVal (TupleShape _ _ xsFldShps) xs, Mir.TyTuple ys, MS.SetupTuple () zs) ->
      sequence_
        [ case xFldShp of
            ReqField shp ->
              matchArg opts sc cc cs prepost md (MIRVal shp x) y z
            OptField shp -> do
              x' <- liftIO $ readMaybeType sym "field" (shapeType shp) x
              matchArg opts sc cc cs prepost md (MIRVal shp x') y z
        | (Some (Functor.Pair xFldShp (Crucible.RV x)), y, z) <-
            zip3 (FC.toListFC Some (Ctx.zipWith Functor.Pair xsFldShps xs))
                 ys
                 zs
        ]

    (_, _, MS.SetupNull empty)                -> absurd empty
    (_, _, MS.SetupGlobal empty _)            -> absurd empty
    (_, _, MS.SetupCast empty _)              -> absurd empty
    (_, _, MS.SetupUnion empty _ _)           -> absurd empty
    (_, _, MS.SetupGlobalInitializer empty _) -> absurd empty

    _ -> failure (MS.conditionLoc md) =<<
           mkStructuralMismatch opts cc sc cs actual expected expectedTy

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
    checkPointsTo (MirPointsTo _ allocIdx _) = checkAllocIndex allocIdx

    checkAllocIndex :: AllocIndex -> OverrideMatcher MIR w Bool
    checkAllocIndex i =
      do m <- OM (use setupValueSub)
         return (Map.member i m)

matchTerm ::
  SharedContext   {- ^ context for constructing SAW terms    -} ->
  MIRCrucibleContext {- ^ context for interacting with Crucible -} ->
  MS.ConditionMetadata ->
  MS.PrePost                                                    ->
  Term            {- ^ exported concrete term                -} ->
  Term            {- ^ expected specification term           -} ->
  OverrideMatcher MIR md ()

matchTerm _ _ _ _ real expect | real == expect = return ()
matchTerm sc cc md prepost real expect =
  do let loc = MS.conditionLoc md
     free <- OM (use osFree)
     case unwrapTermF expect of
       FTermF (ExtCns ec)
         | Set.member (ecVarIndex ec) free ->
         do assignTerm sc cc md prepost (ecVarIndex ec) real

       _ ->
         do t <- liftIO $ scEq sc real expect
            let msg = unlines $
                  [ "Literal equality " ++ MS.stateCond prepost
--                  , "Expected term: " ++ prettyTerm expect
--                  , "Actual term:   " ++ prettyTerm real
                  ]
            addTermEq t md $ Crucible.SimError loc $ Crucible.AssertFailureSimError msg ""

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
mkStructuralMismatch _opts cc _sc spec (MIRVal shp _) setupval mty = do
  setupTy <- typeOfSetupValueMIR cc spec setupval
  pure $ StructuralMismatch
            (PP.pretty shp) -- TODO: Print the entire value, not just the type shape
            (MS.ppSetupValue setupval)
            (Just setupTy)
            mty

readMaybeType ::
     Crucible.IsSymInterface sym
  => sym
  -> String
  -> Crucible.TypeRepr tp
  -> Crucible.RegValue sym (Crucible.MaybeType tp)
  -> IO (Crucible.RegValue sym tp)
readMaybeType sym desc tpr rv =
  case readPartExprMaybe sym rv of
    Just x -> return x
    Nothing -> error $ "readMaybeType: accessed possibly-uninitialized " ++ desc ++
        " of type " ++ show tpr

readPartExprMaybe ::
     Crucible.IsSymInterface sym
  => sym
  -> W4.PartExpr (W4.Pred sym) a
  -> Maybe a
readPartExprMaybe _sym W4.Unassigned = Nothing
readPartExprMaybe _sym (W4.PE p v)
  | Just True <- W4.asConstantPred p = Just v
  | otherwise = Nothing

resolveAllocIndexMIR :: AllocIndex -> OverrideMatcher MIR w (Some (MirPointer Sym))
resolveAllocIndexMIR i =
  do m <- OM (use setupValueSub)
     pure $ lookupAllocIndex m i

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
      -> do vals' <- liftIO $ V.toList <$>
              traverse (readMaybeType sym "vector element" (shapeType arrShp)) vals
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
          OptField shp' -> do
            tm' <- liftIO $ readMaybeType sym "field" (shapeType shp') tm
            pure $ MIRVal shp' tm'
      valueToSC sym md failMsg ty mirVal
