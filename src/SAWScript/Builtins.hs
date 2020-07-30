{- |
Module      : SAWScript.Builtins
Description : Implementations of SAW-Script primitives.
License     : BSD3
Maintainer  : atomb
Stability   : provisional
-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE NondecreasingIndentation #-}
{-# LANGUAGE ImplicitParams #-}

module SAWScript.Builtins where

#if !MIN_VERSION_base(4,8,0)
import Data.Functor
import Control.Applicative
import Data.Monoid
#endif
import Control.Monad.State
import Control.Monad.Reader (ask)
import qualified Control.Exception as Ex
import qualified Data.ByteString as StrictBS
import qualified Data.ByteString.Lazy as BS
import qualified Data.ByteString.Lazy.UTF8 as B
import qualified Data.IntMap as IntMap
import Data.List (isPrefixOf, isInfixOf)
import qualified Data.Map as Map
import Data.Maybe
import Data.Time.Clock
import Data.Typeable
import System.Directory
import qualified System.Environment
import qualified System.Exit as Exit
import System.IO
import System.IO.Temp (withSystemTempFile, emptySystemTempFile)
import System.Process (callCommand, readProcessWithExitCode)
import Text.Printf (printf)
import Text.Read (readMaybe)

import What4.Expr(FloatModeRepr(..))

import qualified Verifier.SAW.Cryptol as Cryptol
import qualified Verifier.SAW.Cryptol.Simpset as Cryptol

-- saw-core
import Verifier.SAW.Grammar (parseSAWTerm)
import Verifier.SAW.ExternalFormat
import Verifier.SAW.FiniteValue
  ( FiniteType(..), readFiniteValue
  , FirstOrderValue(..)
  , toFirstOrderValue, scFirstOrderValue
  )
import Verifier.SAW.Prelude
import Verifier.SAW.SCTypeCheck hiding (TypedTerm)
import qualified Verifier.SAW.SCTypeCheck as TC (TypedTerm(..))
import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedTerm
import qualified Verifier.SAW.Simulator.Concrete as Concrete
import Verifier.SAW.Prim (rethrowEvalError)
import Verifier.SAW.Recognizer
import Verifier.SAW.Rewriter
import Verifier.SAW.Testing.Random (scRunTestsTFIO, scTestableType)
import Verifier.SAW.TypedAST

import SAWScript.Position

-- cryptol-verifier
import qualified Verifier.SAW.CryptolEnv as CEnv

-- saw-core-aig
import qualified Verifier.SAW.Simulator.BitBlast as BBSim

-- saw-core-sbv
import qualified Verifier.SAW.Simulator.SBV as SBVSim

-- saw-core-what4
import qualified Verifier.SAW.Simulator.What4 as W4Sim

-- parameterized-utils
import Data.Parameterized.Nonce

-- crucible-saw
import qualified Lang.Crucible.Backend.SAWCore as Crucible (newSAWCoreBackend, toSC)

-- sbv
import qualified Data.SBV.Dynamic as SBV

-- aig
import qualified Data.AIG as AIG

-- cryptol
import qualified Cryptol.ModuleSystem.Env as C (meSolverConfig)
import qualified Cryptol.TypeCheck as C (SolverConfig)
import qualified Cryptol.TypeCheck.AST as C
import qualified Cryptol.TypeCheck.PP as C (ppWithNames, pp, text, (<+>))
import qualified Cryptol.TypeCheck.Solve as C (defaultReplExpr)
import qualified Cryptol.TypeCheck.Solver.SMT as C (withSolver)
import qualified Cryptol.TypeCheck.Solver.InfNat as C (Nat'(..))
import qualified Cryptol.TypeCheck.Subst as C (Subst, apSubst, listSubst)
import qualified Cryptol.Eval.Monad as C (runEval)
import qualified Cryptol.Eval.Type as C (evalType)
import qualified Cryptol.Eval.Value as C (fromVBit, fromVWord)
import qualified Cryptol.Eval.Concrete.Value as C (Concrete(..), bvVal)
import qualified Cryptol.Utils.Ident as C (packIdent, packModName)
import qualified Cryptol.Utils.RecordMap as C (recordFromFields)
import Cryptol.Utils.PP (pretty)

import qualified SAWScript.SBVParser as SBV
import SAWScript.ImportAIG

import SAWScript.AST (getVal, pShow, Located(..))
import SAWScript.Options as Opts
import SAWScript.Proof
import SAWScript.TopLevel
import qualified SAWScript.Value as SV
import SAWScript.Value (ProofScript, printOutLnTop, AIGNetwork)

import SAWScript.Prover.Util(checkBooleanSchema,liftCexBB)
import SAWScript.Prover.SolverStats
import SAWScript.Prover.Rewrite(rewriteEqs)
import qualified SAWScript.Prover.SBV as Prover
import qualified SAWScript.Prover.RME as Prover
import qualified SAWScript.Prover.ABC as Prover
import qualified SAWScript.Prover.What4 as Prover
import qualified SAWScript.Prover.Exporter as Prover
import qualified SAWScript.Prover.MRSolver as Prover

showPrim :: SV.Value -> TopLevel String
showPrim v = do
  opts <- fmap rwPPOpts getTopLevelRW
  return (SV.showsPrecValue opts 0 v "")

definePrim :: String -> TypedTerm -> TopLevel TypedTerm
definePrim name (TypedTerm schema rhs) =
  do sc <- getSharedContext
     ty <- io $ Cryptol.importSchema sc Cryptol.emptyEnv schema
     t <- io $ scConstant sc name rhs ty
     return $ TypedTerm schema t

sbvUninterpreted :: String -> Term -> TopLevel Uninterp
sbvUninterpreted s t = return $ Uninterp (s, t)

readBytes :: FilePath -> TopLevel TypedTerm
readBytes path = do
  sc <- getSharedContext
  content <- io $ BS.readFile path
  let len = BS.length content
  let bytes = BS.unpack content
  e <- io $ scBitvector sc 8
  xs <- io $ mapM (scBvConst sc 8 . toInteger) bytes
  trm <- io $ scVector sc e xs
  let schema = C.Forall [] [] (C.tSeq (C.tNum len) (C.tSeq (C.tNum (8::Int)) C.tBit))
  return (TypedTerm schema trm)

readSBV :: FilePath -> [Uninterp] -> TopLevel TypedTerm
readSBV path unintlst =
    do sc <- getSharedContext
       opts <- getOptions
       pgm <- io $ SBV.loadSBV path
       let schema = C.Forall [] [] (toCType (SBV.typOf pgm))
       trm <- io $ SBV.parseSBVPgm opts sc (\s _ -> Map.lookup s unintmap) pgm
       when (extraChecks opts) $ do
         tcr <- io $ scTypeCheck sc Nothing trm
         case tcr of
           Left err ->
             printOutLnTop Error $ unlines $
             ("Type error reading " ++ path ++ ":") : prettyTCError err
           Right _ -> return () -- TODO: check that it matches 'schema'?
       return (TypedTerm schema trm)
    where
      unintmap = Map.fromList $ map getUninterp unintlst

      toCType :: SBV.Typ -> C.Type
      toCType typ =
        case typ of
          SBV.TBool      -> C.tBit
          SBV.TFun t1 t2 -> C.tFun (toCType t1) (toCType t2)
          SBV.TVec n t   -> C.tSeq (C.tNum n) (toCType t)
          SBV.TTuple ts  -> C.tTuple (map toCType ts)
          SBV.TRecord bs -> C.tRec (C.recordFromFields [ (C.packIdent n, toCType t) | (n, t) <- bs ])



-- | Use ABC's 'dsec' command to equivalence check to terms
-- representing SAIGs. Note that nothing is returned; you must read
-- the output to see what happened.
--
-- TODO: this is a first version. The interface can be improved later,
-- but I don't want too worry to much about generalization before I
-- have more examples. It might be an improvement to take SAIGs as
-- arguments, in the style of 'cecPrim' below. This would require
-- support for latches in the 'AIGNetwork' SAWScript type.
dsecPrint :: SharedContext -> TypedTerm -> TypedTerm -> TopLevel ()
dsecPrint sc t1 t2 = SV.getProxy >>= \(SV.AIGProxy proxy) -> liftIO $ do
  withSystemTempFile ".aig" $ \path1 _handle1 -> do
  withSystemTempFile ".aig" $ \path2 _handle2 -> do
  Prover.writeSAIGInferLatches proxy sc path1 t1
  Prover.writeSAIGInferLatches proxy sc path2 t2
  callCommand (abcDsec path1 path2)
  where
    -- The '-w' here may be overkill ...
    abcDsec path1 path2 = printf "abc -c 'read %s; dsec -v -w %s;'" path1 path2

cecPrim :: AIGNetwork -> AIGNetwork -> TopLevel SV.ProofResult
cecPrim (SV.AIGNetwork x) (SV.AIGNetwork y) = do
  y' <- case cast y of
          Just n -> return n
          Nothing -> fail "Inconsistent AIG types"
  io $ verifyAIGCompatible x y'
  res <- io $ AIG.cec x y'
  let stats = solverStats "ABC" 0 -- TODO, count the size of the networks...
  case res of
    AIG.Valid -> return $ SV.Valid stats
    AIG.Invalid bs
      | Just fv <- readFiniteValue (FTVec (fromIntegral (length bs)) FTBit) bs ->
           return $ SV.InvalidMulti stats [("x", toFirstOrderValue fv)]
      | otherwise -> fail "cec: impossible, could not parse counterexample"
    AIG.VerifyUnknown -> fail "cec: unknown result "

bbPrim :: TypedTerm -> TopLevel AIGNetwork
bbPrim t = do
  SV.AIGProxy proxy <- SV.getProxy
  sc <- SV.getSharedContext
  aig <- io $ Prover.bitblastPrim proxy sc (ttTerm t)
  return (SV.AIGNetwork aig)

loadAIGPrim :: FilePath -> TopLevel AIGNetwork
loadAIGPrim f = do
  SV.AIGProxy proxy <- SV.getProxy
  exists <- io $ doesFileExist f
  unless exists $ fail $ "AIG file " ++ f ++ " not found."
  et <- io $ loadAIG proxy f
  case et of
    Left err -> fail $ "Reading AIG failed: " ++ err
    Right ntk -> return (SV.AIGNetwork ntk)

saveAIGPrim :: String -> AIGNetwork -> TopLevel ()
saveAIGPrim f (SV.AIGNetwork n) = io $ AIG.writeAiger f n

saveAIGasCNFPrim :: String -> AIGNetwork -> TopLevel ()
saveAIGasCNFPrim f (SV.AIGNetwork (AIG.Network be ls)) =
  case ls of
    [l] -> do _ <- io $ AIG.writeCNF be l f
              return ()
    _ -> fail "save_aig_as_cnf: non-boolean term"

-- | Read an AIG file representing a theorem or an arbitrary function
-- and represent its contents as a @Term@ lambda term. This is
-- inefficient but semantically correct.
readAIGPrim :: FilePath -> TopLevel TypedTerm
readAIGPrim f = do
  sc <- getSharedContext
  SV.AIGProxy proxy <- SV.getProxy
  exists <- io $ doesFileExist f
  unless exists $ fail $ "AIG file " ++ f ++ " not found."
  opts <- getOptions
  et <- io $ readAIG proxy opts sc f
  case et of
    Left err -> fail $ "Reading AIG failed: " ++ err
    Right t -> io $ mkTypedTerm sc t

replacePrim :: TypedTerm -> TypedTerm -> TypedTerm -> TopLevel TypedTerm
replacePrim pat replace t = do
  sc <- getSharedContext

  let tpat  = ttTerm pat
  let trepl = ttTerm replace

  let fvpat = looseVars tpat
  let fvrepl = looseVars trepl

  unless (fvpat == emptyBitSet) $ fail $ unlines
    [ "pattern term is not closed", show tpat ]

  unless (fvrepl == emptyBitSet) $ fail $ unlines
    [ "replacement term is not closed", show trepl ]

  io $ do
    ty1 <- scTypeOf sc tpat
    ty2 <- scTypeOf sc trepl
    c <- scConvertible sc False ty1 ty2
    unless c $ fail $ unlines
      [ "terms do not have convertible types", show tpat, show ty1, show trepl, show ty2 ]

  let ss = emptySimpset
  t' <- io $ replaceTerm sc ss (tpat, trepl) (ttTerm t)

  io $ do
    ty  <- scTypeOf sc (ttTerm t)
    ty' <- scTypeOf sc t'
    c' <- scConvertible sc False ty ty'
    unless c' $ fail $ unlines
      [ "term does not have the same type after replacement", show ty, show ty' ]

  return t{ ttTerm = t' }


hoistIfsPrim :: TypedTerm -> TopLevel TypedTerm
hoistIfsPrim t = do
  sc <- getSharedContext
  t' <- io $ hoistIfs sc (ttTerm t)

  io $ do
    ty  <- scTypeOf sc (ttTerm t)
    ty' <- scTypeOf sc t'
    c' <- scConvertible sc False ty ty'
    unless c' $ fail $ unlines
      [ "term does not have the same type after hoisting ifs", show ty, show ty' ]

  return t{ ttTerm = t' }

checkConvertiblePrim :: TypedTerm -> TypedTerm -> TopLevel ()
checkConvertiblePrim x y = do
   sc <- getSharedContext
   str <- io $ do
     c <- scConvertible sc False (ttTerm x) (ttTerm y)
     pure (if c
            then "Convertible"
            else "Not convertible")
   printOutLnTop Info str


readCore :: FilePath -> TopLevel TypedTerm
readCore path = do
  sc <- getSharedContext
  io (mkTypedTerm sc =<< scReadExternal sc =<< readFile path)

withFirstGoal :: (ProofGoal -> TopLevel (a, SolverStats, Maybe ProofGoal)) -> ProofScript a
withFirstGoal f =
  StateT $ \(ProofState goals concl stats timeout) ->
  case goals of
    [] -> fail "ProofScript failed: no subgoal"
    g : gs -> do
      (x, stats', mg') <- f g
      case mg' of
        Nothing -> return (x, ProofState gs concl (stats <> stats') timeout)
        Just g' -> return (x, ProofState (g' : gs) concl (stats <> stats') timeout)

quickcheckGoal :: SharedContext -> Integer -> ProofScript SV.SatResult
quickcheckGoal sc n = do
  opts <- Control.Monad.State.lift getOptions
  withFirstGoal $ \goal -> io $ do
    printOutLn opts Warn $ "WARNING: using quickcheck to prove goal..."
    hFlush stdout
    tm0 <- propToPredicate sc (goalProp goal)
    tm <- scAbstractExts sc (getAllExts tm0) tm0
    ty <- scTypeOf sc tm
    maybeInputs <- scTestableType sc ty
    let stats = solverStats "quickcheck" (scSharedSize tm)
    case maybeInputs of
      Just inputs -> do
        result <- scRunTestsTFIO sc n tm inputs
        case result of
          Nothing -> do
            printOutLn opts Info $ "checked " ++ show n ++ " cases."
            return (SV.Unsat stats, stats, Nothing)
          -- TODO: use reasonable names here
          Just cex -> return (SV.SatMulti stats (zip (repeat "_") (map toFirstOrderValue cex)), stats, Just goal)
      Nothing -> fail $ "quickcheck:\n" ++
        "term has non-testable type:\n" ++
        showTerm ty ++ ", for term: " ++ showTerm tm

assumeValid :: ProofScript SV.ProofResult
assumeValid =
  withFirstGoal $ \goal ->
  do printOutLnTop Warn $ "WARNING: assuming goal " ++ goalName goal ++ " is valid"
     let stats = solverStats "ADMITTED" (scSharedSize (unProp (goalProp goal)))
     return (SV.Valid stats, stats, Nothing)

assumeUnsat :: ProofScript SV.SatResult
assumeUnsat =
  withFirstGoal $ \goal ->
  do printOutLnTop Warn $ "WARNING: assuming goal " ++ goalName goal ++ " is unsat"
     let stats = solverStats "ADMITTED" (scSharedSize (unProp (goalProp goal)))
     return (SV.Unsat stats, stats, Nothing)

trivial :: ProofScript SV.SatResult
trivial =
  withFirstGoal $ \goal ->
  do checkTrue (unProp (goalProp goal))
     return (SV.Unsat mempty, mempty, Nothing)
  where
    checkTrue :: Term -> TopLevel ()
    checkTrue (asPiList -> (_, asEqTrue -> Just (asBool -> Just True))) = return ()
    checkTrue _ = fail "trivial: not a trivial goal"

split_goal :: ProofScript ()
split_goal =
  StateT $ \(ProofState goals concl stats timeout) ->
  case goals of
    [] -> fail "ProofScript failed: no subgoal"
    (ProofGoal num ty name (Prop prop)) : gs ->
      let (vars, body) = asPiList prop in
      case (isGlobalDef "Prelude.and" <@> return <@> return) =<< asEqTrue body of
        Nothing -> fail "split_goal: goal not of form 'Prelude.and _ _'"
        Just (_ :*: p1 :*: p2) ->
          do sc <- getSharedContext
             t1 <- io $ scPiList sc vars =<< scEqTrue sc p1
             t2 <- io $ scPiList sc vars =<< scEqTrue sc p2
             let g1 = ProofGoal num (ty ++ ".left") name (Prop t1)
             let g2 = ProofGoal num (ty ++ ".right") name (Prop t2)
             return ((), ProofState (g1 : g2 : gs) concl stats timeout)

getTopLevelPPOpts :: TopLevel PPOpts
getTopLevelPPOpts = do
  opts <- fmap rwPPOpts getTopLevelRW
  return (SV.sawPPOpts opts)

show_term :: Term -> TopLevel String
show_term t = do
  opts <- getTopLevelPPOpts
  return (scPrettyTerm opts t)

print_term :: Term -> TopLevel ()
print_term t = do
  opts <- getTopLevelPPOpts
  printOutLnTop Info (scPrettyTerm opts t)

print_term_depth :: Int -> Term -> TopLevel ()
print_term_depth d t = do
  opts <- getTopLevelPPOpts
  let opts' = opts { ppMaxDepth = Just d }
  printOutLnTop Info $ show (scPrettyTerm opts' t)

print_goal :: ProofScript ()
print_goal =
  withFirstGoal $ \goal ->
  do opts <- getTopLevelPPOpts
     printOutLnTop Info ("Goal " ++ goalName goal ++ ":")
     printOutLnTop Info (scPrettyTerm opts (unProp (goalProp goal)))
     return ((), mempty, Just goal)

print_goal_depth :: Int -> ProofScript ()
print_goal_depth n =
  withFirstGoal $ \goal ->
  do opts <- getTopLevelPPOpts
     let opts' = opts { ppMaxDepth = Just n }
     printOutLnTop Info ("Goal " ++ goalName goal ++ ":")
     printOutLnTop Info $ scPrettyTerm opts' (unProp (goalProp goal))
     return ((), mempty, Just goal)

printGoalConsts :: ProofScript ()
printGoalConsts =
  withFirstGoal $ \goal ->
  do mapM_ (printOutLnTop Info) $ Map.keys (getConstantSet (unProp (goalProp goal)))
     return ((), mempty, Just goal)

printGoalSize :: ProofScript ()
printGoalSize =
  withFirstGoal $ \goal ->
  do let Prop t = goalProp goal
     printOutLnTop Info $ "Goal shared size: " ++ show (scSharedSize t)
     printOutLnTop Info $ "Goal unshared size: " ++ show (scTreeSize t)
     return ((), mempty, Just goal)

unfoldGoal :: [String] -> ProofScript ()
unfoldGoal names =
  withFirstGoal $ \goal ->
  do sc <- getSharedContext
     let Prop trm = goalProp goal
     trm' <- io $ scUnfoldConstants sc names trm
     return ((), mempty, Just (goal { goalProp = Prop trm' }))

simplifyGoal :: Simpset -> ProofScript ()
simplifyGoal ss =
  withFirstGoal $ \goal ->
  do sc <- getSharedContext
     let Prop trm = goalProp goal
     trm' <- io $ rewriteSharedTerm sc ss trm
     return ((), mempty, Just (goal { goalProp = Prop trm' }))

goal_eval :: [String] -> ProofScript ()
goal_eval unints =
  withFirstGoal $ \goal ->
  do sc <- getSharedContext
     t0 <- liftIO $ propToPredicate sc (goalProp goal)
     let gen = globalNonceGenerator
     sym <- liftIO $ Crucible.newSAWCoreBackend FloatRealRepr sc gen
     (_names, (_mlabels, p)) <- liftIO $ W4Sim.w4Eval sym sc Map.empty unints t0
     t1 <- liftIO $ Crucible.toSC sym p
     t2 <- liftIO $ scEqTrue sc t1
     return ((), mempty, Just (goal { goalProp = Prop t2 }))

beta_reduce_goal :: ProofScript ()
beta_reduce_goal =
  withFirstGoal $ \goal ->
  do sc <- getSharedContext
     let Prop trm = goalProp goal
     trm' <- io $ betaNormalize sc trm
     return ((), mempty, Just (goal { goalProp = Prop trm' }))

goal_apply :: Theorem -> ProofScript ()
goal_apply (Theorem (Prop rule)) =
  StateT $ \(ProofState goals concl stats timeout) ->
  case goals of
    [] -> fail "goal_apply failed: no subgoal"
    goal : goals' ->
      do sc <- getSharedContext
         let applyFirst [] = fail "goal_apply failed: no match"
             applyFirst ((ruleArgs, ruleConcl) : rest) =
               do result <- io $ scMatch sc ruleConcl (unProp (goalProp goal))
                  case result of
                    Nothing -> applyFirst rest
                    Just inst ->
                      do let inst' = [ Map.lookup i inst | i <- take (length ruleArgs) [0..] ]
                         dummy <- io $ scUnitType sc
                         let mkNewGoals (Nothing : mts) ((_, prop) : args) =
                               do c0 <- instantiateVarList sc 0 (map (fromMaybe dummy) mts) prop
                                  cs <- mkNewGoals mts args
                                  return (Prop c0 : cs)
                             mkNewGoals (Just _ : mts) (_ : args) =
                               mkNewGoals mts args
                             mkNewGoals _ _ = return []
                         newgoalterms <- io $ mkNewGoals inst' (reverse ruleArgs)
                         let newgoals = reverse [ goal { goalProp = t } | t <- newgoalterms ]
                         return ((), ProofState (newgoals ++ goals') concl stats timeout)
         applyFirst (asPiLists rule)
  where
    asPiLists :: Term -> [([(String, Term)], Term)]
    asPiLists t =
      case asPi t of
        Nothing -> [([], t)]
        Just (nm, tp, body) ->
          [ ((nm, tp) : args, concl) | (args, concl) <- asPiLists body ] ++ [([], t)]

goal_assume :: ProofScript Theorem
goal_assume =
  StateT $ \(ProofState goals concl stats timeout) ->
  case goals of
    [] -> fail "goal_assume failed: no subgoal"
    goal : goals' ->
      case asPi (unProp (goalProp goal)) of
        Nothing -> fail "goal_assume failed: not a pi type"
        Just (_nm, tp, body)
          | looseVars body /= emptyBitSet -> fail "goal_assume failed: dependent pi type"
          | otherwise ->
            let goal' = goal { goalProp = Prop body } in
            return (Theorem (Prop tp), ProofState (goal' : goals') concl stats timeout)

goal_intro :: String -> ProofScript TypedTerm
goal_intro s =
  StateT $ \(ProofState goals concl stats timeout) ->
  case goals of
    [] -> fail "goal_intro failed: no subgoal"
    goal : goals' ->
      case asPi (unProp (goalProp goal)) of
        Nothing -> fail "goal_intro failed: not a pi type"
        Just (nm, tp, body) ->
          do let name = if null s then nm else s
             sc <- SV.getSharedContext
             x <- io $ scFreshGlobal sc name tp
             tt <- io $ mkTypedTerm sc x
             body' <- io $ instantiateVar sc 0 x body
             let goal' = goal { goalProp = Prop body' }
             return (tt, ProofState (goal' : goals') concl stats timeout)

goal_insert :: Theorem -> ProofScript ()
goal_insert (Theorem (Prop t)) =
  StateT $ \(ProofState goals concl stats timeout) ->
  case goals of
    [] -> fail "goal_insert failed: no subgoal"
    goal : goals' ->
      do sc <- SV.getSharedContext
         body' <- io $ scFun sc t (unProp (goalProp goal))
         let goal' = goal { goalProp = Prop body' }
         return ((), ProofState (goal' : goals') concl stats timeout)

goal_when :: String -> ProofScript () -> ProofScript ()
goal_when str script =
  StateT $ \s ->
  case psGoals s of
    g : _ | str `isInfixOf` goalName g -> runStateT script s
    _ -> return ((), s)

-- | Bit-blast a proposition and check its validity using ABC.
proveABC :: ProofScript SV.SatResult
proveABC = do
  SV.AIGProxy proxy <- lift SV.getProxy
  wrapProver (Prover.proveABC proxy)

parseDimacsSolution :: [Int]    -- ^ The list of CNF variables to return
                    -> [String] -- ^ The value lines from the solver
                    -> [Bool]
parseDimacsSolution vars ls = map lkup vars
  where
    vs :: [Int]
    vs = concatMap (filter (/= 0) . mapMaybe readMaybe . tail . words) ls
    varToPair n | n < 0 = (-n, False)
                | otherwise = (n, True)
    assgnMap = Map.fromList (map varToPair vs)
    lkup v = Map.findWithDefault False v assgnMap

satExternal :: Bool -> String -> [String] -> ProofScript SV.SatResult
satExternal doCNF execName args = withFirstGoal $ \g -> do
  sc <- SV.getSharedContext
  SV.AIGProxy proxy <- SV.getProxy
  io $ do
  t0 <- propToPredicate sc (goalProp g)
  t <- rewriteEqs sc t0
  let cnfName = goalType g ++ show (goalNum g) ++ ".cnf"
  (path, fh) <- openTempFile "." cnfName
  hClose fh -- Yuck. TODO: allow writeCNF et al. to work on handles.
  let args' = map replaceFileName args
      replaceFileName "%f" = path
      replaceFileName a = a
  BBSim.withBitBlastedPred proxy sc mempty t $ \be l0 shapes -> do
  -- negate formula to turn it into an existentially-quantified SAT query
  let l = AIG.not l0
  variables <- (if doCNF then AIG.writeCNF else writeAIGWithMapping) be l path
  (_ec, out, err) <- readProcessWithExitCode execName args' ""
  removeFile path
  unless (null err) $
    print $ unlines ["Standard error from SAT solver:", err]
  let ls = lines out
      sls = filter ("s " `isPrefixOf`) ls
      vls = filter ("v " `isPrefixOf`) ls
  ft <- Prop <$> (scEqTrue sc =<< scApplyPrelude_False sc)
  let stats = solverStats ("external SAT:" ++ execName) (scSharedSize t)
  case (sls, vls) of
    (["s SATISFIABLE"], _) -> do
      let bs = parseDimacsSolution variables vls
      let r = liftCexBB (map snd shapes) bs
          argNames = map fst shapes
      case r of
        Left msg -> fail $ "Can't parse counterexample: " ++ msg
        Right vs
          | length argNames == length vs -> do
            let r' = SV.SatMulti stats (zip argNames (map toFirstOrderValue vs))
            return (r', stats, Just (g { goalProp = ft }))
          | otherwise -> fail $ unwords ["external SAT results do not match expected arguments", show argNames, show vs]
    (["s UNSATISFIABLE"], []) ->
      return (SV.Unsat stats, stats, Nothing)
    _ -> fail $ "Unexpected result from SAT solver:\n" ++ out

writeAIGWithMapping :: AIG.IsAIG l g => g s -> l s -> FilePath -> IO [Int]
writeAIGWithMapping be l path = do
  nins <- AIG.inputCount be
  AIG.writeAiger path (AIG.Network be [l])
  return [1..nins]

writeAIGPrim :: FilePath -> Term -> TopLevel ()
writeAIGPrim f t = do
  SV.AIGProxy proxy <- SV.getProxy
  sc <- SV.getSharedContext
  liftIO $ Prover.writeAIG proxy sc f t

writeSAIGPrim :: FilePath -> TypedTerm -> TopLevel ()
writeSAIGPrim f t = do
  SV.AIGProxy proxy <- SV.getProxy
  sc <- SV.getSharedContext
  liftIO $ Prover.writeSAIGInferLatches proxy sc f t

writeSAIGComputedPrim :: FilePath -> Term -> Int -> TopLevel ()
writeSAIGComputedPrim f t n = do
  SV.AIGProxy proxy <- SV.getProxy
  sc <- SV.getSharedContext
  liftIO $ Prover.writeSAIG proxy sc f t n

-- | Bit-blast a proposition check its validity using the RME library.
proveRME :: ProofScript SV.SatResult
proveRME = wrapProver Prover.proveRME

codegenSBV :: SharedContext -> FilePath -> [String] -> String -> TypedTerm -> IO ()
codegenSBV sc path unints fname (TypedTerm _schema t) =
  SBVSim.sbvCodeGen sc mempty unints mpath fname t
  where mpath = if null path then Nothing else Just path


-- | Bit-blast a proposition and check its validity using SBV.
-- (Currently ignores satisfying assignments.)
proveSBV :: SBV.SMTConfig -> ProofScript SV.SatResult
proveSBV conf = proveUnintSBV conf []

-- | Bit-blast a proposition and check its validity using SBV.
-- (Currently ignores satisfying assignments.) Constants with names in
-- @unints@ are kept as uninterpreted functions.
proveUnintSBV :: SBV.SMTConfig -> [String] -> ProofScript SV.SatResult
proveUnintSBV conf unints =
  do timeout <- psTimeout <$> get
     wrapProver (Prover.proveUnintSBV conf unints timeout)



wrapProver ::
  ( SharedContext ->
    Prop -> IO (Maybe [(String, FirstOrderValue)], SolverStats)) ->
  ProofScript SV.SatResult
wrapProver f = do
  sc <- lift $ SV.getSharedContext
  withFirstGoal $ \g -> do

  (mb, stats) <- io $ f sc (goalProp g)

  let nope r = do ft <- io $ scEqTrue sc =<< scApplyPrelude_False sc
                  return (r, stats, Just g { goalProp = Prop ft })

  case mb of
    Nothing -> return (SV.Unsat stats, stats, Nothing)
    Just a  -> nope (SV.SatMulti stats a)

wrapW4Prover ::
  ( SharedContext -> Bool ->
    Prop -> IO (Maybe [(String, FirstOrderValue)], SolverStats)) ->
  ProofScript SV.SatResult
wrapW4Prover f = do
  hashConsing <- lift $ gets SV.rwWhat4HashConsing
  wrapProver $ \sc -> f sc hashConsing

--------------------------------------------------
proveBoolector :: ProofScript SV.SatResult
proveBoolector = proveSBV SBV.boolector

proveZ3 :: ProofScript SV.SatResult
proveZ3 = proveSBV SBV.z3

proveCVC4 :: ProofScript SV.SatResult
proveCVC4 = proveSBV SBV.cvc4

proveMathSAT :: ProofScript SV.SatResult
proveMathSAT = proveSBV SBV.mathSAT

proveYices :: ProofScript SV.SatResult
proveYices = proveSBV SBV.yices

proveUnintBoolector :: [String] -> ProofScript SV.SatResult
proveUnintBoolector = proveUnintSBV SBV.boolector

proveUnintZ3 :: [String] -> ProofScript SV.SatResult
proveUnintZ3 = proveUnintSBV SBV.z3

proveUnintCVC4 :: [String] -> ProofScript SV.SatResult
proveUnintCVC4 = proveUnintSBV SBV.cvc4

proveUnintMathSAT :: [String] -> ProofScript SV.SatResult
proveUnintMathSAT = proveUnintSBV SBV.mathSAT

proveUnintYices :: [String] -> ProofScript SV.SatResult
proveUnintYices = proveUnintSBV SBV.yices


--------------------------------------------------
w4_boolector :: ProofScript SV.SatResult
w4_boolector = wrapW4Prover $ Prover.proveWhat4_boolector []

w4_z3 :: ProofScript SV.SatResult
w4_z3 = wrapW4Prover $ Prover.proveWhat4_z3 []

w4_cvc4 :: ProofScript SV.SatResult
w4_cvc4 = wrapW4Prover $ Prover.proveWhat4_cvc4 []

w4_yices :: ProofScript SV.SatResult
w4_yices = wrapW4Prover $ Prover.proveWhat4_yices []

w4_unint_boolector :: [String] -> ProofScript SV.SatResult
w4_unint_boolector = wrapW4Prover . Prover.proveWhat4_boolector

w4_unint_z3 :: [String] -> ProofScript SV.SatResult
w4_unint_z3 = wrapW4Prover . Prover.proveWhat4_z3

w4_unint_cvc4 :: [String] -> ProofScript SV.SatResult
w4_unint_cvc4 = wrapW4Prover . Prover.proveWhat4_cvc4

w4_unint_yices :: [String] -> ProofScript SV.SatResult
w4_unint_yices = wrapW4Prover . Prover.proveWhat4_yices

proveWithExporter ::
  (SharedContext -> FilePath -> Prop -> IO ()) ->
  String ->
  String ->
  ProofScript SV.SatResult
proveWithExporter exporter path ext =
  withFirstGoal $ \g ->
  do let file = path ++ "." ++ goalType g ++ show (goalNum g) ++ ext
     sc <- SV.getSharedContext
     stats <- io $ Prover.proveWithExporter exporter file sc (goalProp g)
     return (SV.Unsat stats, stats, Nothing)

offline_aig :: FilePath -> ProofScript SV.SatResult
offline_aig path = do
  SV.AIGProxy proxy <- lift $ SV.getProxy
  proveWithExporter (Prover.adaptExporter (Prover.writeAIG proxy)) path ".aig"

offline_cnf :: FilePath -> ProofScript SV.SatResult
offline_cnf path = do
  SV.AIGProxy proxy <- lift $ SV.getProxy
  proveWithExporter (Prover.adaptExporter (Prover.writeCNF proxy)) path ".cnf"

offline_coq :: FilePath -> ProofScript SV.SatResult
offline_coq path = proveWithExporter (const (Prover.writeCoqProp "goal" [] [])) path ".v"

offline_extcore :: FilePath -> ProofScript SV.SatResult
offline_extcore path = proveWithExporter (const Prover.writeCoreProp) path ".extcore"

offline_smtlib2 :: FilePath -> ProofScript SV.SatResult
offline_smtlib2 path = proveWithExporter Prover.writeSMTLib2 path ".smt2"

offline_unint_smtlib2 :: [String] -> FilePath -> ProofScript SV.SatResult
offline_unint_smtlib2 unints path = proveWithExporter (Prover.writeUnintSMTLib2 unints) path ".smt2"

set_timeout :: Integer -> ProofScript ()
set_timeout to = modify (\ps -> ps { psTimeout = Just to })

-- | Translate a @Term@ representing a theorem for input to the
-- given validity-checking script and attempt to prove it.
provePrim :: ProofScript SV.SatResult
          -> TypedTerm -> TopLevel SV.ProofResult
provePrim script t = do
  io $ checkBooleanSchema (ttSchema t)
  sc <- getSharedContext
  goal <- io $ makeProofGoal sc Universal 0 "prove" "prove" (ttTerm t)
  (r, pstate) <- runStateT script (startProof goal)
  case finishProof pstate of
    (_stats, Just _)  -> return ()
    (_stats, Nothing) -> printOutLnTop Info $ "prove: " ++ show (length (psGoals pstate)) ++ " unsolved subgoal(s)"
  return (SV.flipSatResult r)

provePrintPrim :: ProofScript SV.SatResult
               -> TypedTerm -> TopLevel Theorem
provePrintPrim script t = do
  sc <- getSharedContext
  goal <- io $ makeProofGoal sc Universal 0 "prove" "prove" (ttTerm t)
  (r, pstate) <- runStateT script (startProof goal)
  opts <- rwPPOpts <$> getTopLevelRW
  case finishProof pstate of
    (_,Just thm) -> do printOutLnTop Info "Valid"
                       return thm
    (_,Nothing) -> fail $ "prove: " ++ show (length (psGoals pstate)) ++ " unsolved subgoal(s)\n"
                     ++ SV.showsProofResult opts (SV.flipSatResult r) ""

satPrim :: ProofScript SV.SatResult -> TypedTerm
        -> TopLevel SV.SatResult
satPrim script t =
  do io $ checkBooleanSchema (ttSchema t)
     sc <- getSharedContext
     goal <- io $ makeProofGoal sc Existential 0 "sat" "sat" (ttTerm t)
     evalStateT script (startProof goal)

satPrintPrim :: ProofScript SV.SatResult
             -> TypedTerm -> TopLevel ()
satPrintPrim script t = do
  result <- satPrim script t
  opts <- rwPPOpts <$> getTopLevelRW
  printOutLnTop Info (SV.showsSatResult opts result "")

-- | Quick check (random test) a term and print the result. The
-- 'Integer' parameter is the number of random tests to run.
quickCheckPrintPrim :: Options -> SharedContext -> Integer -> TypedTerm -> IO ()
quickCheckPrintPrim opts sc numTests tt = do
  let tm = ttTerm tt
  ty <- scTypeOf sc tm
  maybeInputs <- scTestableType sc ty
  case maybeInputs of
    Just inputs -> do
      result <- scRunTestsTFIO sc numTests tm inputs
      case result of
        Nothing -> printOutLn opts Info $ "All " ++ show numTests ++ " tests passed!"
        Just counterExample -> printOutLn opts OnlyCounterExamples $
          "----------Counterexample----------\n" ++
          showList counterExample ""
    Nothing -> fail $ "quickCheckPrintPrim:\n" ++
      "term has non-testable type:\n" ++
      pretty (ttSchema tt)

cryptolSimpset :: TopLevel Simpset
cryptolSimpset =
  do sc <- getSharedContext
     io $ Cryptol.mkCryptolSimpset sc

addPreludeEqs :: [String] -> Simpset
              -> TopLevel Simpset
addPreludeEqs names ss = do
  sc <- getSharedContext
  eqRules <- io $ mapM (scEqRewriteRule sc) (map qualify names)
  return (addRules eqRules ss)
    where qualify = mkIdent (mkModuleName ["Prelude"])

addCryptolEqs :: [String] -> Simpset
              -> TopLevel Simpset
addCryptolEqs names ss = do
  sc <- getSharedContext
  eqRules <- io $ mapM (scEqRewriteRule sc) (map qualify names)
  return (addRules eqRules ss)
    where qualify = mkIdent (mkModuleName ["Cryptol"])

add_core_defs :: String -> [String] -> Simpset -> TopLevel Simpset
add_core_defs modname names ss =
  do sc <- getSharedContext
     defs <- io $ mapM (getDef sc) names -- FIXME: warn if not found
     defRules <- io $ concat <$> (mapM (scDefRewriteRules sc) defs)
     return (addRules defRules ss)
  where
    qualify = mkIdent (mkModuleName [modname])
    getDef sc n =
      scFindDef sc (qualify n) >>= \maybe_def ->
      case maybe_def of
        Just d -> return d
        Nothing -> fail $ modname ++ " definition " ++ n ++ " not found"

add_prelude_defs :: [String] -> Simpset -> TopLevel Simpset
add_prelude_defs = add_core_defs "Prelude"

add_cryptol_defs :: [String] -> Simpset -> TopLevel Simpset
add_cryptol_defs = add_core_defs "Cryptol"

rewritePrim :: Simpset -> TypedTerm -> TopLevel TypedTerm
rewritePrim ss (TypedTerm schema t) = do
  sc <- getSharedContext
  t' <- io $ rewriteSharedTerm sc ss t
  return (TypedTerm schema t')

unfold_term :: [String] -> TypedTerm -> TopLevel TypedTerm
unfold_term names (TypedTerm schema t) = do
  sc <- getSharedContext
  t' <- io $ scUnfoldConstants sc names t
  return (TypedTerm schema t')

beta_reduce_term :: TypedTerm -> TopLevel TypedTerm
beta_reduce_term (TypedTerm schema t) = do
  sc <- getSharedContext
  t' <- io $ betaNormalize sc t
  return (TypedTerm schema t')

addsimp :: Theorem -> Simpset -> Simpset
addsimp (Theorem (Prop t)) ss = addRule (ruleOfProp t) ss

addsimp' :: Term -> Simpset -> Simpset
addsimp' t ss = addRule (ruleOfProp t) ss

addsimps :: [Theorem] -> Simpset -> Simpset
addsimps thms ss = foldr addsimp ss thms

addsimps' :: [Term] -> Simpset -> Simpset
addsimps' ts ss = foldr (\t -> addRule (ruleOfProp t)) ss ts

print_type :: Term -> TopLevel ()
print_type t = do
  sc <- getSharedContext
  opts <- getTopLevelPPOpts
  ty <- io $ scTypeOf sc t
  printOutLnTop Info (scPrettyTerm opts ty)

check_term :: Term -> TopLevel ()
check_term t = do
  sc <- getSharedContext
  opts <- getTopLevelPPOpts
  ty <- io $ scTypeCheckError sc t
  printOutLnTop Info (scPrettyTerm opts ty)

check_goal :: ProofScript ()
check_goal =
  StateT $ \(ProofState goals concl stats timeout) ->
  case goals of
    [] -> fail "ProofScript failed: no subgoal"
    (ProofGoal _num _ty _name (Prop prop)) : _ ->
      do check_term prop
         return ((), ProofState goals concl stats timeout)

fixPos :: Pos
fixPos = PosInternal "FIXME"

freshSymbolicPrim :: String -> C.Schema -> TopLevel TypedTerm
freshSymbolicPrim x schema@(C.Forall [] [] ct) = do
  sc <- getSharedContext
  cty <- io $ Cryptol.importType sc Cryptol.emptyEnv ct
  tm <- io $ scFreshGlobal sc x cty
  return $ TypedTerm schema tm
freshSymbolicPrim _ _ =
  fail "Can't create fresh symbolic variable of non-ground type."

abstractSymbolicPrim :: TypedTerm -> TopLevel TypedTerm
abstractSymbolicPrim (TypedTerm _ t) = do
  sc <- getSharedContext
  io (mkTypedTerm sc =<< bindAllExts sc t)

bindAllExts :: SharedContext -> Term -> IO Term
bindAllExts sc body = scAbstractExts sc (getAllExts body) body

lambda :: TypedTerm -> TypedTerm -> TopLevel TypedTerm
lambda x = lambdas [x]

lambdas :: [TypedTerm] -> TypedTerm -> TopLevel TypedTerm
lambdas vars (TypedTerm schema0 term0) = do
  (es, ts) <- unzip <$> mapM checkVar vars
  ty <- checkMono schema0
  sc <- getSharedContext
  term' <- io $ scAbstractExts sc es term0
  let schema' = C.Forall [] [] (foldr C.tFun ty ts)
  return (TypedTerm schema' term')
  where
    checkMono schema =
      case schema of
        C.Forall [] [] t -> return t
        _ -> fail "lambda: cannot abstract over polymorphic variable"
    checkVar (TypedTerm schema term) = do
      e <- case asExtCns term of
             Just e -> return e
             Nothing -> fail "lambda: argument not a symbolic variable"
      t <- checkMono schema
      return (e, t)

-- | Apply the given Term to the given values, and evaluate to a
-- final value.
-- TODO: Take (ExtCns, FiniteValue) instead of (Term, FiniteValue)
cexEvalFn :: SharedContext -> [(ExtCns Term, FirstOrderValue)] -> Term
          -> IO Concrete.CValue
cexEvalFn sc args tm = do
  -- NB: there may be more args than exts, and this is ok. One side of
  -- an equality may have more free variables than the other,
  -- particularly in the case where there is a counter-example.
  let exts = map fst args
  args' <- mapM (scFirstOrderValue sc . snd) args
  let is = map ecVarIndex exts
      argMap = Map.fromList (zip is args')
  tm' <- scInstantiateExt sc argMap tm
  modmap <- scGetModuleMap sc
  return $ Concrete.evalSharedTerm modmap mempty tm'

toValueCase :: (SV.FromValue b) =>
               (b -> SV.Value -> SV.Value -> TopLevel SV.Value)
            -> SV.Value
toValueCase prim =
  SV.VLambda $ \b -> return $
  SV.VLambda $ \v1 -> return $
  SV.VLambda $ \v2 ->
  prim (SV.fromValue b) v1 v2

caseProofResultPrim :: SV.ProofResult
                    -> SV.Value -> SV.Value
                    -> TopLevel SV.Value
caseProofResultPrim pr vValid vInvalid = do
  sc <- getSharedContext
  case pr of
    SV.Valid _ -> return vValid
    SV.InvalidMulti _ pairs -> do
      let fvs = map snd pairs
      ts <- io $ mapM (scFirstOrderValue sc) fvs
      t <- io $ scTuple sc ts
      tt <- io $ mkTypedTerm sc t
      SV.applyValue vInvalid (SV.toValue tt)

caseSatResultPrim :: SV.SatResult
                  -> SV.Value -> SV.Value
                  -> TopLevel SV.Value
caseSatResultPrim sr vUnsat vSat = do
  sc <- getSharedContext
  case sr of
    SV.Unsat _ -> return vUnsat
    SV.SatMulti _ pairs -> do
      let fvs = map snd pairs
      ts <- io $ mapM (scFirstOrderValue sc) fvs
      t <- io $ scTuple sc ts
      tt <- io $ mkTypedTerm sc t
      SV.applyValue vSat (SV.toValue tt)

envCmd :: TopLevel ()
envCmd = do
  m <- rwTypes <$> getTopLevelRW
  opts <- getOptions
  let showLName = getVal
  io $ sequence_ [ printOutLn opts Info (showLName x ++ " : " ++ pShow v) | (x, v) <- Map.assocs m ]

exitPrim :: Integer -> IO ()
exitPrim code = Exit.exitWith exitCode
  where
    exitCode = if code /= 0
               then Exit.ExitFailure (fromInteger code)
               else Exit.ExitSuccess

-- Run the toplevel command.  Return a tuple containing
-- the elapsed time to run the command in milliseconds
-- and the value returned by the action.
withTimePrim :: TopLevel SV.Value -> TopLevel SV.Value
withTimePrim a = do
  t1 <- liftIO $ getCurrentTime
  r <- a
  t2 <- liftIO $ getCurrentTime
  -- diffUTCTime returns a length of time measured seconds
  let diff = truncate (diffUTCTime t2 t1 * 1000)
  return $ SV.VTuple [ SV.VInteger diff, r ]

timePrim :: TopLevel SV.Value -> TopLevel SV.Value
timePrim a = do
  t1 <- liftIO $ getCurrentTime
  r <- a
  t2 <- liftIO $ getCurrentTime
  let diff = diffUTCTime t2 t1
  printOutLnTop Info $ printf "Time: %s\n" (show diff)
  return r

failsPrim :: TopLevel SV.Value -> TopLevel ()
failsPrim m = TopLevel $ do
  topRO <- ask
  topRW <- Control.Monad.State.get
  x <- liftIO $ Ex.try (runTopLevel m topRO topRW)
  case x of
    Left (ex :: Ex.SomeException) ->
      do liftIO $ putStrLn "== Anticipated failure message =="
         liftIO $ print ex
    Right _ ->
      do liftIO $ fail "Expected failure, but succeeded instead!"

eval_bool :: TypedTerm -> TopLevel Bool
eval_bool t = do
  sc <- getSharedContext
  case ttSchema t of
    C.Forall [] [] (C.tIsBit -> True) -> return ()
    _ -> fail "eval_bool: not type Bit"
  unless (null (getAllExts (ttTerm t))) $
    fail "eval_bool: term contains symbolic variables"
  v <- io $ rethrowEvalError $ SV.evaluateTypedTerm sc t
  return (C.fromVBit v)

eval_int :: TypedTerm -> TopLevel Integer
eval_int t = do
  sc <- getSharedContext
  cenv <- fmap rwCryptol getTopLevelRW
  let cfg = C.meSolverConfig (CEnv.eModuleEnv cenv)
  unless (null (getAllExts (ttTerm t))) $
    fail "term contains symbolic variables"
  opts <- getOptions
  t' <- io $ defaultTypedTerm opts sc cfg t
  case ttSchema t' of
    C.Forall [] [] (isInteger -> True) -> return ()
    _ -> fail "eval_int: argument is not a finite bitvector"
  v <- io $ rethrowEvalError $ SV.evaluateTypedTerm sc t'
  io $ C.runEval SV.quietEvalOpts (C.bvVal <$> C.fromVWord C.Concrete "eval_int" v)

-- Predicate on Cryptol types true of integer types, i.e. types
-- @[n]Bit@ for *finite* @n@.
isInteger :: C.Type -> Bool
isInteger (C.tIsSeq -> Just (C.tIsNum -> Just _, C.tIsBit -> True)) = True
isInteger _ = False

list_term :: [TypedTerm] -> TopLevel TypedTerm
list_term [] = fail "list_term: invalid empty list"
list_term tts@(tt0 : _) =
  do sc <- getSharedContext
     let schema = ttSchema tt0
     unless (all (schema ==) (map ttSchema tts)) $
       fail "list_term: non-uniform element types"
     a <-
       case schema of
         C.Forall [] [] a -> return a
         _ -> fail "list_term: not a monomorphic element type"
     a' <- io $ Cryptol.importType sc Cryptol.emptyEnv a
     trm <- io $ scVectorReduced sc a' (map ttTerm tts)
     let n = C.tNum (length tts)
     return (TypedTerm (C.tMono (C.tSeq n a)) trm)

eval_list :: TypedTerm -> TopLevel [TypedTerm]
eval_list t = do
  sc <- getSharedContext
  (n, a) <-
    case ttSchema t of
      C.Forall [] [] (C.tIsSeq -> Just (C.tIsNum -> Just n, a)) -> return (n, a)
      _ -> fail "eval_list: not a monomorphic array type"
  n' <- io $ scNat sc (fromInteger n)
  a' <- io $ Cryptol.importType sc Cryptol.emptyEnv a
  idxs <- io $ traverse (scNat sc) $ map fromInteger [0 .. n - 1]
  ts <- io $ traverse (scAt sc n' a' (ttTerm t)) idxs
  return (map (TypedTerm (C.tMono a)) ts)

-- | Default the values of the type variables in a typed term.
defaultTypedTerm :: Options -> SharedContext -> C.SolverConfig -> TypedTerm -> IO TypedTerm
defaultTypedTerm opts sc cfg tt@(TypedTerm schema trm)
  | null (C.sVars schema) = return tt
  | otherwise = do
  mdefault <- C.withSolver cfg (\s -> C.defaultReplExpr s undefined schema)
  let inst = do (soln, _) <- mdefault
                mapM (`lookup` soln) (C.sVars schema)
  case inst of
    Nothing -> return (TypedTerm schema trm)
    Just tys -> do
      let vars = C.sVars schema
      let nms = C.addTNames vars IntMap.empty
      mapM_ (warnDefault nms) (zip vars tys)
      let applyType :: Term -> C.Type -> IO Term
          applyType t ty = do
            ty' <- Cryptol.importType sc Cryptol.emptyEnv ty
            scApply sc t ty'
      let dischargeProp :: Term -> C.Prop -> IO Term
          dischargeProp t p
            | Cryptol.isErasedProp p = return t
            | otherwise = scApply sc t =<< Cryptol.proveProp sc Cryptol.emptyEnv p
      trm' <- foldM applyType trm tys
      let su = C.listSubst (zip (map C.tpVar vars) tys)
      let props = map (plainSubst su) (C.sProps schema)
      trm'' <- foldM dischargeProp trm' props
      let schema' = C.Forall [] [] (C.apSubst su (C.sType schema))
      return (TypedTerm schema' trm'')
  where
    warnDefault ns (x,t) =
      printOutLn opts Info $ show $ C.text "Assuming" C.<+> C.ppWithNames ns (x :: C.TParam) C.<+> C.text "=" C.<+> C.pp t
    -- Apply a substitution to a type *without* simplifying
    -- constraints like @Arith [n]a@ to @Arith a@. (This is in contrast to
    -- 'apSubst', which performs simplifications wherever possible.)
    plainSubst :: C.Subst -> C.Type -> C.Type
    plainSubst s ty =
      case ty of
        C.TCon tc ts   -> C.TCon tc (map (plainSubst s) ts)
        C.TUser f ts t -> C.TUser f (map (plainSubst s) ts) (plainSubst s t)
        C.TRec fs      -> C.TRec (fmap (plainSubst s) fs)
        C.TVar x       -> C.apSubst s (C.TVar x)

eval_size :: C.Schema -> TopLevel Integer
eval_size s =
  case s of
    C.Forall [] [] t ->
      case C.evalType mempty t of
        Left (C.Nat x) -> return x
        Left C.Inf     -> fail "eval_size: illegal infinite size"
        Right _        -> fail "eval_size: not a numeric type"
    _ -> fail "eval_size: unsupported polymorphic type"

nthPrim :: [a] -> Int -> TopLevel a
nthPrim [] _ = fail "nth: index too large"
nthPrim (x : _) 0 = return x
nthPrim (_ : xs) i = nthPrim xs (i - 1)

headPrim :: [a] -> TopLevel a
headPrim [] = fail "head: empty list"
headPrim (x : _) = return x

tailPrim :: [a] -> TopLevel [a]
tailPrim [] = fail "tail: empty list"
tailPrim (_ : xs) = return xs

parseCore :: String -> TopLevel Term
parseCore input =
  do sc <- getSharedContext
     let base = "<interactive>"
         path = "<interactive>"
     uterm <-
       case parseSAWTerm base path (B.fromString input) of
         Right uterm -> return uterm
         Left err ->
           do let msg = show err
              printOutLnTop Opts.Error msg
              fail msg
     let mnm = Just $ mkModuleName ["Cryptol"]
     err_or_t <- io $ runTCM (typeInferComplete uterm) sc mnm []
     case err_or_t of
       Left err -> fail (show err)
       Right (TC.TypedTerm x _) -> return x

parse_core :: String -> TopLevel TypedTerm
parse_core input = do
  t <- parseCore input
  sc <- getSharedContext
  io $ mkTypedTerm sc t

prove_core :: ProofScript SV.SatResult -> String -> TopLevel Theorem
prove_core script input =
  do t <- parseCore input
     (r', pstate) <- runStateT script (startProof (ProofGoal 0 "prove" "prove" (Prop t)))
     let r = SV.flipSatResult r'
     opts <- rwPPOpts <$> getTopLevelRW
     case finishProof pstate of
       (_,Just thm) -> return thm
       (_,Nothing)  -> fail $ "prove_core: " ++ show (length (psGoals pstate)) ++ " unsolved subgoal(s)\n"
                         ++ SV.showsProofResult opts r ""

core_axiom :: String -> TopLevel Theorem
core_axiom input =
  do t <- parseCore input
     return (Theorem (Prop t))

core_thm :: String -> TopLevel Theorem
core_thm input =
  do t <- parseCore input
     sc <- getSharedContext
     ty <- io $ scTypeOf sc t
     return (Theorem (Prop ty))

get_opt :: Int -> TopLevel String
get_opt n = do
  prog <- io $ System.Environment.getProgName
  args <- io $ System.Environment.getArgs
  nthPrim (prog : args) n

cryptol_prims :: TopLevel CryptolModule
cryptol_prims = CryptolModule Map.empty <$> Map.fromList <$> traverse parsePrim prims
  where
    prims :: [(String, Ident, String)]
    prims =
      [ ("trunc", "Cryptol.ecTrunc" , "{m, n} (fin m, fin n) => [m+n] -> [n]")
      , ("uext" , "Cryptol.ecUExt"  , "{m, n} (fin m, fin n) => [n] -> [m+n]")
      , ("sext" , "Cryptol.ecSExt"  , "{m, n} (fin m, fin n, n >= 1) => [n] -> [m+n]")
      , ("sgt"  , "Cryptol.ecSgt"   , "{n} (fin n) => [n] -> [n] -> Bit")
      , ("sge"  , "Cryptol.ecSge"   , "{n} (fin n) => [n] -> [n] -> Bit")
      , ("slt"  , "Cryptol.ecSlt"   , "{n} (fin n) => [n] -> [n] -> Bit")
      , ("sle"  , "Cryptol.ecSle"   , "{n} (fin n) => [n] -> [n] -> Bit")
      ]
      -- TODO: sext, sdiv, srem, sshr

    noLoc :: String -> CEnv.InputText
    noLoc x = CEnv.InputText
                { CEnv.inpText = x
                , CEnv.inpFile = "(cryptol_prims)"
                , CEnv.inpLine = 1
                , CEnv.inpCol  = 1 + 2 -- add 2 for dropped {{
                }

    parsePrim :: (String, Ident, String) -> TopLevel (C.Name, TypedTerm)
    parsePrim (n, i, s) = do
      sc <- getSharedContext
      rw <- getTopLevelRW
      let cenv = rwCryptol rw
      let mname = C.packModName ["Prims"]
      let ?fileReader = StrictBS.readFile
      (n', cenv') <- io $ CEnv.declareName cenv mname n
      s' <- io $ CEnv.parseSchema cenv' (noLoc s)
      t' <- io $ scGlobalDef sc i
      putTopLevelRW $ rw { rwCryptol = cenv' }
      return (n', TypedTerm s' t')

cryptol_load :: (FilePath -> IO StrictBS.ByteString) -> FilePath -> TopLevel CryptolModule
cryptol_load fileReader path = do
  sc <- getSharedContext
  rw <- getTopLevelRW
  let ce = rwCryptol rw
  let ?fileReader = fileReader
  (m, ce') <- io $ CEnv.loadCryptolModule sc ce path
  putTopLevelRW $ rw { rwCryptol = ce' }
  return m


mr_solver_tests :: [SharedContext -> IO Term]
mr_solver_tests =
  let helper nm = \sc -> scGlobalDef sc nm in
  map helper
  [ "Prelude.test_fun0", "Prelude.test_fun1", "Prelude.test_fun2"
  , "Prelude.test_fun3", "Prelude.test_fun4", "Prelude.test_fun5"
  , "Prelude.test_fun6"]

testMRSolver :: Integer -> Integer -> TopLevel ()
testMRSolver i1 i2 =
  do sc <- getSharedContext
     t1 <- liftIO $ (mr_solver_tests !! fromInteger i1) sc
     t2 <- liftIO $ (mr_solver_tests !! fromInteger i2) sc
     res <- liftIO $ Prover.askMRSolver sc SBV.z3 Nothing t1 t2
     case res of
       Just err -> io $ putStrLn $ Prover.showMRFailure err
       Nothing -> io $ putStrLn "Success!"

parseSharpSATResult :: String -> Maybe Integer
parseSharpSATResult s = parse (lines s)
  where
    parse (h : n : _) | "# solutions" `isPrefixOf` h = readMaybe n
    parse (_ : rest) = parse rest
    parse [] = Nothing

sharpSAT :: TypedTerm -> TopLevel Integer
sharpSAT t = do
  sc <- getSharedContext
  tmp <- io $ emptySystemTempFile "sharpSAT-input"
  Prover.write_cnf sc tmp t
  (_ec, out, _err) <- io $ readProcessWithExitCode "sharpSAT" [tmp] ""
  io $ removeFile tmp
  case parseSharpSATResult out of
    Nothing -> fail $ "Garbled result from sharpSAT\n\n" ++ out
    Just n -> return n

approxmc :: TypedTerm -> TopLevel ()
approxmc t = do
  sc <- getSharedContext
  tmp <- io $ emptySystemTempFile "approxmc-input"
  Prover.write_cnf sc tmp t
  (_ec, out, _err) <- io $ readProcessWithExitCode "approxmc" [tmp] ""
  io $ removeFile tmp
  let msg = filter ("[appmc] Number of solutions is" `isPrefixOf`) (lines out)
  case msg of
    [l] -> io $ putStrLn l
    _ -> fail $ "Garbled result from approxmc\n\n" ++ out
