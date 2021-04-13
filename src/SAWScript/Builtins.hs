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
{-# LANGUAGE LambdaCase #-}
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
import Control.Monad.Except (MonadError(..))
import Control.Monad.State
import Control.Monad.Reader (ask)
import qualified Control.Exception as Ex
import qualified Data.ByteString as StrictBS
import qualified Data.ByteString.Lazy as BS
import qualified Data.ByteString.Lazy.UTF8 as B
import qualified Data.IntMap as IntMap
import Data.List (isPrefixOf, isInfixOf)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
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

import qualified Verifier.SAW.Cryptol as Cryptol
import qualified Verifier.SAW.Cryptol.Simpset as Cryptol

-- saw-core
import Verifier.SAW.Grammar (parseSAWTerm)
import Verifier.SAW.ExternalFormat
import Verifier.SAW.FiniteValue
  ( FiniteType(..), readFiniteValue
  , FirstOrderValue(..)
  , scFirstOrderValue
  )
import Verifier.SAW.SATQuery
import Verifier.SAW.SCTypeCheck hiding (TypedTerm)
import qualified Verifier.SAW.SCTypeCheck as TC (TypedTerm(..))
import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedTerm
import qualified Verifier.SAW.Simulator.Concrete as Concrete
import Verifier.SAW.Prim (rethrowEvalError)
import Verifier.SAW.Rewriter
import Verifier.SAW.Testing.Random (prepareSATQuery, runManyTests)
import Verifier.SAW.TypedAST

import SAWScript.Position

-- cryptol-saw-core
import qualified Verifier.SAW.CryptolEnv as CEnv

-- saw-core-sbv
import qualified Verifier.SAW.Simulator.SBV as SBVSim

-- sbv
import qualified Data.SBV.Dynamic as SBV

-- aig
import qualified Data.AIG as AIG

-- cryptol
import qualified Cryptol.ModuleSystem.Env as C (meSolverConfig, meSearchPath)
import qualified Cryptol.TypeCheck as C (SolverConfig)
import qualified Cryptol.TypeCheck.AST as C
import qualified Cryptol.TypeCheck.PP as C (ppWithNames, pp, text, (<+>))
import qualified Cryptol.TypeCheck.Solve as C (defaultReplExpr)
import qualified Cryptol.TypeCheck.Solver.SMT as C (withSolver)
import qualified Cryptol.TypeCheck.Solver.InfNat as C (Nat'(..))
import qualified Cryptol.TypeCheck.Subst as C (Subst, apSubst, listSubst)
import qualified Cryptol.Backend.Monad as C (runEval)
import qualified Cryptol.Eval.Type as C (evalType)
import qualified Cryptol.Eval.Value as C (fromVBit, fromVWord)
import qualified Cryptol.Eval.Concrete as C (Concrete(..), bvVal)
import qualified Cryptol.Utils.Ident as C (mkIdent, packModName)
import qualified Cryptol.Utils.RecordMap as C (recordFromFields)

import qualified SAWScript.SBVParser as SBV
import SAWScript.ImportAIG

import SAWScript.AST (getVal, pShow, Located(..))
import SAWScript.Options as Opts
import SAWScript.Proof
import SAWScript.TopLevel
import qualified SAWScript.Value as SV
import SAWScript.Value (ProofScript, printOutLnTop, AIGNetwork)

import SAWScript.Prover.Util(checkBooleanSchema)
import SAWScript.Prover.SolverStats
import qualified SAWScript.Prover.SBV as Prover
import qualified SAWScript.Prover.RME as Prover
import qualified SAWScript.Prover.ABC as Prover
import qualified SAWScript.Prover.What4 as Prover
import qualified SAWScript.Prover.Exporter as Prover
import qualified SAWScript.Prover.MRSolver as Prover
import SAWScript.VerificationSummary

showPrim :: SV.Value -> TopLevel String
showPrim v = do
  opts <- fmap rwPPOpts getTopLevelRW
  return (SV.showsPrecValue opts 0 v "")

definePrim :: Text -> TypedTerm -> TopLevel TypedTerm
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
          SBV.TRecord bs -> C.tRec (C.recordFromFields [ (C.mkIdent n, toCType t) | (n, t) <- bs ])



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
dsecPrint sc t1 t2 = SV.getProxy >>= \(SV.AIGProxy proxy) -> do
  withSystemTempFile ".aig" $ \path1 _handle1 -> do
  withSystemTempFile ".aig" $ \path2 _handle2 -> do
  Prover.writeSAIGInferLatches proxy sc path1 t1
  Prover.writeSAIGInferLatches proxy sc path2 t2
  io $ callCommand (abcDsec path1 path2)
  where
    -- The '-w' here may be overkill ...
    abcDsec path1 path2 = printf "abc -c 'read %s; dsec -v -w %s;'" path1 path2

cecPrim :: AIGNetwork -> AIGNetwork -> TopLevel ProofResult
cecPrim (SV.AIGNetwork x) (SV.AIGNetwork y) = do
  y' <- case cast y of
          Just n -> return n
          Nothing -> fail "Inconsistent AIG types"
  io $ verifyAIGCompatible x y'
  res <- io $ AIG.cec x y'
  let stats = solverStats "ABC" 0 -- TODO, count the size of the networks...
  case res of
    AIG.Valid -> return $ ValidProof stats (error "cecPrim: deprecated function!")
    AIG.Invalid bs
      | Just _fv <- readFiniteValue (FTVec (fromIntegral (length bs)) FTBit) bs ->
           return $ InvalidProof stats [] (error "cecPRim : deprecated function!")
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
    Right (inLen, outLen, t) -> pure $ TypedTerm schema t
      where
        t1 = C.tWord (C.tNum inLen)
        t2 = C.tWord (C.tNum outLen)
        schema = C.tMono (C.tFun t1 t2)

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

execTactic :: Tactic TopLevel a -> ProofScript a
execTactic tac =
  do st <- get
     SV.scriptTopLevel (withFirstGoal tac st) >>= \case
       Left cex -> throwError cex
       Right (x,st') ->
         do put st'
            return x

quickcheckGoal :: SharedContext -> Integer -> ProofScript ()
quickcheckGoal sc n = do
  opts <- SV.scriptTopLevel getOptions
  execTactic $ tacticSolve $ \goal -> io $ do
    printOutLn opts Warn $ "WARNING: using quickcheck to prove goal..."
    hFlush stdout
    satq <- propToSATQuery sc mempty (goalProp goal)
    testGen <- prepareSATQuery sc satq
    let stats = solverStats "quickcheck" (propSize (goalProp goal))
    runManyTests testGen n >>= \case
       Nothing ->
         do printOutLn opts Info $ "checked " ++ show n ++ " cases."
            return (stats, SolveSuccess (QuickcheckEvidence n (goalProp goal)))
       Just cex -> return (stats, SolveCounterexample cex)

assumeValid :: ProofScript ()
assumeValid =
  execTactic $ tacticSolve $ \goal ->
  do printOutLnTop Warn $ "WARNING: assuming goal " ++ goalName goal ++ " is valid"
     pos <- SV.getPosition
     let admitMsg = "assumeValid: " ++ goalName goal
     let stats = solverStats "ADMITTED" (propSize (goalProp goal))
     return (stats, SolveSuccess (Admitted admitMsg pos (goalProp goal)))

assumeUnsat :: ProofScript ()
assumeUnsat =
  execTactic $ tacticSolve $ \goal ->
  do printOutLnTop Warn $ "WARNING: assuming goal " ++ goalName goal ++ " is unsat"
     pos <- SV.getPosition
     let admitMsg = "assumeUnsat: " ++ goalName goal
     let stats = solverStats "ADMITTED" (propSize (goalProp goal))
     return (stats, SolveSuccess (Admitted admitMsg pos (goalProp goal)))

admitProof :: String -> ProofScript ()
admitProof msg =
  execTactic $ tacticSolve $ \goal ->
  do printOutLnTop Warn $ "WARNING: admitting goal " ++ goalName goal
     pos <- SV.getPosition
     let stats = solverStats "ADMITTED" (propSize (goalProp goal))
     return (stats, SolveSuccess (Admitted msg pos (goalProp goal)))

trivial :: ProofScript ()
trivial =
  do sc <- SV.scriptTopLevel getSharedContext
     execTactic (tacticTrivial sc)

split_goal :: ProofScript ()
split_goal =
  do sc <- SV.scriptTopLevel getSharedContext
     execTactic (tacticSplit sc)

getTopLevelPPOpts :: TopLevel PPOpts
getTopLevelPPOpts = do
  opts <- fmap rwPPOpts getTopLevelRW
  return (SV.sawPPOpts opts)

show_term :: Term -> TopLevel String
show_term t =
  do opts <- getTopLevelPPOpts
     sc <- getSharedContext
     liftIO $ scShowTerm sc opts t

print_term :: Term -> TopLevel ()
print_term t = printOutLnTop Info =<< show_term t

print_term_depth :: Int -> Term -> TopLevel ()
print_term_depth d t =
  do opts <- getTopLevelPPOpts
     sc <- getSharedContext
     let opts' = opts { ppMaxDepth = Just d }
     output <- liftIO $ scShowTerm sc opts' t
     printOutLnTop Info output

print_goal :: ProofScript ()
print_goal =
  execTactic $ tacticId $ \goal ->
  do opts <- getTopLevelPPOpts
     sc <- getSharedContext
     output <- liftIO (scShowTerm sc opts =<< propToTerm sc (goalProp goal))
     printOutLnTop Info ("Goal " ++ goalName goal ++ " (goal number " ++ (show $ goalNum goal) ++ "):")
     printOutLnTop Info output

print_goal_depth :: Int -> ProofScript ()
print_goal_depth n =
  execTactic $ tacticId $ \goal ->
  do opts <- getTopLevelPPOpts
     sc <- getSharedContext
     let opts' = opts { ppMaxDepth = Just n }
     output <- liftIO (scShowTerm sc opts' =<< propToTerm sc (goalProp goal))
     printOutLnTop Info ("Goal " ++ goalName goal ++ ":")
     printOutLnTop Info output

printGoalConsts :: ProofScript ()
printGoalConsts =
  execTactic $ tacticId $ \goal ->
  do sc <- getSharedContext
     tm <- io (propToTerm sc (goalProp goal))
     mapM_ (printOutLnTop Info) $
       [ show nm
       | (_,(nm,_,_)) <- Map.toList (getConstantSet tm)
       ]

printGoalSize :: ProofScript ()
printGoalSize =
  execTactic $ tacticId $ \goal ->
  do sc <- getSharedContext
     t  <- io (propToTerm sc (goalProp goal))
     printOutLnTop Info $ "Goal shared size: " ++ show (scSharedSize t)
     printOutLnTop Info $ "Goal unshared size: " ++ show (scTreeSize t)

resolveNames :: [String] -> TopLevel (Set VarIndex)
resolveNames nms =
  do sc <- getSharedContext
     Set.fromList <$> mapM (resolveName sc) nms

-- | Given a user-provided name, resolve it to some
--   'ExtCns' that represents an unfoldable 'Constant'
--   value or a fresh uninterpreted constant.
--
--   We first attempt to find the name in the local Cryptol
--   environment; if the name is found, attempt to resolve it to
--   an 'ExtCns' in the SAWCore environment.  If the given name
--   does not resolve to a cryptol value in the current environment that
--  maps to an 'ExtCns', then instead directly look it up
--  in the SAWCore naming environment.  If both stages
--  fail, then throw an exception.
resolveName :: SharedContext -> String -> TopLevel VarIndex
resolveName sc nm =
  do cenv <- rwCryptol <$> getTopLevelRW
     let ?fileReader = StrictBS.readFile
     res <- io $ CEnv.resolveIdentifier cenv tnm
     case res of
       Just cnm ->
         do importedName <- io $ Cryptol.importName cnm
            case importedName of
              ImportedName uri _ ->
                do resolvedName <- io $ scResolveNameByURI sc uri
                   case resolvedName of
                     Just vi -> pure vi
                     Nothing -> fallback
              _ -> fallback
       Nothing -> fallback

 where
 tnm = Text.pack nm
 fallback = fst <$> io (scResolveUnambiguous sc tnm)


unfoldGoal :: [String] -> ProofScript ()
unfoldGoal unints =
  execTactic $ tacticChange $ \goal ->
  do sc <- getSharedContext
     unints' <- resolveNames unints
     prop' <- io (unfoldProp sc unints' (goalProp goal))
     return (prop', UnfoldEvidence unints')

simplifyGoal :: Simpset -> ProofScript ()
simplifyGoal ss =
  execTactic $ tacticChange $ \goal ->
  do sc <- getSharedContext
     prop' <- io (simplifyProp sc ss (goalProp goal))
     return (prop', RewriteEvidence ss)

goal_eval :: [String] -> ProofScript ()
goal_eval unints =
  execTactic $ tacticChange $ \goal ->
  do sc <- getSharedContext
     unintSet <- resolveNames unints
     prop' <- io (evalProp sc unintSet (goalProp goal))
     return (prop', EvalEvidence unintSet)

extract_uninterp :: [String] -> TypedTerm -> TopLevel (TypedTerm, [(String,[(TypedTerm,TypedTerm)])])
extract_uninterp unints tt =
  do sc <- getSharedContext
     idxs <- mapM (resolveName sc) unints
     let unintSet = Set.fromList idxs
     (tm, repls) <- io (Prover.w4_extract_uninterp sc unintSet (ttTerm tt))
     tt' <- io (mkTypedTerm sc tm)

     -- printOutLnTop Info "====== Replacement values ======"
     -- forM_ (zip unints idxs) $ \(nm,idx) ->
     --   do printOutLnTop Info ("== Values for " ++ nm ++ " ==")
     --      let ls = fromMaybe [] (Map.lookup idx repls)
     --      forM_ ls $ \(e,vs) ->
     --        do es  <- show_term e
     --           vss <- show_term vs
     --           printOutLnTop Info (unwords ["output:", es, "inputs:", vss])
     -- printOutLnTop Info "====== End Replacement values ======"

     replList <- io $
        forM (zip unints idxs) $ \(nm,idx) ->
           do let ls = fromMaybe [] (Map.lookup idx repls)
              xs <- forM ls $ \(e,vs) ->
                      do e'  <- mkTypedTerm sc e
                         vs' <- mkTypedTerm sc vs
                         pure (e',vs')
              pure (nm,xs)
     pure (tt', replList)

beta_reduce_goal :: ProofScript ()
beta_reduce_goal =
  execTactic $ tacticChange $ \goal ->
  do sc <- getSharedContext
     prop' <- io (betaReduceProp sc (goalProp goal))
     return (prop', id)

goal_apply :: Theorem -> ProofScript ()
goal_apply thm =
  do sc <- SV.scriptTopLevel getSharedContext
     execTactic (tacticApply sc thm)

goal_assume :: ProofScript Theorem
goal_assume =
  do sc <- SV.scriptTopLevel getSharedContext
     execTactic (tacticAssume sc)

goal_intro :: Text -> ProofScript TypedTerm
goal_intro s =
  do sc <- SV.scriptTopLevel getSharedContext
     execTactic (tacticIntro sc s)

goal_insert :: Theorem -> ProofScript ()
goal_insert thm =
  do sc <- SV.scriptTopLevel getSharedContext
     execTactic (tacticCut sc thm)

goal_num_when :: Int -> ProofScript () -> ProofScript ()
goal_num_when n script =
  do s <- get
     case psGoals s of
       g : _ | goalNum g == n -> script
       _ -> return ()

goal_when :: String -> ProofScript () -> ProofScript ()
goal_when str script =
  do s <- get
     case psGoals s of
       g : _ | str `isInfixOf` goalName g -> script
       _ -> return ()

goal_num_ite :: Int -> ProofScript SV.Value -> ProofScript SV.Value -> ProofScript SV.Value
goal_num_ite n s1 s2 =
  do s <- get
     case psGoals s of
          g : _ | goalNum g == n -> s1
          _ -> s2

-- | Bit-blast a proposition and check its validity using ABC.
proveABC :: ProofScript ()
proveABC = do
  SV.AIGProxy proxy <- SV.scriptTopLevel SV.getProxy
  wrapProver (Prover.proveABC proxy)

satExternal :: Bool -> String -> [String] -> ProofScript ()
satExternal doCNF execName args =
  execTactic $ tacticSolve $ \g ->
    do SV.AIGProxy proxy <- SV.getProxy
       sc <- SV.getSharedContext
       (mb, stats) <- Prover.abcSatExternal proxy sc doCNF execName args g
       case mb of
         Nothing -> return (stats, SolveSuccess (SolverEvidence stats (goalProp g)))
         Just a  -> return (stats, SolveCounterexample a)

writeAIGPrim :: FilePath -> Term -> TopLevel ()
writeAIGPrim f t = do
  SV.AIGProxy proxy <- SV.getProxy
  sc <- SV.getSharedContext
  Prover.writeAIG proxy sc f t

writeSAIGPrim :: FilePath -> TypedTerm -> TopLevel ()
writeSAIGPrim f t = do
  SV.AIGProxy proxy <- SV.getProxy
  sc <- SV.getSharedContext
  Prover.writeSAIGInferLatches proxy sc f t

writeSAIGComputedPrim :: FilePath -> Term -> Int -> TopLevel ()
writeSAIGComputedPrim f t n = do
  SV.AIGProxy proxy <- SV.getProxy
  sc <- SV.getSharedContext
  Prover.writeSAIG proxy sc f t n

-- | Bit-blast a proposition check its validity using the RME library.
proveRME :: ProofScript ()
proveRME = wrapProver Prover.proveRME

codegenSBV :: SharedContext -> FilePath -> [String] -> String -> TypedTerm -> TopLevel ()
codegenSBV sc path unints fname (TypedTerm _schema t) =
  do unintSet <- resolveNames unints
     let mpath = if null path then Nothing else Just path
     io $ SBVSim.sbvCodeGen sc mempty unintSet mpath fname t

-- | Bit-blast a proposition and check its validity using SBV.
-- (Currently ignores satisfying assignments.)
proveSBV :: SBV.SMTConfig -> ProofScript ()
proveSBV conf = proveUnintSBV conf []

-- | Bit-blast a proposition and check its validity using SBV.
-- (Currently ignores satisfying assignments.) Constants with names in
-- @unints@ are kept as uninterpreted functions.
proveUnintSBV :: SBV.SMTConfig -> [String] -> ProofScript ()
proveUnintSBV conf unints =
  do timeout <- psTimeout <$> get
     unintSet <- SV.scriptTopLevel (resolveNames unints)
     wrapProver (Prover.proveUnintSBV conf unintSet timeout)

applyProverToGoal :: (SharedContext
                      -> Prop -> IO (Maybe CEX, SolverStats))
                     -> SharedContext
                     -> ProofGoal
                     -> TopLevel (SolverStats, SolveResult)
applyProverToGoal f sc g = do
  (mb, stats) <- io $ f sc (goalProp g)
  case mb of
    Nothing -> return (stats, SolveSuccess (SolverEvidence stats (goalProp g)))
    Just a  -> return (stats, SolveCounterexample a)

wrapProver ::
  (SharedContext -> Prop -> IO (Maybe CEX, SolverStats)) ->
  ProofScript ()
wrapProver f = do
  sc <- SV.scriptTopLevel SV.getSharedContext
  execTactic $ tacticSolve $ applyProverToGoal f sc

wrapW4Prover ::
  ( Set VarIndex -> SharedContext -> Bool ->
    Prop -> IO (Maybe CEX, SolverStats)) ->
  [String] ->
  ProofScript ()
wrapW4Prover f unints = do
  hashConsing <- SV.scriptTopLevel $ gets SV.rwWhat4HashConsing
  unintSet <- SV.scriptTopLevel $ resolveNames unints
  wrapProver $ \sc -> f unintSet sc hashConsing

wrapW4ProveExporter ::
  ( Set VarIndex -> SharedContext -> Bool -> FilePath ->
    Prop -> IO (Maybe CEX, SolverStats)) ->
  [String] ->
  String ->
  String ->
  ProofScript ()
wrapW4ProveExporter f unints path ext = do
  hashConsing <- SV.scriptTopLevel $ gets SV.rwWhat4HashConsing
  sc <- SV.scriptTopLevel $ SV.getSharedContext
  unintSet <- SV.scriptTopLevel $ resolveNames unints
  execTactic $ tacticSolve $ \g -> do
    let file = path ++ "." ++ goalType g ++ show (goalNum g) ++ ext
    applyProverToGoal (\s -> f unintSet s hashConsing file) sc g

--------------------------------------------------
proveABC_SBV :: ProofScript ()
proveABC_SBV = proveSBV SBV.abc

proveBoolector :: ProofScript ()
proveBoolector = proveSBV SBV.boolector

proveZ3 :: ProofScript ()
proveZ3 = proveSBV SBV.z3

proveCVC4 :: ProofScript ()
proveCVC4 = proveSBV SBV.cvc4

proveMathSAT :: ProofScript ()
proveMathSAT = proveSBV SBV.mathSAT

proveYices :: ProofScript ()
proveYices = proveSBV SBV.yices

proveUnintBoolector :: [String] -> ProofScript ()
proveUnintBoolector = proveUnintSBV SBV.boolector

proveUnintZ3 :: [String] -> ProofScript ()
proveUnintZ3 = proveUnintSBV SBV.z3

proveUnintCVC4 :: [String] -> ProofScript ()
proveUnintCVC4 = proveUnintSBV SBV.cvc4

proveUnintMathSAT :: [String] -> ProofScript ()
proveUnintMathSAT = proveUnintSBV SBV.mathSAT

proveUnintYices :: [String] -> ProofScript ()
proveUnintYices = proveUnintSBV SBV.yices


--------------------------------------------------
w4_abc_smtlib2 :: ProofScript ()
w4_abc_smtlib2 = wrapW4Prover Prover.proveWhat4_abc []

w4_boolector :: ProofScript ()
w4_boolector = wrapW4Prover Prover.proveWhat4_boolector []

w4_z3 :: ProofScript ()
w4_z3 = wrapW4Prover Prover.proveWhat4_z3 []

w4_cvc4 :: ProofScript ()
w4_cvc4 = wrapW4Prover Prover.proveWhat4_cvc4 []

w4_yices :: ProofScript ()
w4_yices = wrapW4Prover Prover.proveWhat4_yices []

w4_unint_boolector :: [String] -> ProofScript ()
w4_unint_boolector = wrapW4Prover Prover.proveWhat4_boolector

w4_unint_z3 :: [String] -> ProofScript ()
w4_unint_z3 = wrapW4Prover Prover.proveWhat4_z3

w4_unint_cvc4 :: [String] -> ProofScript ()
w4_unint_cvc4 = wrapW4Prover Prover.proveWhat4_cvc4

w4_unint_yices :: [String] -> ProofScript ()
w4_unint_yices = wrapW4Prover Prover.proveWhat4_yices

offline_w4_unint_z3 :: [String] -> String -> ProofScript ()
offline_w4_unint_z3 unints path =
     wrapW4ProveExporter Prover.proveExportWhat4_z3 unints path ".smt2"

offline_w4_unint_cvc4 :: [String] -> String -> ProofScript ()
offline_w4_unint_cvc4 unints path =
     wrapW4ProveExporter Prover.proveExportWhat4_cvc4 unints path ".smt2"

offline_w4_unint_yices :: [String] -> String -> ProofScript ()
offline_w4_unint_yices unints path =
     wrapW4ProveExporter Prover.proveExportWhat4_yices unints path ".smt2"

proveWithSATExporter ::
  (SharedContext -> FilePath -> SATQuery -> TopLevel a) ->
  Set VarIndex ->
  String ->
  String ->
  String ->
  ProofScript ()
proveWithSATExporter exporter unintSet path sep ext =
  execTactic $ tacticSolve $ \g ->
  do let file = path ++ sep ++ goalType g ++ show (goalNum g) ++ ext
     stats <- Prover.proveWithSATExporter exporter unintSet file (goalProp g)
     return (stats, SolveSuccess (SolverEvidence stats (goalProp g)))

proveWithPropExporter ::
  (SharedContext -> FilePath -> Prop -> TopLevel a) ->
  String ->
  String ->
  String ->
  ProofScript ()
proveWithPropExporter exporter path sep ext =
  execTactic $ tacticSolve $ \g ->
  do let file = path ++ sep ++ goalType g ++ show (goalNum g) ++ ext
     stats <- Prover.proveWithPropExporter exporter file (goalProp g)
     return (stats, SolveSuccess (SolverEvidence stats (goalProp g)))

offline_aig :: FilePath -> ProofScript ()
offline_aig path = do
  SV.AIGProxy proxy <- SV.scriptTopLevel SV.getProxy
  proveWithSATExporter (Prover.writeAIG_SAT proxy) mempty path "." ".aig"

offline_aig_external :: FilePath -> ProofScript ()
offline_aig_external path =
  proveWithSATExporter Prover.writeAIG_SATviaVerilog mempty path "." ".aig"

offline_cnf :: FilePath -> ProofScript ()
offline_cnf path = do
  SV.AIGProxy proxy <- SV.scriptTopLevel SV.getProxy
  proveWithSATExporter (Prover.writeCNF proxy) mempty path "." ".cnf"

offline_cnf_external :: FilePath -> ProofScript ()
offline_cnf_external path =
  proveWithSATExporter Prover.writeCNF_SATviaVerilog mempty path "." ".cnf"

offline_coq :: FilePath -> ProofScript ()
offline_coq path = proveWithPropExporter (const (Prover.writeCoqProp "goal" [] [])) path "_" ".v"

offline_extcore :: FilePath -> ProofScript ()
offline_extcore path = proveWithPropExporter (const Prover.writeCoreProp) path "." ".extcore"

offline_smtlib2 :: FilePath -> ProofScript ()
offline_smtlib2 path = proveWithSATExporter Prover.writeSMTLib2 mempty path "." ".smt2"

w4_offline_smtlib2 :: FilePath -> ProofScript ()
w4_offline_smtlib2 path = proveWithSATExporter Prover.writeSMTLib2What4 mempty path "." ".smt2"

offline_unint_smtlib2 :: [String] -> FilePath -> ProofScript ()
offline_unint_smtlib2 unints path =
  do unintSet <- SV.scriptTopLevel $ resolveNames unints
     proveWithSATExporter Prover.writeSMTLib2 unintSet path "." ".smt2"

offline_verilog :: FilePath -> ProofScript ()
offline_verilog path =
  proveWithSATExporter Prover.writeVerilogSAT mempty path "." ".v"

w4_abc_verilog :: ProofScript ()
w4_abc_verilog = wrapW4Prover Prover.w4AbcVerilog []

set_timeout :: Integer -> ProofScript ()
set_timeout to = modify (setProofTimeout to)

-- | Translate a @Term@ representing a theorem for input to the
-- given validity-checking script and attempt to prove it.
provePrim ::
  ProofScript () ->
  TypedTerm ->
  TopLevel ProofResult
provePrim script t = do
  io $ checkBooleanSchema (ttSchema t)
  sc <- getSharedContext
  prop <- io $ predicateToProp sc Universal (ttTerm t)
  let goal = ProofGoal 0 "prove" "prove" prop
  res <- SV.runProofScript script goal
  case res of
    UnfinishedProof pst ->
      printOutLnTop Info $ "prove: " ++ show (length (psGoals pst)) ++ " unsolved subgoal(s)"
    _ -> return ()
  return res

provePrintPrim ::
  ProofScript () ->
  TypedTerm ->
  TopLevel Theorem
provePrintPrim script t = do
  sc <- getSharedContext
  prop <- io $ predicateToProp sc Universal (ttTerm t)
  let goal = ProofGoal 0 "prove" "prove" prop
  opts <- rwPPOpts <$> getTopLevelRW
  res <- SV.runProofScript script goal
  let failProof pst =
         fail $ "prove: " ++ show (length (psGoals pst)) ++ " unsolved subgoal(s)\n"
                          ++ SV.showsProofResult opts res ""
  case res of
    ValidProof _stats thm ->
      do printOutLnTop Debug $ "Valid: " ++ show (ppTerm (SV.sawPPOpts opts) $ ttTerm t)
         SV.returnProof thm
    InvalidProof _stats _cex pst -> failProof pst
    UnfinishedProof pst -> failProof pst

satPrim ::
  ProofScript () ->
  TypedTerm ->
  TopLevel SV.SatResult
satPrim script t =
  do io $ checkBooleanSchema (ttSchema t)
     sc <- getSharedContext
     prop <- io $ predicateToProp sc Existential (ttTerm t)
     let goal = ProofGoal 0 "sat" "sat" prop
     res <- SV.runProofScript script goal
     case res of
       InvalidProof stats cex _ -> return (SV.Sat stats cex)
       ValidProof stats _thm -> return (SV.Unsat stats)
       UnfinishedProof _ -> return SV.SatUnknown

satPrintPrim ::
  ProofScript () ->
  TypedTerm ->
  TopLevel ()
satPrintPrim script t = do
  result <- satPrim script t
  opts <- rwPPOpts <$> getTopLevelRW
  printOutLnTop Info (SV.showsSatResult opts result "")

-- | Quick check (random test) a term and print the result. The
-- 'Integer' parameter is the number of random tests to run.
quickCheckPrintPrim :: Options -> SharedContext -> Integer -> TypedTerm -> IO ()
quickCheckPrintPrim opts sc numTests tt =
  do prop <- predicateToProp sc Universal (ttTerm tt)
     satq <- propToSATQuery sc mempty prop
     testGen <- prepareSATQuery sc satq
     runManyTests testGen numTests >>= \case
        Nothing -> printOutLn opts Info $ "All " ++ show numTests ++ " tests passed!"
        Just cex ->
          do let cex' = [ (Text.unpack (toShortName (ecName ec)), v) | (ec,v) <- cex ]
             printOutLn opts OnlyCounterExamples $
               "----------Counterexample----------\n" ++
               showList cex' ""

cryptolSimpset :: TopLevel Simpset
cryptolSimpset =
  do sc <- getSharedContext
     io $ Cryptol.mkCryptolSimpset sc

addPreludeEqs :: [Text] -> Simpset -> TopLevel Simpset
addPreludeEqs names ss = do
  sc <- getSharedContext
  eqRules <- io $ mapM (scEqRewriteRule sc) (map qualify names)
  return (addRules eqRules ss)
    where qualify = mkIdent (mkModuleName ["Prelude"])

addCryptolEqs :: [Text] -> Simpset -> TopLevel Simpset
addCryptolEqs names ss = do
  sc <- getSharedContext
  eqRules <- io $ mapM (scEqRewriteRule sc) (map qualify names)
  return (addRules eqRules ss)
    where qualify = mkIdent (mkModuleName ["Cryptol"])

add_core_defs :: Text -> [Text] -> Simpset -> TopLevel Simpset
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
        Nothing -> fail $ Text.unpack $ modname <> " definition " <> n <> " not found"

add_prelude_defs :: [Text] -> Simpset -> TopLevel Simpset
add_prelude_defs = add_core_defs "Prelude"

add_cryptol_defs :: [Text] -> Simpset -> TopLevel Simpset
add_cryptol_defs = add_core_defs "Cryptol"

rewritePrim :: Simpset -> TypedTerm -> TopLevel TypedTerm
rewritePrim ss (TypedTerm schema t) = do
  sc <- getSharedContext
  t' <- io $ rewriteSharedTerm sc ss t
  return (TypedTerm schema t')

unfold_term :: [String] -> TypedTerm -> TopLevel TypedTerm
unfold_term unints (TypedTerm schema t) = do
  sc <- getSharedContext
  unints' <- mapM (resolveName sc) unints
  t' <- io $ scUnfoldConstants sc unints' t
  return (TypedTerm schema t')

beta_reduce_term :: TypedTerm -> TopLevel TypedTerm
beta_reduce_term (TypedTerm schema t) = do
  sc <- getSharedContext
  t' <- io $ betaNormalize sc t
  return (TypedTerm schema t')

addsimp :: Theorem -> Simpset -> TopLevel Simpset
addsimp thm ss =
  do sc <- getSharedContext
     io (propToRewriteRule sc (thmProp thm)) >>= \case
       Nothing -> fail "addsimp: theorem not an equation"
       Just rule -> pure (addRule rule ss)

addsimp' :: Term -> Simpset -> TopLevel Simpset
addsimp' t ss =
  case ruleOfProp t of
    Nothing -> fail "addsimp': theorem not an equation"
    Just rule -> pure (addRule rule ss)

addsimps :: [Theorem] -> Simpset -> TopLevel Simpset
addsimps thms ss = foldM (flip addsimp) ss thms

addsimps' :: [Term] -> Simpset -> TopLevel Simpset
addsimps' ts ss = foldM (flip addsimp') ss ts

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
  do pfst <- get
     case psGoals pfst of
       [] -> fail "ProofScript failed: no subgoal"
       g : _ ->
         SV.scriptTopLevel $
         do sc <- getSharedContext
            tm <- io (propToTerm sc (goalProp g))
            check_term tm
            return ()

fixPos :: Pos
fixPos = PosInternal "FIXME"

freshSymbolicPrim :: Text -> C.Schema -> TopLevel TypedTerm
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
lambdas vars tt =
  do tecs <- traverse checkVar vars
     sc <- getSharedContext
     io $ abstractTypedExts sc tecs tt
  where
    checkVar v =
      case asTypedExtCns v of
        Just tec -> pure tec
        Nothing -> fail "lambda: argument not a valid symbolic variable"

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

  -- TODO, instead of instantiating and then evaluating, we should
  -- evaluate in the context of an EC map instead.  argMap is almost
  -- what we need, but the values syould be @Concrete.CValue@ instead.

  tm' <- scInstantiateExt sc argMap tm
  modmap <- scGetModuleMap sc
  return $ Concrete.evalSharedTerm modmap mempty mempty tm'

toValueCase :: (SV.FromValue b) =>
               (b -> SV.Value -> SV.Value -> TopLevel SV.Value)
            -> SV.Value
toValueCase prim =
  SV.VLambda $ \b -> return $
  SV.VLambda $ \v1 -> return $
  SV.VLambda $ \v2 ->
  prim (SV.fromValue b) v1 v2

caseProofResultPrim ::
  ProofResult ->
  SV.Value {- ^ valid case -} ->
  SV.Value {- ^ invalid/unknown case -} ->
  TopLevel SV.Value
caseProofResultPrim pr vValid vInvalid = do
  sc <- getSharedContext
  case pr of
    ValidProof _ thm ->
      SV.applyValue vValid (SV.toValue thm)
    InvalidProof _ pairs _pst -> do
      let fov = FOVTuple (map snd pairs)
      tt <- io $ typedTermOfFirstOrderValue sc fov
      SV.applyValue vInvalid (SV.toValue tt)
    UnfinishedProof _ -> do
      tt <- io $ typedTermOfFirstOrderValue sc (FOVTuple [])
      SV.applyValue vInvalid (SV.toValue tt)

caseSatResultPrim ::
  SV.SatResult ->
  SV.Value {- ^ unsat case -} ->
  SV.Value {- ^ sat/unknown case -} ->
  TopLevel SV.Value
caseSatResultPrim sr vUnsat vSat = do
  sc <- getSharedContext
  case sr of
    SV.Unsat _ -> return vUnsat
    SV.Sat _ pairs -> do
      let fov = FOVTuple (map snd pairs)
      tt <- io $ typedTermOfFirstOrderValue sc fov
      SV.applyValue vSat (SV.toValue tt)
    SV.SatUnknown -> do
      let fov = FOVTuple []
      tt <- io $ typedTermOfFirstOrderValue sc fov
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
  io $ C.runEval mempty (C.bvVal <$> C.fromVWord C.Concrete "eval_int" v)

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
        C.TNewtype nt ts -> C.TNewtype nt (fmap (plainSubst s) ts)

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

prove_core :: ProofScript () -> String -> TopLevel Theorem
prove_core script input =
  do sc <- getSharedContext
     t <- parseCore input
     p <- io (termToProp sc t)
     opts <- rwPPOpts <$> getTopLevelRW
     res <- SV.runProofScript script (ProofGoal 0 "prove" "prove" p)
     let failProof pst =
            fail $ "prove_core: " ++ show (length (psGoals pst)) ++ " unsolved subgoal(s)\n"
                                  ++ SV.showsProofResult opts res ""
     case res of
       ValidProof _ thm -> SV.returnProof thm
       InvalidProof _ _ pst -> failProof pst
       UnfinishedProof pst  -> failProof pst

core_axiom :: String -> TopLevel Theorem
core_axiom input =
  do sc <- getSharedContext
     pos <- SV.getPosition
     t <- parseCore input
     p <- io (termToProp sc t)
     SV.returnProof (admitTheorem "core_axiom" pos p)

core_thm :: String -> TopLevel Theorem
core_thm input =
  do t <- parseCore input
     sc <- getSharedContext
     thm <- io (proofByTerm sc t)
     SV.returnProof thm

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

cryptol_add_path :: FilePath -> TopLevel ()
cryptol_add_path path =
  do rw <- getTopLevelRW
     let ce = rwCryptol rw
     let me = CEnv.eModuleEnv ce
     let me' = me { C.meSearchPath = path : C.meSearchPath me }
     let ce' = ce { CEnv.eModuleEnv = me' }
     let rw' = rw { rwCryptol = ce' }
     putTopLevelRW rw'

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

summarize_verification :: TopLevel ()
summarize_verification =
  do values <- rwProofs <$> getTopLevelRW
     let jspecs  = [ s | SV.VJVMMethodSpec s <- values ]
         lspecs  = [ s | SV.VLLVMCrucibleMethodSpec s <- values ]
         thms    = [ t | SV.VTheorem t <- values ]
         summary = computeVerificationSummary jspecs lspecs thms
     io $ putStrLn $ prettyVerificationSummary summary
