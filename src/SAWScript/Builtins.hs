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
import qualified Control.Exception as Ex
import Data.Char (toLower)
import qualified Data.ByteString as StrictBS
import qualified Data.ByteString.Lazy as BS
import qualified Data.ByteString.Lazy.UTF8 as B
import qualified Data.IntMap as IntMap
import Data.IORef
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
import System.FilePath (hasDrive, (</>))
import System.Process (callCommand, readProcessWithExitCode)
import Text.Printf (printf)
import Text.Read (readMaybe)

import qualified Cryptol.TypeCheck.AST as Cryptol
import qualified Verifier.SAW.Cryptol as Cryptol
import qualified Verifier.SAW.Cryptol.Simpset as Cryptol
import qualified Verifier.SAW.Cryptol.Monadify as Monadify

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
import Verifier.SAW.Recognizer
import Verifier.SAW.Prelude (scEq)
import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedTerm
import qualified Verifier.SAW.Simulator.Concrete as Concrete
import Verifier.SAW.Prim (rethrowEvalError)
import Verifier.SAW.Rewriter
import Verifier.SAW.Testing.Random (prepareSATQuery, runManyTests)
import Verifier.SAW.TypedAST
import qualified Verifier.SAW.Simulator.TermModel as TM
import Verifier.SAW.Term.Pretty (SawDoc, renderSawDoc)

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
import qualified Cryptol.ModuleSystem.Env as C (meSearchPath)
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
import qualified Cryptol.Utils.Ident as C (mkIdent, packModName,
                                           textToModName, PrimIdent(..))
import qualified Cryptol.Utils.RecordMap as C (recordFromFields)

import qualified SAWScript.SBVParser as SBV
import SAWScript.ImportAIG

import SAWScript.AST (getVal, pShow, Located(..))
import SAWScript.Options as Opts
import SAWScript.Proof
import SAWScript.Crucible.Common (PathSatSolver(..))
import SAWScript.TopLevel
import qualified SAWScript.Value as SV
import SAWScript.Value (ProofScript, printOutLnTop, AIGNetwork)

import SAWScript.Crucible.Common.MethodSpec (ppTypedTermType)
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
  nenv <- io . scGetNamingEnv =<< getSharedContext
  return (SV.showsPrecValue opts nenv 0 v "")

definePrim :: Text -> TypedTerm -> TopLevel TypedTerm
definePrim name (TypedTerm (TypedTermSchema schema) rhs) =
  do sc <- getSharedContext
     ty <- io $ Cryptol.importSchema sc Cryptol.emptyEnv schema
     t <- io $ scConstant sc name rhs ty
     return $ TypedTerm (TypedTermSchema schema) t
definePrim _name (TypedTerm tp _) =
  fail $ unlines
    [ "Expected term with Cryptol schema type, but got"
    , show (ppTypedTermType tp)
    ]

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
  return (TypedTerm (TypedTermSchema schema) trm)

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
       return (TypedTerm (TypedTermSchema schema) trm)
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
dsecPrint :: TypedTerm -> TypedTerm -> TopLevel ()
dsecPrint t1 t2 = do
  write_t1 <- Prover.writeSAIGInferLatches t1
  write_t2 <- Prover.writeSAIGInferLatches t2
  io $ withSystemTempFile ".aig" $ \path1 _handle1 ->
       withSystemTempFile ".aig" $ \path2 _handle2 ->
        do write_t1 path1
           write_t2 path2
           callCommand (abcDsec path1 path2)
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
    Right (inLen, outLen, t) -> pure $ TypedTerm (TypedTermSchema schema) t
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

  let ss = emptySimpset :: SV.SAWSimpset
  (_,t') <- io $ replaceTerm sc ss (tpat, trepl) (ttTerm t)

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

isConvertiblePrim :: TypedTerm -> TypedTerm -> TopLevel Bool
isConvertiblePrim x y = do
   sc <- getSharedContext
   io $ scConvertible sc False (ttTerm x) (ttTerm y)

checkConvertiblePrim :: TypedTerm -> TypedTerm -> TopLevel ()
checkConvertiblePrim x y = do
   c <- isConvertiblePrim x y
   printOutLnTop Info (if c
                        then "Convertible"
                        else "Not convertible")


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
    satq <- sequentToSATQuery sc mempty (goalSequent goal)
    testGen <- prepareSATQuery sc satq
    let stats = solverStats "quickcheck" (sequentSharedSize (goalSequent goal))
    runManyTests testGen n >>= \case
       Nothing ->
         do printOutLn opts Info $ "checked " ++ show n ++ " cases."
            return (stats, SolveSuccess (QuickcheckEvidence n (goalSequent goal)))
       Just cex -> return (stats, SolveCounterexample cex)

assumeValid :: ProofScript ()
assumeValid =
  execTactic $ tacticSolve $ \goal ->
  do printOutLnTop Warn $ "WARNING: assuming goal " ++ goalName goal ++ " is valid"
     pos <- SV.getPosition
     let admitMsg = "assumeValid: " <> Text.pack (goalName goal)
     let stats = solverStats "ADMITTED" (sequentSharedSize (goalSequent goal))
     return (stats, SolveSuccess (Admitted admitMsg pos (goalSequent goal)))

assumeUnsat :: ProofScript ()
assumeUnsat =
  execTactic $ tacticSolve $ \goal ->
  do printOutLnTop Warn $ "WARNING: assuming goal " ++ goalName goal ++ " is unsat"
     pos <- SV.getPosition
     let admitMsg = "assumeUnsat: " <> Text.pack (goalName goal)
     let stats = solverStats "ADMITTED" (sequentSharedSize (goalSequent goal))
     return (stats, SolveSuccess (Admitted admitMsg pos (goalSequent goal)))

admitProof :: Text -> ProofScript ()
admitProof msg =
  execTactic $ tacticSolve $ \goal ->
  do printOutLnTop Warn $ "WARNING: admitting goal " ++ goalName goal
     pos <- SV.getPosition
     let stats = solverStats "ADMITTED" (sequentSharedSize (goalSequent goal))
     return (stats, SolveSuccess (Admitted msg pos (goalSequent goal)))

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

goalSummary :: ProofGoal -> String
goalSummary goal = unlines $ concat
  [ [ "Goal " ++ goalName goal ++ " (goal number " ++ (show $ goalNum goal) ++ "): " ++ goalType goal
    , "at " ++ goalLoc goal
    ]
  , if Set.null (goalTags goal) then [] else
      [ unwords ("Tags:" : map show (Set.toList (goalTags goal)))
      ]
  , if null (goalDesc goal) then [] else [ goalDesc goal ]
  ]

write_goal :: String -> ProofScript ()
write_goal fp =
  execTactic $ tacticId $ \goal ->
  do opts <- getTopLevelPPOpts
     sc <- getSharedContext
     liftIO $ do
       nenv <- scGetNamingEnv sc
       let output = prettySequent opts nenv (goalSequent goal)
       writeFile fp (unlines [goalSummary goal, output])

print_goal :: ProofScript ()
print_goal =
  execTactic $ tacticId $ \goal ->
  do opts <- getTopLevelPPOpts
     sc <- getSharedContext
     nenv <- io (scGetNamingEnv sc)
     let output = prettySequent opts nenv (goalSequent goal)
     printOutLnTop Info (unlines [goalSummary goal, output])

print_goal_summary :: ProofScript ()
print_goal_summary =
  execTactic $ tacticId $ \goal ->
    printOutLnTop Info (goalSummary goal)

print_focus :: ProofScript ()
print_focus =
  execTactic $ tacticId $ \goal ->
    do opts <- getTopLevelPPOpts
       sc <- getSharedContext
       nenv <- io (scGetNamingEnv sc)
       case sequentGetFocus (goalSequent goal) of
         Nothing ->
           printOutLnTop Warn "Sequent is not focused"
         Just (Left (i,h)) ->
           let output = ppProp opts nenv h in
           printOutLnTop Info (unlines ["Hypothesis " ++ show i, show output])
         Just (Right (i,c)) ->
           let output = ppProp opts nenv c in
           printOutLnTop Info (unlines ["Conclusion " ++ show i, show output])


goal_num :: ProofScript Int
goal_num =
  execTactic $ tacticId $ \goal ->
    return (goalNum goal)

print_goal_depth :: Int -> ProofScript ()
print_goal_depth n =
  execTactic $ tacticId $ \goal ->
  do opts <- getTopLevelPPOpts
     sc <- getSharedContext
     let opts' = opts { ppMaxDepth = Just n }
     nenv <- io (scGetNamingEnv sc)
     let output = prettySequent opts' nenv (goalSequent goal)
     printOutLnTop Info (unlines [goalSummary goal, output])

printGoalConsts :: ProofScript ()
printGoalConsts =
  execTactic $ tacticId $ \goal ->
  do let cs = sequentConstantSet (goalSequent goal)
     mapM_ (printOutLnTop Info) $
       [ show nm | (_,(nm,_,_)) <- Map.toList cs ]

printGoalSize :: ProofScript ()
printGoalSize =
  execTactic $ tacticId $ \goal ->
  do printOutLnTop Info $ "Goal shared size: " ++ show (sequentSharedSize (goalSequent goal))
     printOutLnTop Info $ "Goal unshared size: " ++ show (sequentTreeSize (goalSequent goal))

resolveNames :: [String] -> TopLevel (Set VarIndex)
resolveNames nms =
  do sc <- getSharedContext
     Set.fromList . mconcat <$> mapM (resolveName sc) nms

-- | Given a user-provided name, resolve it to (potentially several)
-- 'ExtCns' that each represent an unfoldable 'Constant' value or a
-- fresh uninterpreted constant.
-- The given name is searched for in both the local Cryptol environment
-- and the SAWCore naming environment. If it is found in neither, an
-- exception is thrown.
resolveName :: SharedContext -> String -> TopLevel [VarIndex]
resolveName sc nm =
  do cenv <- rwCryptol <$> getTopLevelRW
     scnms <- fmap fst <$> io (scResolveName sc tnm)
     let ?fileReader = StrictBS.readFile
     res <- io $ CEnv.resolveIdentifier cenv tnm
     case res of
       Just cnm ->
         do importedName <- io $ Cryptol.importName cnm
            case importedName of
              ImportedName uri _ ->
                do resolvedName <- io $ scResolveNameByURI sc uri
                   case resolvedName of
                     Just vi -> pure $ vi:scnms
                     Nothing -> fallback scnms
              _ -> fallback scnms
       Nothing -> fallback scnms

 where
 tnm = Text.pack nm
 fallback [] = fail $ "Could not resolve name: " <> show nm
 fallback scnms = pure scnms


normalize_term :: TypedTerm -> TopLevel TypedTerm
normalize_term tt = normalize_term_opaque [] tt

normalize_term_opaque :: [String] -> TypedTerm -> TopLevel TypedTerm
normalize_term_opaque opaque tt =
  do sc <- getSharedContext
     modmap <- io (scGetModuleMap sc)
     idxs <- mconcat <$> mapM (resolveName sc) opaque
     let opaqueSet = Set.fromList idxs
     tm' <- io (TM.normalizeSharedTerm sc modmap mempty mempty opaqueSet (ttTerm tt))
     pure tt{ ttTerm = tm' }

goal_normalize :: [String] -> ProofScript ()
goal_normalize opaque =
  execTactic $ tacticChange $ \goal ->
    do sc <- getSharedContext
       idxs <- mconcat <$> mapM (resolveName sc) opaque
       modmap <- io (scGetModuleMap sc)
       let opaqueSet = Set.fromList idxs
       sqt' <- io $ traverseSequentWithFocus (normalizeProp sc modmap opaqueSet) (goalSequent goal)
       return (sqt', NormalizePropEvidence opaqueSet)

unfocus :: ProofScript ()
unfocus =
  execTactic $ tacticChange $ \goal ->
    do let sqt' = unfocusSequent (goalSequent goal)
       return (sqt', structuralEvidence sqt')

focus_concl :: Integer -> ProofScript ()
focus_concl i =
  execTactic $ tacticChange $ \goal ->
    case focusOnConcl i (goalSequent goal) of
      Nothing -> fail "focus_concl : not enough conclusions"
      Just sqt' -> return (sqt', structuralEvidence sqt')

focus_hyp :: Integer -> ProofScript ()
focus_hyp i =
  execTactic $ tacticChange $ \goal ->
    case focusOnHyp i (goalSequent goal) of
      Nothing -> fail "focus_hyp : not enough hypotheses"
      Just sqt' -> return (sqt', structuralEvidence sqt')

delete_hyps :: [Integer] -> ProofScript ()
delete_hyps hs =
  execTactic $ tacticChange $ \goal ->
    let sqt' = filterHyps (BlackList (Set.fromList hs)) (goalSequent goal)
     in return (sqt', structuralEvidence sqt')

retain_hyps :: [Integer] -> ProofScript ()
retain_hyps hs =
  execTactic $ tacticChange $ \goal ->
    let sqt' = filterHyps (WhiteList (Set.fromList hs)) (goalSequent goal)
     in return (sqt', structuralEvidence sqt')

delete_concl :: [Integer] -> ProofScript ()
delete_concl gs =
  execTactic $ tacticChange $ \goal ->
    let sqt' = filterConcls (BlackList (Set.fromList gs)) (goalSequent goal)
     in return (sqt', structuralEvidence sqt')

retain_concl :: [Integer] -> ProofScript ()
retain_concl gs =
  execTactic $ tacticChange $ \goal ->
    let sqt' = filterConcls (WhiteList (Set.fromList gs)) (goalSequent goal)
     in return (sqt', structuralEvidence sqt')


goal_cut :: Term -> ProofScript ()
goal_cut tm =
  do -- TODO? Theres a bit of duplicated work here
     -- and in boolToProp, termToProp.
     -- maybe we can consolatate
     sc <- SV.scriptTopLevel getSharedContext
     p  <- SV.scriptTopLevel $ io $
            do tp <- scWhnf sc =<< scTypeOf sc tm
               case () of
                 _ | Just () <- asBoolType tp
                   -> boolToProp sc [] tm

                   | Just s <- asSort tp, s == propSort
                   -> termToProp sc tm

                   | otherwise
                   -> fail "goal_cut: expected Bool or Prop term"
     execTactic (tacticCut sc p)

normalize_sequent :: ProofScript ()
normalize_sequent =
  execTactic $ tacticChange $ \goal ->
    do sc <- getSharedContext
       sqt' <- io $ normalizeSequent sc (goalSequent goal)
       return (sqt', NormalizeSequentEvidence sqt')

unfoldGoal :: [String] -> ProofScript ()
unfoldGoal unints =
  execTactic $ tacticChange $ \goal ->
  do sc <- getSharedContext
     unints' <- resolveNames unints
     sqt' <- traverseSequentWithFocus (io . unfoldProp sc unints') (goalSequent goal)
     return (sqt', UnfoldEvidence unints')

simplifyGoal :: SV.SAWSimpset -> ProofScript ()
simplifyGoal ss =
  execTactic $ tacticChange $ \goal ->
  do sc <- getSharedContext
     sqt' <- traverseSequentWithFocus (\p -> snd <$> io (simplifyProp sc ss p)) (goalSequent goal)
     return (sqt', RewriteEvidence [] ss)

simplifyGoalWithLocals :: [Integer] -> SV.SAWSimpset -> ProofScript ()
simplifyGoalWithLocals hs ss =
  execTactic $ tacticChange $ \goal ->
  do sc <- getSharedContext
     ss' <- io (localHypSimpset (goalSequent goal) hs ss)
     sqt' <- traverseSequentWithFocus
               (\p -> snd <$> io (simplifyProp sc ss' p)) (goalSequent goal)
     return (sqt', RewriteEvidence hs ss)

hoistIfsInGoalPrim :: ProofScript ()
hoistIfsInGoalPrim =
  execTactic $ tacticChange $ \goal ->
    do sc <- getSharedContext
       sqt' <- traverseSequentWithFocus (io . hoistIfsInProp sc) (goalSequent goal)
       return (sqt', HoistIfsEvidence)

term_type :: TypedTerm -> TopLevel C.Schema
term_type tt =
  case ttType tt of
    TypedTermSchema sch -> pure sch
    tp -> fail $ unlines
            [ "Term does not have a Cryptol type"
            , show (ppTypedTermType tp)
            ]

goal_eval :: [String] -> ProofScript ()
goal_eval unints =
  execTactic $ tacticChange $ \goal ->
  do sc <- getSharedContext
     unintSet <- resolveNames unints
     sqt' <- traverseSequentWithFocus (io . evalProp sc unintSet) (goalSequent goal)
     return (sqt', EvalEvidence unintSet)

extract_uninterp ::
  [String] {- ^ uninterpred identifiers -} ->
  [String] {- ^ opaque identifiers -} ->
  TypedTerm ->
  TopLevel (TypedTerm, [(String,[(TypedTerm,TypedTerm)])])
extract_uninterp unints opaques tt =
  do sc <- getSharedContext
     idxs <- mconcat <$> mapM (resolveName sc) unints
     let unintSet = Set.fromList idxs
     mmap <- io (scGetModuleMap sc)

     opaqueSet <- Set.fromList . mconcat <$> mapM (resolveName sc) opaques

     boundECRef <- io (newIORef Set.empty)
     let ?recordEC = \ec -> modifyIORef boundECRef (Set.insert ec)
     (tm, repls) <- io (TM.extractUninterp sc mmap mempty mempty unintSet opaqueSet (ttTerm tt))
     boundECSet <- io (readIORef boundECRef)
     let tt' = tt{ ttTerm = tm }

     let f = traverse $ \(ec,vs) ->
               do ectm <- scExtCns sc ec
                  vs'  <- filterCryTerms sc vs
                  pure (ectm, vs')
     repls' <- io (traverse f repls)

     usedECRef <- io (newIORef Set.empty)
     replList <- io $
        forM (zip unints idxs) $ \(nm,idx) ->
           do let ls = fromMaybe [] (Map.lookup idx repls')
              xs <- forM ls $ \(e,vs) ->
                      do e'  <- mkTypedTerm sc e
                         vs' <- tupleTypedTerm sc vs
                         modifyIORef usedECRef (Set.union (getAllExtSet (ttTerm vs')))
                         pure (e',vs')
              pure (nm,xs)
     usedECSet <- io (readIORef usedECRef)

     let boundAndUsed = Set.intersection boundECSet usedECSet
     unless (Set.null boundAndUsed)
       (do ppOpts <- getTopLevelPPOpts
           vs <- io $ forM (Set.toList boundAndUsed) $ \ec ->
                              do pptm <- scPrettyTerm ppOpts <$> scExtCns sc ec
                                 let ppty = scPrettyTerm ppOpts (ecType ec)
                                 return (pptm <> " : " <> ppty)
           printOutLnTop Warn $ unlines $
             [ "WARNING: extracted arguments reference captured variables!"
             , "This usually means one of functions you extracted was used in a higher-order way"
             , "that could not be fully unrolled, or the expression depends on lambda-bound variables."
             , "The results of reasoning about this extraction may be unexpected."
             , "The affected variables are:"
             ] ++ (map ("  "++) vs))

     pure (tt', replList)


congruence_for :: TypedTerm -> TopLevel TypedTerm
congruence_for tt =
  do sc <- getSharedContext
     congTm <- io $ build_congruence sc (ttTerm tt)
     io $ mkTypedTerm sc congTm

-- | Given an input term, construct another term that
--   represents a congruence law for that term.
--   This term will be a Curry-Howard style theorem statement
--   that can be dispatched to solvers, and should have
--   type "Prop".
--
--   This will only work for terms that represent non-dependent
--   functions.
build_congruence :: SharedContext -> Term -> IO Term
build_congruence sc tm =
  do ty <- scTypeOf sc tm
     case asPiList ty of
       ([],_) -> fail "congruence_for: Term is not a function"
       (pis, body) ->
         if looseVars body == emptyBitSet then
           loop pis []
         else
           fail "congruence_for: cannot build congruence for dependent functions"
 where
  loop ((nm,tp):pis) vars =
    if looseVars tp == emptyBitSet then
      do l <- scFreshEC sc (nm <> "_1") tp
         r <- scFreshEC sc (nm <> "_2") tp
         loop pis ((l,r):vars)
     else
       fail "congruence_for: cannot build congruence for dependent functions"

  loop [] vars =
    do lvars <- mapM (scExtCns sc . fst) (reverse vars)
       rvars <- mapM (scExtCns sc . snd) (reverse vars)
       let allVars = concat [ [l,r] | (l,r) <- reverse vars ]

       basel <- scApplyAll sc tm lvars
       baser <- scApplyAll sc tm rvars
       baseeq <- scEqTrue sc =<< scEq sc basel baser

       let f x (l,r) =
             do l' <- scExtCns sc l
                r' <- scExtCns sc r
                eq <- scEqTrue sc =<< scEq sc l' r'
                scFun sc eq x
       finalEq <- foldM f baseeq vars

       scGeneralizeExts sc allVars finalEq


filterCryTerms :: SharedContext -> [Term] -> IO [TypedTerm]
filterCryTerms sc = loop
  where
  loop [] = pure []
  loop (x:xs) =
    do tp <- Cryptol.scCryptolType sc =<< scTypeOf sc x
       case tp of
         Just (Right cty) ->
           do let x' = TypedTerm (TypedTermSchema (C.tMono cty)) x
              xs' <- loop xs
              pure (x':xs')

         _ -> loop xs


beta_reduce_goal :: ProofScript ()
beta_reduce_goal =
  execTactic $ tacticChange $ \goal ->
  do sc <- getSharedContext
     sqt' <- traverseSequentWithFocus (io . betaReduceProp sc) (goalSequent goal)
     return (sqt', ConversionEvidence sqt')

goal_apply :: Theorem -> ProofScript ()
goal_apply thm =
  do sc <- SV.scriptTopLevel getSharedContext
     execTactic (tacticApply sc thm)

goal_exact :: TypedTerm -> ProofScript ()
goal_exact tm =
  do sc <- SV.scriptTopLevel getSharedContext
     execTactic (tacticExact sc (ttTerm tm))

goal_intro_hyp :: ProofScript ()
goal_intro_hyp =
  do sc <- SV.scriptTopLevel getSharedContext
     execTactic (tacticIntroHyps sc 1)

goal_intro_hyps :: Integer -> ProofScript ()
goal_intro_hyps n =
  do sc <- SV.scriptTopLevel getSharedContext
     execTactic (tacticIntroHyps sc n)

goal_revert_hyp :: Integer -> ProofScript ()
goal_revert_hyp i =
  do sc <- SV.scriptTopLevel getSharedContext
     execTactic (tacticRevertHyp sc i)

goal_intro :: Text -> ProofScript TypedTerm
goal_intro s =
  do sc <- SV.scriptTopLevel getSharedContext
     execTactic (tacticIntro sc s)

goal_insert :: Theorem -> ProofScript ()
goal_insert thm =
  do sc <- SV.scriptTopLevel getSharedContext
     execTactic (tacticInsert sc thm [])

goal_insert_and_specialize :: Theorem -> [TypedTerm] -> ProofScript ()
goal_insert_and_specialize thm tms =
  do sc <- SV.scriptTopLevel getSharedContext
     execTactic (tacticInsert sc thm (map ttTerm tms))

goal_specialize_hyp :: [TypedTerm] -> ProofScript ()
goal_specialize_hyp ts =
  do sc <- SV.scriptTopLevel getSharedContext
     execTactic (tacticSpecializeHyp sc (map ttTerm ts))

goal_apply_hyp :: Integer -> ProofScript ()
goal_apply_hyp n =
  do sc <- SV.scriptTopLevel getSharedContext
     execTactic (tacticApplyHyp sc n)

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

goal_has_tags :: [String] -> ProofScript Bool
goal_has_tags tags =
  do s <- get
     case psGoals s of
       g : _ | Set.isSubsetOf (Set.fromList tags) (goalTags g) -> return True
       _ -> return False

goal_has_some_tag :: [String] -> ProofScript Bool
goal_has_some_tag tags =
  do s <- get
     case psGoals s of
       g : _ | not $ Set.disjoint (Set.fromList tags) (goalTags g) -> return True
       _ -> return False

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
         Nothing -> return (stats, SolveSuccess (SolverEvidence stats (goalSequent g)))
         Just a  -> return (stats, SolveCounterexample a)

writeAIGPrim :: FilePath -> Term -> TopLevel ()
writeAIGPrim = Prover.writeAIG

writeSAIGPrim :: FilePath -> TypedTerm -> TopLevel ()
writeSAIGPrim file tt =
  do write_tt <- Prover.writeSAIGInferLatches tt
     io $ write_tt file

writeSAIGComputedPrim :: FilePath -> Term -> Int -> TopLevel ()
writeSAIGComputedPrim = Prover.writeSAIG

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

applyProverToGoal :: (Sequent -> TopLevel (Maybe CEX, SolverStats))
                     -> ProofGoal
                     -> TopLevel (SolverStats, SolveResult)
applyProverToGoal f g = do
  (mb, stats) <- f (goalSequent g)
  case mb of
    Nothing -> return (stats, SolveSuccess (SolverEvidence stats (goalSequent g)))
    Just a  -> return (stats, SolveCounterexample a)

wrapProver ::
  (Sequent -> TopLevel (Maybe CEX, SolverStats)) ->
  ProofScript ()
wrapProver f = execTactic $ tacticSolve $ applyProverToGoal f

wrapW4Prover ::
  ( Set VarIndex -> Bool ->
    Sequent -> TopLevel (Maybe CEX, SolverStats)) ->
  [String] ->
  ProofScript ()
wrapW4Prover f unints = do
  hashConsing <- SV.scriptTopLevel $ gets SV.rwWhat4HashConsing
  unintSet <- SV.scriptTopLevel $ resolveNames unints
  wrapProver $ f unintSet hashConsing

wrapW4ProveExporter ::
  ( Set VarIndex -> Bool -> FilePath ->
    Sequent -> TopLevel (Maybe CEX, SolverStats)) ->
  [String] ->
  String ->
  String ->
  ProofScript ()
wrapW4ProveExporter f unints path ext = do
  hashConsing <- SV.scriptTopLevel $ gets SV.rwWhat4HashConsing
  unintSet <- SV.scriptTopLevel $ resolveNames unints
  execTactic $ tacticSolve $ \g -> do
    let file = path ++ "." ++ goalType g ++ show (goalNum g) ++ ext
    applyProverToGoal (f unintSet hashConsing file) g

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

w4_unint_z3_using :: String -> [String] -> ProofScript ()
w4_unint_z3_using tactic = wrapW4Prover (Prover.proveWhat4_z3_using tactic)

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
  (FilePath -> SATQuery -> TopLevel a) ->
  Set VarIndex ->
  String ->
  String ->
  String ->
  ProofScript ()
proveWithSATExporter exporter unintSet path sep ext =
  execTactic $ tacticSolve $ \g ->
  do let file = path ++ sep ++ goalType g ++ show (goalNum g) ++ ext
     stats <- Prover.proveWithSATExporter exporter unintSet file (goalSequent g)
     return (stats, SolveSuccess (SolverEvidence stats (goalSequent g)))

proveWithPropExporter ::
  (FilePath -> Prop -> TopLevel a) ->
  String ->
  String ->
  String ->
  ProofScript ()
proveWithPropExporter exporter path sep ext =
  execTactic $ tacticSolve $ \g ->
  do let file = path ++ sep ++ goalType g ++ show (goalNum g) ++ ext
     sc <- getSharedContext
     p <- io $ sequentToProp sc (goalSequent g)
     stats <- Prover.proveWithPropExporter exporter file p
     return (stats, SolveSuccess (SolverEvidence stats (goalSequent g)))

offline_aig :: FilePath -> ProofScript ()
offline_aig path =
  proveWithSATExporter Prover.writeAIG_SAT mempty path "." ".aig"

offline_aig_external :: FilePath -> ProofScript ()
offline_aig_external path =
  proveWithSATExporter Prover.writeAIG_SATviaVerilog mempty path "." ".aig"

offline_cnf :: FilePath -> ProofScript ()
offline_cnf path =
  proveWithSATExporter Prover.writeCNF mempty path "." ".cnf"

offline_cnf_external :: FilePath -> ProofScript ()
offline_cnf_external path =
  proveWithSATExporter Prover.writeCNF_SATviaVerilog mempty path "." ".cnf"

offline_coq :: FilePath -> ProofScript ()
offline_coq path = proveWithPropExporter (Prover.writeCoqProp "goal" [] []) path "_" ".v"

offline_extcore :: FilePath -> ProofScript ()
offline_extcore path = proveWithPropExporter Prover.writeCoreProp path "." ".extcore"

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

w4_abc_aiger :: ProofScript ()
w4_abc_aiger = wrapW4Prover Prover.w4AbcAIGER []

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
  io $ checkBooleanSchema (ttType t)
  sc <- getSharedContext
  prop <- io $ predicateToProp sc Universal (ttTerm t)
  pos <- SV.getPosition
  let goal = ProofGoal
             { goalNum  = 0
             , goalType = "prove"
             , goalName = "prove_prim"
             , goalLoc  = show pos
             , goalDesc = ""
             , goalSequent = propToSequent prop
             , goalTags = mempty
             }
  res <- SV.runProofScript script prop goal Nothing "prove_prim" True False
  case res of
    UnfinishedProof pst ->
      printOutLnTop Info $ "prove: " ++ show (length (psGoals pst)) ++ " unsolved subgoal(s)"
    ValidProof _ thm -> SV.recordProof thm
    _ -> return ()
  return res

proveHelper ::
  String ->
  ProofScript () ->
  Term ->
  (Term -> TopLevel Prop) ->
  TopLevel Theorem
proveHelper nm script t f = do
  prop <- f t
  pos <- SV.getPosition
  let goal = ProofGoal
             { goalNum = 0
             , goalType = "prove"
             , goalName = nm
             , goalLoc  = show pos
             , goalDesc = ""
             , goalSequent = propToSequent prop
             , goalTags = mempty
             }
  opts <- rwPPOpts <$> getTopLevelRW
  res <- SV.runProofScript script prop goal Nothing (Text.pack nm) True False
  let failProof pst =
         fail $ "prove: " ++ show (length (psGoals pst)) ++ " unsolved subgoal(s)\n"
                          ++ SV.showsProofResult opts res ""
  case res of
    ValidProof _stats thm ->
      do printOutLnTop Debug $ "Valid: " ++ show (ppTerm (SV.sawPPOpts opts) t)
         SV.returnProof thm
    InvalidProof _stats _cex pst -> failProof pst
    UnfinishedProof pst -> failProof pst

-- | See the inline help for 'prove_by_bv_induction' in the interpreter
--   for a description of what this is doing.
proveByBVInduction ::
  ProofScript () ->
  TypedTerm ->
  TopLevel Theorem
proveByBVInduction script t =
  do sc <- getSharedContext
     opts <- rwPPOpts <$> getTopLevelRW
     ty <- io $ scTypeCheckError sc (ttTerm t)
     io (checkInductionScheme sc opts [] ty) >>= \case
       Nothing -> badTy opts ty
       Just ([],_) -> badTy opts ty
       Just (pis,w) ->

         -- This is a whole bunch of gross SAWCore manipulation to build a custom
         -- induction principle for the user-given theorem statement.
         -- I don't know offhand of a less gross way to do this.

         -- The basic pattern closely follows the definition of BV_complete_induction
         -- from the SAWCore prelude. Here, we reproduce the statement of the corresponding
         -- parts of BV_complete_induction to give a sense of what term we intend to produce
         -- in each of the following sub-parts.

         do wt  <- io $ scNat sc w
            natty <- io $ scNatType sc
            toNat  <- io $ scGlobalDef sc "Prelude.bvToNat"

            -- The result type of the theorem.
            --
            --   (x : Vec w Bool) -> p x
            thmResult <- io $
                do vars <- reverse <$> mapM (scLocalVar sc) [ 0 .. length pis - 1]
                   t1   <- scApplyAllBeta sc (ttTerm t) vars
                   t2   <- scEqTrue sc =<< scTupleSelector sc t1 2 2 -- rightmost tuple element
                   t3   <- scPiList sc pis t2
                   _    <- scTypeCheckError sc t3 -- sanity check
                   return t3

            -- The type of the main hypothesis to the induction scheme. This is what
            -- the user will ultimately be asked to prove. Note that this includes
            -- the induction hypothesis.
            --
            --   ((x : Vec w Bool) -> ((y: Vec w Bool) -> is_bvult w y x -> p y) -> p x)
            thmHyp <- io $
                do vars  <- reverse <$> mapM (scLocalVar sc) [ 0 .. length pis - 1]
                   t1    <- scApplyAllBeta sc (ttTerm t) vars
                   tsz   <- scTupleSelector sc t1 1 2 -- left element
                   tbody <- scEqTrue sc =<< scTupleSelector sc t1 2 2 -- rightmost tuple element
                   tsz_shft   <- incVars sc 0 (length pis) tsz

                   bvult <- scGlobalDef sc "Prelude.bvult"
                   islt  <- scEqTrue sc =<< scApplyAll sc bvult [wt, tsz, tsz_shft]

                   tinner <- scPi sc "_" islt =<< incVars sc 0 1 tbody
                   thyp   <- scPiList sc [ ("i_" <> nm, z) | (nm,z) <- pis ] tinner

                   touter <- scPi sc "_" thyp =<< incVars sc 0 1 tbody
                   scPiList sc pis touter

            -- The "motive" we will pass to the 'Nat_complete_induction' principle.
            --
            --      (\ (n:Nat) -> (x:Vec w Bool) -> IsLeNat (bvToNat w x) n -> p x)
            indMotive <- io $
                do vars   <- reverse <$> mapM (scLocalVar sc) [ 0 .. length pis-1 ]
                   indVar <- scLocalVar sc (length pis)
                   t1     <- scApplyAllBeta sc (ttTerm t) vars
                   tsz    <- scTupleSelector sc t1 1 2 -- left element
                   tsz'   <- scApplyAll sc toNat [wt, tsz]
                   teq    <- scDataTypeApp sc "Prelude.IsLeNat" [tsz', indVar]
                   tbody  <- scEqTrue sc =<< scTupleSelector sc t1 2 2 -- right element
                   t2     <- scPi sc "_" teq =<< incVars sc 0 1 tbody
                   t3     <- scPiList sc pis t2
                   scLambda sc "inductionVar" natty t3

            -- This is the most complicated part of building the induction schema. Here we provide
            -- the proof term required by 'Nat_complete_induction' that shows how to reduce our
            -- current specific case to induction on natural numbers.
            --
            --      \ (H: (x : Vec w Bool) -> ((y: Vec w Bool) -> is_bvult w y x -> p y) -> p x)
            --      \ (n:Nat) ->
            --      \ (Hind : (m : Nat) -> (Hm : IsLtNat m n) -> (y : Vec w Bool) ->
            --                (Hy : IsLeNat (bvToNat w y) m) -> p y) ->
            --      \ (x : Vec w Bool) ->
            --      \ (Hx : IsLeNat (bvToNat w x) n) ->
            --        H x (\ (y:Vec w Bool) -> \ (Hult : is_bvult w y x) ->
            --               Hind (bvToNat w y)
            --                 (IsLeNat_transitive (Succ (bvToNat w y)) (bvToNat w x) n (bvultToIsLtNat w y x Hult) Hx)
            --                 y (IsLeNat_base (bvToNat w y)))

            indHypProof <- io $
                do hEC  <- scFreshEC sc "H" thmHyp
                   hVar <- scExtCns sc hEC
                   nEC  <- scFreshEC sc "n" natty
                   nVar <- scExtCns sc nEC
                   hindEC <- scFreshEC sc "Hind" =<<
                                do var0 <- scLocalVar sc 0
                                   var1 <- scLocalVar sc 1
                                   lt   <- scGlobalApply sc "Prelude.IsLtNat" [var0, nVar]
                                   scPi sc "m" natty =<< scPi sc "_" lt =<< scApplyBeta sc indMotive var1
                   hindVar <- scExtCns sc hindEC
                   varECs <- mapM (uncurry (scFreshEC sc)) pis
                   vars   <- mapM (scExtCns sc) varECs

                   innerVarECs <- mapM (uncurry (scFreshEC sc)) [ ("i_" <> nm, z) | (nm,z) <- pis ]
                   innerVars   <- mapM (scExtCns sc) innerVarECs

                   outersz <- do t1   <- scApplyAllBeta sc (ttTerm t) vars
                                 scTupleSelector sc t1 1 2 -- left element
                   natoutersz <- scApplyAll sc toNat [wt, outersz]

                   innersz <- do t1   <- scApplyAllBeta sc (ttTerm t) innerVars
                                 scTupleSelector sc t1 1 2 -- left element
                   natinnersz <- scApplyAll sc toNat [wt, innersz]

                   succinnersz <- scCtorApp sc "Prelude.Succ" [natinnersz]

                   bvltEC  <- scFreshEC sc "Hult" =<< scEqTrue sc =<< scBvULt sc wt innersz outersz
                   bvltVar <- scExtCns sc bvltEC

                   leEC    <- scFreshEC sc "Hle" =<<
                                 scDataTypeApp sc "Prelude.IsLeNat" [natoutersz, nVar]
                   leVar   <- scExtCns sc leEC

                   refl_inner <- scCtorApp sc "Prelude.IsLeNat_base" [natinnersz]

                   prf     <- do hyx <- scGlobalApply sc "Prelude.bvultToIsLtNat" [wt,innersz,outersz,bvltVar]
                                 scGlobalApply sc "Prelude.IsLeNat_transitive" [succinnersz, natoutersz, nVar, hyx, leVar]
                   inner   <- do body <- scApplyAll sc hindVar ([natinnersz,prf]++innerVars++[refl_inner])
                                 scAbstractExts sc (innerVarECs ++ [bvltEC]) body

                   body <- scApplyAll sc hVar (vars ++ [inner])

                   scAbstractExts sc ([hEC, nEC, hindEC] ++ varECs ++ [leEC]) body

            -- Now we put all the pieces together
            --
            -- \ (Hind : (x : Vec w Bool) -> ((y: Vec w Bool) -> is_bvult w y x -> p y) -> p x) ->
            -- \ (x : Vec x Bool) ->
            --    Nat_complete_induction indMotive (indHypProof Hind) (bvToNat w x) x (IsLeNat_base (bvToNat w x))
            indApp <- io $
                do vars   <- reverse <$> mapM (scLocalVar sc) [ 0 .. length pis-1 ]
                   varH   <- scLocalVar sc (length pis)
                   t1     <- scApplyAllBeta sc (ttTerm t) vars
                   tsz    <- scTupleSelector sc t1 1 2 -- left element
                   tsz'   <- scApplyAll sc toNat [wt, tsz]
                   trefl  <- scCtorApp sc "Prelude.IsLeNat_base" [tsz']
                   indHypArg <- scApplyBeta sc indHypProof varH
                   ind    <- scGlobalApply sc "Prelude.Nat_complete_induction" ([indMotive,indHypArg,tsz'] ++ vars ++ [trefl])
                   ind'   <- scLambdaList sc pis ind
                   ind''  <- scLambda sc "Hind" thmHyp ind'

                   _tp    <- scTypeCheckError sc ind'' -- sanity check
                   return ind''

            indAppTT <- io $ mkTypedTerm sc indApp

            -- First produce a theorem value for our custom induction schemd by providing the
            -- above as direct proof term.
            ind_scheme_goal <- io $ scFun sc thmHyp thmResult
            ind_scheme_theorem <- proveHelper "bv_induction_scheme" (goal_exact indAppTT) ind_scheme_goal (io . termToProp sc)

            -- Now, set up a proof to actually prove the statement of interest by first immediately applying
            -- our constructed induction schema, and then using the user-provided proof script.
            let script' = goal_apply ind_scheme_theorem >> script
            proveHelper "prove_by_bv_induction" script' thmResult (io . termToProp sc)

 where
  -- Here, we expect to see a collection of lambda bound terms, followed
  -- by a tuple.  The first component must be a bitvector value, defining
  -- the value we are performing induction on.  The second component is
  -- a boolean value defining the proposition we are attempting to prove.
  --
  -- Return a list of the names and types of the lambda-bound variables,
  -- and the width of the bitvector we are doing induction on.
  checkInductionScheme sc opts pis ty =
    do ty' <- scWhnf sc ty
       case asPi ty' of
         Just (nm,tp,body) -> checkInductionScheme sc opts ((nm,tp):pis) body
         Nothing ->
           case asTupleType ty' of
             Just [bv, bool] ->
               do bool' <- scWhnf sc bool
                  bv'   <- scWhnf sc bv
                  case (asVectorType bv', asBoolType bool') of
                    (Just (w,vbool), Just ()) ->
                      do w' <- scWhnf sc w
                         vbool' <- scWhnf sc vbool
                         case (asNat w', asBoolType vbool') of
                           (Just n, Just ()) -> return (Just (reverse pis, n))
                           _ -> return Nothing
                    _ -> return Nothing
             _ -> return Nothing

  badTy opts ty =
    fail $ unlines [ "Incorrect type for proof by induction!"
                   , "Run `:help prove_by_bv_induction` to see a description of what is expected."
                   , show (ppTerm (SV.sawPPOpts opts) ty)
                   ]

provePrintPrim ::
  ProofScript () ->
  TypedTerm ->
  TopLevel Theorem
provePrintPrim script t = do
  sc <- getSharedContext
  proveHelper "prove_print" script (ttTerm t) $ io . predicateToProp sc Universal

provePropPrim ::
  ProofScript () ->
  TypedTerm ->
  TopLevel Theorem
provePropPrim script t = do
  sc <- getSharedContext
  proveHelper "prove_extcore" script (ttTerm t) $ io . termToProp sc

satPrim ::
  ProofScript () ->
  TypedTerm ->
  TopLevel SV.SatResult
satPrim script t =
  do io $ checkBooleanSchema (ttType t)
     sc <- getSharedContext
     prop <- io $ predicateToProp sc Existential (ttTerm t)
     pos <- SV.getPosition
     let goal = ProofGoal
                { goalNum = 0
                , goalType = "sat"
                , goalName = "sat"
                , goalLoc  = show pos
                , goalDesc = ""
                , goalSequent = propToSequent prop
                , goalTags = mempty
                }
     res <- SV.runProofScript script prop goal Nothing "sat" False False
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

cryptolSimpset :: TopLevel SV.SAWSimpset
cryptolSimpset =
  do sc <- getSharedContext
     io $ Cryptol.mkCryptolSimpset sc

addPreludeEqs :: [Text] -> SV.SAWSimpset -> TopLevel SV.SAWSimpset
addPreludeEqs names ss = do
  sc <- getSharedContext
  eqRules <- io $ mapM (scEqRewriteRule sc) (map qualify names)
  return (addRules eqRules ss)
    where qualify = mkIdent (mkModuleName ["Prelude"])

addCryptolEqs :: [Text] -> SV.SAWSimpset -> TopLevel SV.SAWSimpset
addCryptolEqs names ss = do
  sc <- getSharedContext
  eqRules <- io $ mapM (scEqRewriteRule sc) (map qualify names)
  return (addRules eqRules ss)
    where qualify = mkIdent (mkModuleName ["Cryptol"])

add_core_defs :: Text -> [Text] -> SV.SAWSimpset -> TopLevel SV.SAWSimpset
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

add_prelude_defs :: [Text] -> SV.SAWSimpset -> TopLevel SV.SAWSimpset
add_prelude_defs = add_core_defs "Prelude"

add_cryptol_defs :: [Text] -> SV.SAWSimpset -> TopLevel SV.SAWSimpset
add_cryptol_defs = add_core_defs "Cryptol"

rewritePrim :: SV.SAWSimpset -> TypedTerm -> TopLevel TypedTerm
rewritePrim ss (TypedTerm schema t) = do
  sc <- getSharedContext
  (_,t') <- io $ rewriteSharedTerm sc ss t
  return (TypedTerm schema t')

unfold_term :: [String] -> TypedTerm -> TopLevel TypedTerm
unfold_term unints (TypedTerm schema t) = do
  sc <- getSharedContext
  unints' <- mconcat <$> mapM (resolveName sc) unints
  t' <- io $ scUnfoldConstants sc unints' t
  return (TypedTerm schema t')

beta_reduce_term :: TypedTerm -> TopLevel TypedTerm
beta_reduce_term (TypedTerm schema t) = do
  sc <- getSharedContext
  t' <- io $ betaNormalize sc t
  return (TypedTerm schema t')

addsimp :: Theorem -> SV.SAWSimpset -> TopLevel SV.SAWSimpset
addsimp thm ss =
  do sc <- getSharedContext
     io (propToRewriteRule sc (thmProp thm) (Just (thmNonce thm))) >>= \case
       Nothing -> fail "addsimp: theorem not an equation"
       Just rule -> pure (addRule rule ss)

addsimp_shallow :: Theorem -> SV.SAWSimpset -> TopLevel SV.SAWSimpset
addsimp_shallow thm ss =
  do sc <- getSharedContext
     io (propToRewriteRule sc (thmProp thm) (Just (thmNonce thm))) >>= \case
       Nothing -> fail "addsimp: theorem not an equation"
       Just rule -> pure (addRule (shallowRule rule) ss)

-- TODO: remove this, it implicitly adds axioms
addsimp' :: Term -> SV.SAWSimpset -> TopLevel SV.SAWSimpset
addsimp' t ss =
  case ruleOfProp t Nothing of
    Nothing -> fail "addsimp': theorem not an equation"
    Just rule -> pure (addRule rule ss)

addsimps :: [Theorem] -> SV.SAWSimpset -> TopLevel SV.SAWSimpset
addsimps thms ss = foldM (flip addsimp) ss thms

addsimps' :: [Term] -> SV.SAWSimpset -> TopLevel SV.SAWSimpset
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
            opts <- getTopLevelPPOpts
            io $ checkSequent sc opts (goalSequent g)

fixPos :: Pos
fixPos = PosInternal "FIXME"

freshSymbolicPrim :: Text -> C.Schema -> TopLevel TypedTerm
freshSymbolicPrim x schema@(C.Forall [] [] ct) = do
  sc <- getSharedContext
  cty <- io $ Cryptol.importType sc Cryptol.emptyEnv ct
  tm <- io $ scFreshGlobal sc x cty
  return $ TypedTerm (TypedTermSchema schema) tm
freshSymbolicPrim _ _ =
  fail "Can't create fresh symbolic variable of non-ground type."

abstractSymbolicPrim :: TypedTerm -> TopLevel TypedTerm
abstractSymbolicPrim (TypedTerm _ t) = do
  sc <- getSharedContext
  io (mkTypedTerm sc =<< bindAllExts sc t)

bindAllExts :: SharedContext -> Term -> IO Term
bindAllExts sc body = scAbstractExts sc (getAllExts body) body

term_apply :: TypedTerm -> [TypedTerm] -> TopLevel TypedTerm
term_apply fn args =
  do sc <- getSharedContext
     io $ applyTypedTerms sc fn args

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

implies_term :: TypedTerm -> TypedTerm -> TopLevel TypedTerm
implies_term x y =
  do sc <- getSharedContext
     -- check that the given terms are props
     _ <- io $ termToProp sc (ttTerm x)
     _ <- io $ termToProp sc (ttTerm y)
     z <- io $ scFun sc (ttTerm x) (ttTerm y)
     io $ mkTypedTerm sc z

generalize_term :: [TypedTerm] -> TypedTerm -> TopLevel TypedTerm
generalize_term vars tt =
  do tecs <- traverse checkVar vars
     sc <- getSharedContext
     tm <- io $ scGeneralizeExts sc (map tecExt tecs) (ttTerm tt)
     _tp <- io $ scTypeCheckError sc tm -- sanity check the term
     io $ mkTypedTerm sc tm

  where
    checkVar v =
      case asTypedExtCns v of
        Just tec -> pure tec
        Nothing -> fail "generalize_term: argument not a valid symbolic variable"

-- | Apply the given Term to the given values, and evaluate to a
-- final value.
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
  m <- rwTypes <$> SV.getMergedEnv
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

failPrim :: String -> TopLevel SV.Value
failPrim msg = fail msg

failsPrim :: TopLevel SV.Value -> TopLevel ()
failsPrim m = do
  topRO <- getTopLevelRO
  topRW <- getTopLevelRW
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
  case ttType t of
    TypedTermSchema (C.Forall [] [] (C.tIsBit -> True)) -> return ()
    _ -> fail "eval_bool: not type Bit"
  unless (null (getAllExts (ttTerm t))) $
    fail "eval_bool: term contains symbolic variables"
  v <- io $ rethrowEvalError $ SV.evaluateTypedTerm sc t
  return (C.fromVBit v)

eval_int :: TypedTerm -> TopLevel Integer
eval_int t = do
  sc <- getSharedContext
  cenv <- fmap rwCryptol getTopLevelRW
  let cfg = CEnv.meSolverConfig (CEnv.eModuleEnv cenv)
  unless (null (getAllExts (ttTerm t))) $
    fail "term contains symbolic variables"
  opts <- getOptions
  t' <- io $ defaultTypedTerm opts sc cfg t
  case ttType t' of
    TypedTermSchema (C.Forall [] [] (isInteger -> True)) -> return ()
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
     a <- case ttType tt0 of
            TypedTermSchema (C.Forall [] [] a) -> return a
            _ -> fail "list_term: not a monomorphic element type"
     let eqa (TypedTermSchema (C.Forall [] [] x)) = a == x
         eqa _ = False
     unless (all eqa (map ttType tts)) $
       fail "list_term: non-uniform element types"

     a' <- io $ Cryptol.importType sc Cryptol.emptyEnv a
     trm <- io $ scVectorReduced sc a' (map ttTerm tts)
     let n = C.tNum (length tts)
     return (TypedTerm (TypedTermSchema (C.tMono (C.tSeq n a))) trm)

eval_list :: TypedTerm -> TopLevel [TypedTerm]
eval_list t = do
  sc <- getSharedContext
  (n, a) <-
    case ttType t of
      TypedTermSchema (C.Forall [] [] (C.tIsSeq -> Just (C.tIsNum -> Just n, a))) -> return (n, a)
      _ -> fail "eval_list: not a monomorphic array type"
  n' <- io $ scNat sc (fromInteger n)
  a' <- io $ Cryptol.importType sc Cryptol.emptyEnv a
  idxs <- io $ traverse (scNat sc) $ map fromInteger [0 .. n - 1]
  ts <- io $ traverse (scAt sc n' a' (ttTerm t)) idxs
  return (map (TypedTerm (TypedTermSchema (C.tMono a))) ts)

term_theories :: [String] -> TypedTerm -> TopLevel [String]
term_theories unints t = do
  sc <- getSharedContext
  unintSet <- resolveNames unints
  hashConsing <- gets SV.rwWhat4HashConsing
  prop <- io (predicateToProp sc Universal (ttTerm t))
  Prover.what4Theories unintSet hashConsing (propToSequent prop)

default_typed_term :: TypedTerm -> TopLevel TypedTerm
default_typed_term tt = do
  sc <- getSharedContext
  cenv <- fmap rwCryptol getTopLevelRW
  let cfg = CEnv.meSolverConfig (CEnv.eModuleEnv cenv)
  opts <- getOptions
  io $ defaultTypedTerm opts sc cfg tt

-- | Default the values of the type variables in a typed term.
defaultTypedTerm :: Options -> SharedContext -> C.SolverConfig -> TypedTerm -> IO TypedTerm
defaultTypedTerm opts sc cfg tt@(TypedTerm (TypedTermSchema schema) trm)
  | null (C.sVars schema) = return tt
  | otherwise = do
  mdefault <- C.withSolver (return ()) cfg (\s -> C.defaultReplExpr s undefined schema)
  let inst = do (soln, _) <- mdefault
                mapM (`lookup` soln) (C.sVars schema)
  case inst of
    Nothing -> return (TypedTerm (TypedTermSchema schema) trm)
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
      return (TypedTerm (TypedTermSchema schema') trm'')
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

defaultTypedTerm _opts _sc _cfg tt = return tt


eval_size :: C.Schema -> TopLevel Integer
eval_size s =
  case s of
    C.Forall [] [] t ->
      case C.evalType mempty t of
        Left (C.Nat x) -> return x
        Left C.Inf     -> fail "eval_size: illegal infinite size"
        Right _        -> fail "eval_size: not a numeric type"
    _ -> fail "eval_size: unsupported polymorphic type"

int_to_term :: Int -> TopLevel TypedTerm
int_to_term i
  | i < 0 =
     do sc  <- getSharedContext
        tm  <- io (scNat sc (fromInteger (negate (toInteger i))))
        tm' <- io (scIntNeg sc =<< scNatToInt sc tm)
        io (mkTypedTerm sc tm')
  | otherwise =
     do sc  <- getSharedContext
        tm  <- io (scNat sc (fromIntegral i))
        tm' <- io (scNatToInt sc tm)
        io (mkTypedTerm sc tm')

nat_to_term :: Int -> TopLevel TypedTerm
nat_to_term i
  | i >= 0 =
      do sc <- getSharedContext
         tm <- io $ scNat sc (fromIntegral i)
         io $ mkTypedTerm sc tm

  | otherwise =
      fail ("nat_to_term: negative value " ++ show i)


size_to_term :: C.Schema -> TopLevel TypedTerm
size_to_term s =
  do sc <- getSharedContext
     tm <- io $ case s of
                  C.Forall [] [] t ->
                    case C.evalType mempty t of
                      Left (C.Nat x) | x >= 0 ->
                        scCtorApp sc "Cryptol.TCNum" =<< sequence [scNat sc (fromInteger x)]
                      Left C.Inf -> scCtorApp sc "Cryptol.TCInf" []
                      _ -> fail "size_to_term: not a numeric type"
                  _ -> fail "size_to_term: unsupported polymorphic type"

     return (TypedTerm (TypedTermKind C.KNum) tm)

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

parseCoreMod :: String -> String -> TopLevel Term
parseCoreMod mnm_str input =
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
     let mnm =
           mkModuleName $ Text.splitOn (Text.pack ".") $ Text.pack mnm_str
     _ <- io $ scFindModule sc mnm -- Check that mnm exists
     err_or_t <- io $ runTCM (typeInferComplete uterm) sc (Just mnm) []
     case err_or_t of
       Left err -> fail (show err)
       Right (TC.TypedTerm x _) -> return x

parseCore :: String -> TopLevel Term
parseCore = parseCoreMod "Cryptol"

parse_core :: String -> TopLevel TypedTerm
parse_core input = do
  t <- parseCore input
  sc <- getSharedContext
  io $ mkTypedTerm sc t

parse_core_mod :: String -> String -> TopLevel TypedTerm
parse_core_mod mnm input = do
  t <- parseCoreMod mnm input
  sc <- getSharedContext
  io $ mkTypedTerm sc t

prove_core :: ProofScript () -> String -> TopLevel Theorem
prove_core script input =
  do sc <- getSharedContext
     t <- parseCore input
     p <- io (termToProp sc t)
     pos <- SV.getPosition
     opts <- rwPPOpts <$> getTopLevelRW
     let goal = ProofGoal
                { goalNum = 0
                , goalType = "prove"
                , goalName = "prove_core"
                , goalLoc  = show pos
                , goalDesc = ""
                , goalSequent = propToSequent p
                , goalTags = mempty
                }
     res <- SV.runProofScript script p goal Nothing "prove_core" True False
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
     db <- SV.getTheoremDB
     thm <- io (admitTheorem db "core_axiom" p pos "core_axiom")
     SV.returnProof thm

core_thm :: String -> TopLevel Theorem
core_thm input =
  do t <- parseCore input
     sc <- getSharedContext
     pos <- SV.getPosition
     db <- SV.getTheoremDB
     thm <- io (proofByTerm sc db t pos "core_thm")
     SV.returnProof thm

specialize_theorem :: Theorem -> [TypedTerm] -> TopLevel Theorem
specialize_theorem thm ts =
  do sc <- getSharedContext
     db <- SV.getTheoremDB
     pos <- SV.getPosition
     thm' <- io (specializeTheorem sc db pos "specialize_theorem" thm (map ttTerm ts))
     SV.returnProof thm'

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
      return (n', TypedTerm (TypedTermSchema s') t')

cryptol_load :: (FilePath -> IO StrictBS.ByteString) -> FilePath -> TopLevel CryptolModule
cryptol_load fileReader path = do
  sc <- getSharedContext
  rw <- getTopLevelRW
  let ce = rwCryptol rw
  let ?fileReader = fileReader
  (m, ce') <- io $ CEnv.loadCryptolModule sc CEnv.defaultPrimitiveOptions ce path
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

cryptol_add_prim :: String -> String -> TypedTerm -> TopLevel ()
cryptol_add_prim mnm nm trm =
  do rw <- getTopLevelRW
     let env = rwCryptol rw
     let prim_name =
           C.PrimIdent (C.textToModName $ Text.pack mnm) (Text.pack nm)
     let env' =
           env { CEnv.ePrims =
                   Map.insert prim_name (ttTerm trm) (CEnv.ePrims env) }
     putTopLevelRW (rw { rwCryptol = env' })

cryptol_add_prim_type :: String -> String -> TypedTerm -> TopLevel ()
cryptol_add_prim_type mnm nm tp =
  do rw <- getTopLevelRW
     let env = rwCryptol rw
     let prim_name =
           C.PrimIdent (C.textToModName $ Text.pack mnm) (Text.pack nm)
     let env' = env { CEnv.ePrimTypes =
                        Map.insert prim_name (ttTerm tp) (CEnv.ePrimTypes env) }
     putTopLevelRW (rw { rwCryptol = env' })

-- | Call 'Cryptol.importSchema' using a 'CEnv.CryptolEnv'
importSchemaCEnv :: SharedContext -> CEnv.CryptolEnv -> Cryptol.Schema ->
                    IO Term
importSchemaCEnv sc cenv schema =
  do cry_env <- let ?fileReader = StrictBS.readFile in CEnv.mkCryEnv cenv
     Cryptol.importSchema sc cry_env schema

monadifyTypedTerm :: SharedContext -> TypedTerm -> TopLevel TypedTerm
monadifyTypedTerm sc t =
  do rw <- get
     let menv = rwMonadify rw
     (ret_t, menv') <-
       liftIO $
       case ttType t of
         TypedTermSchema schema ->
           do tp <- importSchemaCEnv sc (rwCryptol rw) schema
              Monadify.monadifyTermInEnv sc menv (ttTerm t) tp
         TypedTermKind _ ->
           fail "monadify_term applied to a type"
         TypedTermOther tp ->
           Monadify.monadifyTermInEnv sc menv (ttTerm t) tp
     modify (\s -> s { rwMonadify = menv' })
     tp <- liftIO $ scTypeOf sc ret_t
     return $ TypedTerm (TypedTermOther tp) ret_t

-- | Ensure that a 'TypedTerm' has been monadified
ensureMonadicTerm :: SharedContext -> TypedTerm -> TopLevel TypedTerm
ensureMonadicTerm sc t
  | TypedTermOther tp <- ttType t =
    io (Prover.isCompFunType sc tp) >>= \case
      True -> return t
      False -> monadifyTypedTerm sc t
ensureMonadicTerm sc t = monadifyTypedTerm sc t

-- | A wrapper for either 'Prover.askMRSolver' or 'Prover.assumeMRSolver' from
-- @MRSolver.hs@: if the first argument is @Just str@, prints out @str@
-- followed by an abridged version of the refinement being asked, then calls
-- the given function, returning how long it took to execute
mrSolver :: (SharedContext -> Prover.MREnv -> Maybe Integer -> Term -> Term -> IO a) ->
            Maybe SawDoc -> SharedContext -> TypedTerm -> TypedTerm ->
            TopLevel (NominalDiffTime, a)
mrSolver f printStr sc t1 t2 =
  do env <- rwMRSolverEnv <$> get
     m1 <- collapseEta <$> ttTerm <$> ensureMonadicTerm sc t1
     m2 <- collapseEta <$> ttTerm <$> ensureMonadicTerm sc t2
     case printStr of
       Nothing -> return ()
       Just str -> printOutLnTop Info $ renderSawDoc defaultPPOpts $
         "[MRSolver] " <> str <> ": " <> ppTmHead m1 <>
                               " |= " <> ppTmHead m2
     time1 <- liftIO getCurrentTime
     res <- io $ f sc env Nothing m1 m2
     time2 <- liftIO getCurrentTime
     return (diffUTCTime time2 time1, res)
  where -- Turn a term of the form @\x1 ... xn -> f x1 ... xn@ into @f@
        collapseEta :: Term -> Term
        collapseEta (asLambdaList -> (lamVars,
                     asApplyAll -> (t@(smallestFreeVar -> Nothing),
                                    mapM asLocalVar -> Just argVars)))
          | argVars == [(length lamVars - 1), (length lamVars - 2) .. 0] = t
        collapseEta t = t
        -- Pretty-print the name of the top-level function call, followed by
        -- "..." if it is given any arguments, or just "..." if there is no
        -- top-level call
        ppTmHead :: Term -> SawDoc
        ppTmHead (asLambdaList -> (_,
                  asApplyAll -> (t@(
                  Prover.asProjAll -> (
                  Monadify.asTypedGlobalDef -> Just _, _)), args))) =
          ppTerm defaultPPOpts t <> if length args > 0 then " ..." else ""
        ppTmHead _ = "..."

-- | Run Mr Solver to prove that the first term refines the second, adding
-- any relevant 'Prover.FunAssump's to the 'Prover.MREnv' if the first argument
-- is true and this can be done, or printing an error message and exiting if it
-- cannot.
mrSolverProve :: Bool -> SharedContext -> TypedTerm -> TypedTerm -> TopLevel ()
mrSolverProve addToEnv sc t1 t2 =
  do dlvl <- Prover.mreDebugLevel <$> rwMRSolverEnv <$> get
     let printStr = if addToEnv then "Proving" else "Testing"
     (diff, res) <- mrSolver Prover.askMRSolver (Just printStr) sc t1 t2
     case res of
       Left err | dlvl == 0 ->
         io (putStrLn $ Prover.showMRFailure err) >>
         printOutLnTop Info (printf "[MRSolver] Failure in %s" (show diff)) >>
         io (Exit.exitWith $ Exit.ExitFailure 1)
       Left err ->
         -- we ignore the MRFailure context here since it will have already
         -- been printed by the debug trace
         io (putStrLn $ Prover.showMRFailureNoCtx err) >>
         printOutLnTop Info (printf "[MRSolver] Failure in %s" (show diff)) >>
         io (Exit.exitWith $ Exit.ExitFailure 1)
       Right (Just (fnm, fassump)) | addToEnv ->
         let assump_str = case Prover.fassumpRHS fassump of
                            Prover.OpaqueFunAssump _ _ -> "an opaque"
                            Prover.RewriteFunAssump _ -> "a rewrite" in
         printOutLnTop Info (
           printf "[MRSolver] Success in %s, added as %s assumption"
                  (show diff) (assump_str :: String)) >>
         modify (\rw -> rw { rwMRSolverEnv =
           Prover.mrEnvAddFunAssump fnm fassump (rwMRSolverEnv rw) })
       _ ->
         printOutLnTop Info $ printf "[MRSolver] Success in %s" (show diff)

-- | Run Mr Solver to prove that the first term refines the second, returning
-- true iff this can be done. This function will not modify the 'Prover.MREnv'.
mrSolverQuery :: SharedContext -> TypedTerm -> TypedTerm -> TopLevel Bool
mrSolverQuery sc t1 t2 =
  do dlvl <- Prover.mreDebugLevel <$> rwMRSolverEnv <$> get
     (diff, res) <- mrSolver Prover.askMRSolver (Just "Querying") sc t1 t2
     case res of
       Left _ | dlvl == 0 ->
         printOutLnTop Info (printf "[MRSolver] Failure in %s" (show diff)) >>
         return False
       Left err ->
         -- we ignore the MRFailure context here since it will have already
         -- been printed by the debug trace
         io (putStrLn $ Prover.showMRFailureNoCtx err) >>
         printOutLnTop Info (printf "[MRSolver] Failure in %s" (show diff)) >>
         return False
       Right _ ->
         printOutLnTop Info (printf "[MRSolver] Success in %s" (show diff)) >>
         return True

-- | Generate the 'Prover.FunAssump' which corresponds to the given refinement
-- and add it to the 'Prover.MREnv'
mrSolverAssume :: SharedContext -> TypedTerm -> TypedTerm -> TopLevel ()
mrSolverAssume sc t1 t2 =
  do dlvl <- Prover.mreDebugLevel <$> rwMRSolverEnv <$> get
     (_, res) <- mrSolver Prover.assumeMRSolver (Just "Assuming") sc t1 t2
     case res of
       Left err | dlvl == 0 ->
         io (putStrLn $ Prover.showMRFailure err) >>
         printOutLnTop Info (printf "[MRSolver] Failure") >>
         io (Exit.exitWith $ Exit.ExitFailure 1)
       Left err ->
         -- we ignore the MRFailure context here since it will have already
         -- been printed by the debug trace
         io (putStrLn $ Prover.showMRFailureNoCtx err) >>
         printOutLnTop Info (printf "[MRSolver] Failure") >>
         io (Exit.exitWith $ Exit.ExitFailure 1)
       Right (Just (fnm, fassump)) ->
         printOutLnTop Info (
           printf "[MRSolver] Success, added as an opaque assumption") >>
         modify (\rw -> rw { rwMRSolverEnv =
           Prover.mrEnvAddFunAssump fnm fassump (rwMRSolverEnv rw) })
       _ ->
         printOutLnTop Info $ printf $
           "[MRSolver] Failure, given refinement cannot be interpreted as" ++
                     " an assumption"

-- | Set the debug level of the 'Prover.MREnv'
mrSolverSetDebug :: Int -> TopLevel ()
mrSolverSetDebug dlvl =
  modify (\rw -> rw { rwMRSolverEnv =
                        Prover.mrEnvSetDebugLevel dlvl (rwMRSolverEnv rw) })

setMonadification :: SharedContext -> String -> String -> TopLevel ()
setMonadification sc cry_str saw_str =
  do rw <- get

     -- Step 1: convert the first string to a Cryptol name
     cry_nm <-
       let ?fileReader = StrictBS.readFile in
       liftIO (CEnv.resolveIdentifier
               (rwCryptol rw) (Text.pack cry_str)) >>= \case
       Just n -> return n
       Nothing -> fail ("No such Cryptol identifer: " ++ cry_str)
     cry_nmi <- liftIO $ Cryptol.importName cry_nm

     -- Step 2: get the monadified type for this Cryptol name
     --
     -- FIXME: not sure if this is the correct way to get the type of a Cryptol
     -- name, so we are falling back on just translating the name to SAW core
     -- and monadifying its type there
     cry_saw_tp <-
       liftIO $
       case Map.lookup cry_nm (CEnv.eExtraTypes $ rwCryptol rw) of
         Just schema ->
           -- putStrLn ("Found Cryptol type for name: " ++ show cry_str) >>
           importSchemaCEnv sc (rwCryptol rw) schema
         Nothing
           | Just cry_nm_trans <- Map.lookup cry_nm (CEnv.eTermEnv $
                                                     rwCryptol rw) ->
             -- putStrLn ("No Cryptol type for name: " ++ cry_str) >>
             scTypeOf sc cry_nm_trans
         _ -> fail ("Could not find type for Cryptol name: " ++ cry_str)
     cry_mon_tp <- liftIO $ Monadify.monadifyCompleteArgType sc cry_saw_tp

     -- Step 3: convert the second string to a typed SAW core term, and if it
     -- has an existing macro, check that it has the same type as the type for
     -- the cryptol name, or if no macro exists, check that it has the same
     -- type as the monadified type for the Cryptol name and generate a macro
     -- which maps the Cryptol name to the SAW core term
     let saw_ident = parseIdent saw_str
     saw_trm <- liftIO $ scGlobalDef sc saw_ident
     saw_tp <- liftIO $ scTypeOf sc saw_trm
     let (tp_to_check, macro) =
           case Map.lookup (ModuleIdentifier saw_ident) (rwMonadify rw) of
             Just existing_macro -> (cry_saw_tp, existing_macro)
             Nothing -> (cry_mon_tp, Monadify.argGlobalMacro cry_nmi saw_ident)
     liftIO $ scCheckSubtype sc Nothing (TC.TypedTerm saw_trm saw_tp) tp_to_check

     -- Step 4: Add the generated macro
     put (rw { rwMonadify = Map.insert cry_nmi macro (rwMonadify rw) })

parseSharpSATResult :: String -> Maybe Integer
parseSharpSATResult s = parse (lines s)
  where
    parse (h : n : _) | "# solutions" `isPrefixOf` h = readMaybe n
    parse (_ : rest) = parse rest
    parse [] = Nothing

sharpSAT :: TypedTerm -> TopLevel Integer
sharpSAT t = do
  tmp <- io $ emptySystemTempFile "sharpSAT-input"
  Prover.write_cnf tmp t
  (_ec, out, _err) <- io $ readProcessWithExitCode "sharpSAT" [tmp] ""
  io $ removeFile tmp
  case parseSharpSATResult out of
    Nothing -> fail $ "Garbled result from sharpSAT\n\n" ++ out
    Just n -> return n

approxmc :: TypedTerm -> TopLevel ()
approxmc t = do
  tmp <- io $ emptySystemTempFile "approxmc-input"
  Prover.write_cnf tmp t
  (_ec, out, _err) <- io $ readProcessWithExitCode "approxmc" [tmp] ""
  io $ removeFile tmp
  let msg = filter ("[appmc] Number of solutions is" `isPrefixOf`) (lines out)
  case msg of
    [l] -> io $ putStrLn l
    _ -> fail $ "Garbled result from approxmc\n\n" ++ out

set_path_sat_solver :: String -> TopLevel ()
set_path_sat_solver nm =
  case map toLower nm of
    "z3"    -> modify (\rw -> rw{ rwPathSatSolver = PathSat_Z3 })
    "yices" -> modify (\rw -> rw{ rwPathSatSolver = PathSat_Yices })
    _ -> fail $ "Unknown path sat solver: " ++ show nm

summarize_verification :: TopLevel ()
summarize_verification =
  do values <- rwProofs <$> getTopLevelRW
     let jspecs  = [ s | SV.VJVMMethodSpec s <- values ]
         lspecs  = [ s | SV.VLLVMCrucibleMethodSpec s <- values ]
         thms    = [ t | SV.VTheorem t <- values ]
     db <- SV.getTheoremDB
     summary <- io (computeVerificationSummary db jspecs lspecs thms)
     opts <- fmap (SV.sawPPOpts . rwPPOpts) getTopLevelRW
     nenv <- io . scGetNamingEnv =<< getSharedContext
     io $ putStrLn $ prettyVerificationSummary opts nenv summary

summarize_verification_json :: String -> TopLevel ()
summarize_verification_json fpath =
  do values <- rwProofs <$> getTopLevelRW
     let jspecs  = [ s | SV.VJVMMethodSpec s <- values ]
         lspecs  = [ s | SV.VLLVMCrucibleMethodSpec s <- values ]
         thms    = [ t | SV.VTheorem t <- values ]
     db <- SV.getTheoremDB
     summary <- io (computeVerificationSummary db jspecs lspecs thms)
     io (writeFile fpath (jsonVerificationSummary summary))

writeVerificationSummary :: TopLevel ()
writeVerificationSummary = do
  do
    db <- SV.getTheoremDB
    values <- rwProofs <$> getTopLevelRW
    let jspecs  = [ s | SV.VJVMMethodSpec s <- values ]
        lspecs  = [ s | SV.VLLVMCrucibleMethodSpec s <- values ]
        thms    = [ t | SV.VTheorem t <- values ]
    summary <- io (computeVerificationSummary db jspecs lspecs thms)
    opts <- roOptions <$> getTopLevelRO
    dir <- roInitWorkDir <$> getTopLevelRO
    nenv <- io . scGetNamingEnv =<< getSharedContext
    ppOpts <- fmap (SV.sawPPOpts . rwPPOpts) getTopLevelRW

    case summaryFile opts of
      Nothing -> return ()
      Just f -> let
        f' = if hasDrive f then f else dir </> f
        formatSummary = case summaryFormat opts of
                       JSON -> jsonVerificationSummary
                       Pretty -> prettyVerificationSummary ppOpts nenv
        in io $ writeFile f' $ formatSummary summary
