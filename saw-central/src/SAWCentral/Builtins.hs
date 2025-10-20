{- |
Module      : SAWCentral.Builtins
Description : Implementations of SAW-Script primitives.
License     : BSD3
Maintainer  : atomb
Stability   : provisional
-}
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

module SAWCentral.Builtins where

import Control.Lens (view)
import Control.Monad (foldM, unless)
import Control.Monad.Except (MonadError(..))
import Control.Monad.IO.Class (MonadIO(..))
import Control.Monad.Reader (asks)
import Control.Monad.State (MonadState(..), gets, modify)
import qualified Control.Exception as Ex
import qualified Data.ByteString as StrictBS
import qualified Data.ByteString.Lazy as BS
import qualified Data.IntMap as IntMap
import Data.List (isPrefixOf, isInfixOf, sort)
import qualified Data.Map as Map
import Data.Parameterized.Classes (KnownRepr(..))
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.Lazy as LText
import qualified Data.Text.Lazy.IO as TLIO
import Data.Time.Clock
import Data.Typeable

import System.Directory
import qualified System.Environment as Env
import qualified System.Exit as Exit
import qualified Data.Text.IO as TextIO
import System.IO
import System.IO.Temp (withSystemTempFile, emptySystemTempFile)
import System.FilePath (hasDrive, (</>))
import System.Process (callCommand, readProcessWithExitCode)
import Text.Printf (printf)
import Text.Read (readMaybe)

import qualified Cryptol.Utils.PP as CryptolPP
import qualified Cryptol.TypeCheck.AST as Cryptol
import qualified CryptolSAWCore.Cryptol as Cryptol
import qualified CryptolSAWCore.Simpset as Cryptol

-- saw-support
import qualified SAWSupport.Pretty as PPS (MemoStyle(..), Opts(..), pShowText)

-- saw-core
import qualified SAWCore.Parser.AST as Un
import SAWCore.Parser.Grammar (parseSAW, parseSAWTerm)
import SAWCore.ExternalFormat
import SAWCore.FiniteValue
  ( FiniteType(..), readFiniteValue
  , FirstOrderValue(..)
  , scFirstOrderValue
  )
import SAWCore.Name (ModuleName, VarName(..), ecShortName, mkModuleName)
import SAWCore.SATQuery
import SAWCore.SCTypeCheck
import SAWCore.Recognizer
import SAWCore.Prelude (scEq)
import SAWCore.SharedTerm
import SAWCore.Typechecker (tcInsertModule, inferCompleteTermCtx)
import SAWCore.Term.Functor
import SAWCore.Term.Pretty (ppTerm, scPrettyTerm)
import SAWCore.Term.Raw
import CryptolSAWCore.TypedTerm

import qualified SAWCore.Simulator.Concrete as Concrete
import SAWCore.Prim (rethrowEvalError)
import SAWCore.Rewriter
import SAWCore.Testing.Random (prepareSATQuery, runManyTests)

-- cryptol-saw-core
import qualified CryptolSAWCore.CryptolEnv as CEnv

-- saw-core-sbv
import qualified SAWCoreSBV.SBV as SBVSim

-- saw-core-what4
import qualified SAWCoreWhat4.What4 as W4Sim

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
import qualified Cryptol.Utils.Ident as C (packModName,
                                           textToModName, PrimIdent(..))

-- crucible
import Lang.Crucible.CFG.Common (freshGlobalVar)

import SAWCentral.ImportAIG

import SAWCentral.Options as Opts
import SAWCentral.Panic (panic)
import SAWCentral.Proof
import SAWCentral.Crucible.Common (PathSatSolver(..))
import qualified SAWCentral.Crucible.Common as Common
import SAWCentral.TopLevel
import qualified SAWCentral.Value as SV
import SAWCentral.Value (ProofScript, printOutLnTop, AIGNetwork)
import SAWCentral.SolverCache
import SAWCentral.SolverVersions

import qualified SAWCentral.Crucible.Common.MethodSpec as MS
import SAWCentral.Crucible.Common.Setup.Type (addCondition, croTags)
import SAWCentral.Prover.Util(checkBooleanSchema)
import SAWCentral.Prover.SolverStats
import qualified SAWCentral.Prover.SBV as Prover
import qualified SAWCentral.Prover.RME as Prover
import qualified SAWCentral.Prover.ABC as Prover
import qualified SAWCentral.Prover.What4 as Prover
import qualified SAWCentral.Prover.Exporter as Prover
import SAWCentral.VerificationSummary

showPrim :: SV.Value -> TopLevel Text
showPrim v = do
  opts <- fmap rwPPOpts getTopLevelRW
  nenv <- io . scGetNamingEnv =<< getSharedContext
  return $ Text.pack $ SV.showsPrecValue opts nenv 0 v ""

definePrim :: Text -> TypedTerm -> TopLevel TypedTerm
definePrim name (TypedTerm (TypedTermSchema schema) rhs) =
  do sc <- getSharedContext
     ty <- io $ Cryptol.importSchema sc Cryptol.emptyEnv schema
     t <- io $ scFreshConstant sc name rhs ty
     return $ TypedTerm (TypedTermSchema schema) t
definePrim _name (TypedTerm tp _) =
  fail $ unlines
    [ "Expected term with Cryptol schema type, but got"
    , show (ppTypedTermType tp)
    ]

readBytes :: Text -> TopLevel TypedTerm
readBytes pathtxt = do
  let path :: FilePath = Text.unpack pathtxt
  sc <- getSharedContext
  content <- io $ BS.readFile path
  let len = BS.length content
  let bytes = BS.unpack content
  e <- io $ scBitvector sc 8
  xs <- io $ mapM (scBvConst sc 8 . toInteger) bytes
  trm <- io $ scVector sc e xs
  let schema = C.Forall [] [] (C.tSeq (C.tNum len) (C.tSeq (C.tNum (8::Int)) C.tBit))
  return (TypedTerm (TypedTermSchema schema) trm)



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

loadAIGPrim :: Text -> TopLevel AIGNetwork
loadAIGPrim ftxt = do
  let f = Text.unpack ftxt
  SV.AIGProxy proxy <- SV.getProxy
  exists <- io $ doesFileExist f
  unless exists $ fail $ "AIG file " ++ f ++ " not found."
  et <- io $ loadAIG proxy f
  case et of
    Left err -> fail $ "Reading AIG failed: " ++ err
    Right ntk -> return (SV.AIGNetwork ntk)

saveAIGPrim :: Text -> AIGNetwork -> TopLevel ()
saveAIGPrim f (SV.AIGNetwork n) = io $ AIG.writeAiger (Text.unpack f) n

saveAIGasCNFPrim :: Text -> AIGNetwork -> TopLevel ()
saveAIGasCNFPrim f (SV.AIGNetwork (AIG.Network be ls)) =
  case ls of
    [l] -> do _ <- io $ AIG.writeCNF be l (Text.unpack f)
              return ()
    _ -> fail "save_aig_as_cnf: non-boolean term"

-- | Read an AIG file representing a theorem or an arbitrary function
-- and represent its contents as a @Term@ lambda term. This is
-- inefficient but semantically correct.
readAIGPrim :: Text -> TopLevel TypedTerm
readAIGPrim ftxt = do
  let f :: FilePath = Text.unpack ftxt
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

  unless (closedTerm tpat) $ fail $ unlines
    [ "pattern term is not closed", show tpat ]

  unless (closedTerm trepl) $ fail $ unlines
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


readCore :: Text -> TopLevel TypedTerm
readCore pathtxt = do
  let path :: FilePath = Text.unpack pathtxt
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

getTopLevelPPOpts :: TopLevel PPS.Opts
getTopLevelPPOpts =
  rwPPOpts <$> getTopLevelRW

show_term :: Term -> TopLevel Text
show_term t =
  do opts <- getTopLevelPPOpts
     sc <- getSharedContext
     str <- liftIO $ scShowTerm sc opts t
     return $ Text.pack str

print_term :: Term -> TopLevel ()
print_term t = do
  txt <- show_term t
  printOutLnTop Info $ Text.unpack txt

print_term_depth :: Int -> Term -> TopLevel ()
print_term_depth d t =
  do opts <- getTopLevelPPOpts
     sc <- getSharedContext
     let opts' = opts { PPS.ppMaxDepth = Just d }
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

write_goal :: FilePath -> ProofScript ()
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

-- | Print the current goal that a proof script is attempting to prove, without
-- generating @let@ bindings for the provided indices. For example,
-- @print_goal_inline [1,9,3]@ will print the goal without inlining the
-- variables that would otherwise be abstracted as @x\@1@, @x\@9@, and @x\@3@.
print_goal_inline :: [Int] -> ProofScript ()
print_goal_inline noInline =
  execTactic $ tacticId $ \goal ->
    do
      opts <- getTopLevelPPOpts
      opts' <-
        case PPS.ppMemoStyle opts of
          PPS.Incremental -> pure opts { PPS.ppNoInlineMemoFresh = sort noInline }
          PPS.HashIncremental _ -> pure opts { PPS.ppNoInlineMemoFresh = sort noInline }
          PPS.Hash _ -> warnIncremental >> pure opts
      sc <- getSharedContext
      nenv <- io (scGetNamingEnv sc)
      let output = prettySequent opts' nenv (goalSequent goal)
      printOutLnTop Info (unlines [goalSummary goal, output])
  where
    warnIncremental =
      printOutLnTop Warn $
        unlines
          [ "`print_goal_inline` is incompatible with non-incremental"
          , "memoization strategies. Printing goal without inlining..."
          ]

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
     let opts' = opts { PPS.ppMaxDepth = Just n }
     nenv <- io (scGetNamingEnv sc)
     let output = prettySequent opts' nenv (goalSequent goal)
     printOutLnTop Info (unlines [goalSummary goal, output])

printGoalConsts :: ProofScript ()
printGoalConsts =
  execTactic $ tacticId $ \goal ->
  do let cs = sequentConstantSet (goalSequent goal)
     mapM_ (printOutLnTop Info) $
       [ show nm | (_, nm) <- Map.toList cs ]

printGoalSize :: ProofScript ()
printGoalSize =
  execTactic $ tacticId $ \goal ->
  do printOutLnTop Info $ "Goal shared size: " ++ show (sequentSharedSize (goalSequent goal))
     printOutLnTop Info $ "Goal unshared size: " ++ show (sequentTreeSize (goalSequent goal))

resolveNames :: [Text] -> TopLevel (Set VarIndex)
resolveNames nms =
  do sc <- getSharedContext
     Set.fromList . mconcat <$> mapM (resolveName sc) nms

-- | Given a user-provided name, resolve it to (potentially several)
-- 'VarIndex'es that each represent an unfoldable 'Constant' value or a
-- fresh uninterpreted constant.
-- The given name is searched for in both the local Cryptol environment
-- and the SAWCore naming environment.
-- Pulling this out of `TopLevel` is useful so we can use it in other
-- contexts (e.g., `crucible-mir-comp`)
resolveNameIO :: SharedContext -> CEnv.CryptolEnv -> Text -> IO [VarIndex]
resolveNameIO sc cenv nm =
  do scnms <- scResolveName sc nm
     let ?fileReader = StrictBS.readFile
     res <- CEnv.resolveIdentifier cenv nm
     case res of
       Just cnm ->
         do importedName <- Cryptol.importName cnm
            case importedName of
              ImportedName uri _ ->
                do resolvedName <- scResolveNameByURI sc uri
                   case resolvedName of
                     Just vi -> pure (vi : scnms)
                     Nothing -> pure scnms
              _ -> pure scnms
       Nothing -> pure scnms

-- | Given a user-provided name, resolve it to (potentially several)
-- 'VarIndex'es that each represent an unfoldable 'Constant' value or a
-- fresh uninterpreted constant.
-- The given name is searched for in both the local Cryptol environment
-- and the SAWCore naming environment. If it is found in neither, an
-- exception is thrown.
resolveName :: SharedContext -> Text -> TopLevel [VarIndex]
resolveName sc nm =
  do cenv <- rwCryptol <$> getTopLevelRW
     scnms <- io (resolveNameIO sc cenv nm)
     case scnms of
       [] -> fail $ Text.unpack $ "Could not resolve name: " <> nm
       _  -> pure scnms

normalize_term :: TypedTerm -> TopLevel TypedTerm
normalize_term tt = normalize_term_opaque [] tt

normalize_term_opaque :: [Text] -> TypedTerm -> TopLevel TypedTerm
normalize_term_opaque opaque tt =
  do sc <- getSharedContext
     idxs <- mconcat <$> mapM (resolveName sc) opaque
     let opaqueSet = Set.fromList idxs
     tm' <- io (scTypeCheckWHNF sc =<< scUnfoldConstantSet sc False opaqueSet (ttTerm tt))
     pure tt{ ttTerm = tm' }

goal_normalize :: [Text] -> ProofScript ()
goal_normalize opaque =
  execTactic $ tacticChange $ \goal ->
    do sc <- getSharedContext
       idxs <- mconcat <$> mapM (resolveName sc) opaque
       let opaqueSet = Set.fromList idxs
       sqt' <- io $ traverseSequentWithFocus (normalizeProp sc opaqueSet) (goalSequent goal)
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

unfoldGoal :: [Text] -> ProofScript ()
unfoldGoal unints =
  execTactic $ tacticChange $ \goal ->
  do sc <- getSharedContext
     unints' <- resolveNames unints
     sqt' <- traverseSequentWithFocus (io . unfoldProp sc unints') (goalSequent goal)
     return (sqt', UnfoldEvidence unints')

unfoldFixOnceGoal :: [Text] -> ProofScript ()
unfoldFixOnceGoal unints =
  execTactic $ tacticChange $ \goal ->
  do sc <- getSharedContext
     unints' <- resolveNames unints
     sqt' <- traverseSequentWithFocus (io . unfoldFixOnceProp sc unints') (goalSequent goal)
     return (sqt', UnfoldFixOnceEvidence unints')

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
     ss' <- io (localHypSimpset sc (goalSequent goal) hs ss)
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

goal_eval :: [Text] -> ProofScript ()
goal_eval unints =
  execTactic $ tacticChange $ \goal ->
  do sc <- getSharedContext
     unintSet <- resolveNames unints
     what4PushMuxOps <- gets rwWhat4PushMuxOps
     sqt' <- traverseSequentWithFocus (io . evalProp sc what4PushMuxOps unintSet) (goalSequent goal)
     return (sqt', EvalEvidence unintSet)

congruence_for :: TypedTerm -> TopLevel TypedTerm
congruence_for tt =
  do sc <- getSharedContext
     congTm <- io $ build_congruence sc (ttTerm tt)
     io $ mkTypedTerm sc congTm

-- | Given an input term, construct another term that
--   represents a congruence law for that term.
--   This term will be a Curry-Howard style theorem statement
--   that can be dispatched to solvers, and should have
--   type \"Prop\".
--
--   This will only work for terms that represent non-dependent
--   functions.
build_congruence :: SharedContext -> Term -> IO Term
build_congruence sc tm =
  do ty <- scTypeOf sc tm
     case asPiList ty of
       ([],_) -> fail "congruence_for: Term is not a function"
       (pis, body) ->
         if closedTerm body then
           loop pis []
         else
           fail "congruence_for: cannot build congruence for dependent functions"
 where
  loop ((nm,tp):pis) vars =
    if closedTerm tp then
      do l <- scFreshEC sc (vnName nm <> "_1") tp
         r <- scFreshEC sc (vnName nm <> "_2") tp
         loop pis ((l,r):vars)
     else
       fail "congruence_for: cannot build congruence for dependent functions"

  loop [] vars =
    do lvars <- mapM (scVariable sc . fst) (reverse vars)
       rvars <- mapM (scVariable sc . snd) (reverse vars)
       let allVars = concat [ [l,r] | (l,r) <- reverse vars ]

       basel <- scApplyAll sc tm lvars
       baser <- scApplyAll sc tm rvars
       baseeq <- scEqTrue sc =<< scEq sc basel baser

       let f x (l,r) =
             do l' <- scVariable sc l
                r' <- scVariable sc r
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

goal_when :: Text -> ProofScript () -> ProofScript ()
goal_when str script =
  do s <- get
     case psGoals s of
       g : _ | (Text.unpack str) `isInfixOf` goalName g -> script
       _ -> return ()

goal_has_tags :: [Text] -> ProofScript Bool
goal_has_tags tags =
  do s <- get
     case psGoals s of
       g : _ | Set.isSubsetOf (Set.fromList (map Text.unpack tags)) (goalTags g) -> return True
       _ -> return False

goal_has_some_tag :: [Text] -> ProofScript Bool
goal_has_some_tag tags =
  do s <- get
     case psGoals s of
       g : _ | not $ Set.disjoint (Set.fromList (map Text.unpack tags)) (goalTags g) -> return True
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
  wrapProver [AIG] [] (Prover.proveABC proxy) Set.empty

satExternal :: Bool -> Text -> [Text] -> ProofScript ()
satExternal doCNF execName args =
  execTactic $ tacticSolve $ \g ->
    do SV.AIGProxy proxy <- SV.getProxy
       sc <- SV.getSharedContext
       let execName' = Text.unpack execName
           args' = map Text.unpack args
       (mb, stats) <- Prover.abcSatExternal proxy sc doCNF execName' args' g
       case mb of
         Nothing -> return (stats, SolveSuccess (SolverEvidence stats (goalSequent g)))
         Just a  -> return (stats, SolveCounterexample a)

writeAIGPrim :: Text -> Term -> TopLevel ()
writeAIGPrim ftxt e = do
  let f :: FilePath = Text.unpack ftxt
  Prover.writeAIG f e

writeSAIGPrim :: Text -> TypedTerm -> TopLevel ()
writeSAIGPrim filetxt tt = do
  let file :: FilePath = Text.unpack filetxt
  write_tt <- Prover.writeSAIGInferLatches tt
  io $ write_tt file

writeSAIGComputedPrim :: Text -> Term -> Int -> TopLevel ()
writeSAIGComputedPrim ftxt e n = do
  let f :: FilePath = Text.unpack ftxt
  Prover.writeSAIG f e n

-- | Bit-blast a proposition check its validity using the RME library.
proveRME :: ProofScript ()
proveRME = wrapProver [RME] [] Prover.proveRME Set.empty

codegenSBV :: SharedContext -> Text -> [Text] -> Text -> TypedTerm -> TopLevel ()
codegenSBV sc pathtxt unints fnametxt (TypedTerm _schema t) = do
     let path :: FilePath = Text.unpack pathtxt
         fname :: FilePath = Text.unpack fnametxt
     unintSet <- resolveNames unints
     let mpath = if null path then Nothing else Just path
     io $ SBVSim.sbvCodeGen sc mempty unintSet mpath fname t

-- | Bit-blast a proposition and check its validity using SBV.
-- (Currently ignores satisfying assignments.)
proveSBV :: SBV.SMTConfig -> ProofScript ()
proveSBV conf = proveUnintSBV conf []

-- | Bit-blast a proposition and check its validity using SBV.
-- (Currently ignores satisfying assignments.) Constants with names in
-- @unints@ are kept as uninterpreted functions.
proveUnintSBV :: SBV.SMTConfig -> [Text] -> ProofScript ()
proveUnintSBV conf unints =
  do timeout <- psTimeout <$> get
     unintSet <- SV.scriptTopLevel (resolveNames unints)
     wrapProver (sbvBackends conf) []
                (Prover.proveUnintSBV conf timeout) unintSet

-- | Given a continuation which calls a prover, call the continuation on the
-- given 'Sequent' and return a 'SolveResult'. If there is a 'SolverCache',
-- do not call the continuation if the goal has an already cached result,
-- and otherwise save the result of the call to the cache.
applyProverToGoal :: [SolverBackend] -> [SolverBackendOption]
                     -> (SATQuery -> TopLevel (Maybe CEX, Text))
                     -> Set VarIndex -> Sequent
                     -> TopLevel (SolverStats, SolveResult)
applyProverToGoal backends opts f unintSet sqt = do
  sc <- getSharedContext
  let opt_backends = concatMap optionBackends opts
  vs   <- io $ getSolverBackendVersions (backends ++ opt_backends)
  satq <- io $ sequentToSATQuery sc unintSet sqt
  k    <- io $ mkSolverCacheKey sc vs opts satq
  (mb, solver_name) <- SV.onSolverCache (lookupInSolverCache k) >>= \case
    -- Use a cached result if one exists (and it's valid w.r.t our query)
    Just v -> return $ fromSolverCacheValue satq v
    -- Otherwise try to cache the result of the call
    _ -> f satq >>= \res -> io (toSolverCacheValue vs opts satq res) >>= \case
           Just v  -> SV.onSolverCache (insertInSolverCache k v) >>
                      return res
           Nothing -> return res
  let stats = solverStats solver_name (sequentSharedSize sqt)
  case mb of
    Nothing -> return (stats, SolveSuccess (SolverEvidence stats sqt))
    Just a  -> return (stats, SolveCounterexample a)

wrapProver ::
  [SolverBackend] -> [SolverBackendOption] ->
  (SATQuery -> TopLevel (Maybe CEX, Text)) ->
  Set VarIndex ->
  ProofScript ()
wrapProver backends opts f unints =
  execTactic $ tacticSolve $ applyProverToGoal backends opts f unints . goalSequent

wrapW4Prover ::
  SolverBackend -> [SolverBackendOption] ->
  ( Bool -> SATQuery -> TopLevel (Maybe CEX, Text) ) ->
  [Text] ->
  ProofScript ()
wrapW4Prover backend opts f unints = do
  hashConsing <- SV.scriptTopLevel $ gets SV.rwWhat4HashConsing
  unintSet <- SV.scriptTopLevel $ resolveNames unints
  wrapProver [What4, backend] opts (f hashConsing) unintSet

wrapW4ProveExporter ::
  ( Bool -> FilePath -> SATQuery -> TopLevel (Maybe CEX, Text) ) ->
  [Text] ->
  FilePath ->
  FilePath ->
  ProofScript ()
wrapW4ProveExporter f unints path ext = do
  hashConsing <- SV.scriptTopLevel $ gets SV.rwWhat4HashConsing
  unintSet <- SV.scriptTopLevel $ resolveNames unints
  execTactic $ tacticSolve $ \g -> do
    let file = path ++ "." ++ goalType g ++ show (goalNum g) ++ ext
    sc <- getSharedContext
    satq <- io $ sequentToSATQuery sc unintSet (goalSequent g)
    (_, solver_name) <- f hashConsing file satq
    let stats = solverStats solver_name (sequentSharedSize (goalSequent g))
    return (stats, SolveSuccess (SolverEvidence stats (goalSequent g)))

--------------------------------------------------
proveABC_SBV :: ProofScript ()
proveABC_SBV = proveSBV SBV.abc

proveBitwuzla :: ProofScript ()
proveBitwuzla = proveSBV SBV.bitwuzla

proveBoolector :: ProofScript ()
proveBoolector = proveSBV SBV.boolector

proveZ3 :: ProofScript ()
proveZ3 = proveSBV SBV.z3

proveCVC4 :: ProofScript ()
proveCVC4 = proveSBV SBV.cvc4

proveCVC5 :: ProofScript ()
proveCVC5 = proveSBV SBV.cvc5

proveMathSAT :: ProofScript ()
proveMathSAT = proveSBV SBV.mathSAT

proveYices :: ProofScript ()
proveYices = proveSBV SBV.yices

proveUnintBitwuzla :: [Text] -> ProofScript ()
proveUnintBitwuzla = proveUnintSBV SBV.bitwuzla

proveUnintBoolector :: [Text] -> ProofScript ()
proveUnintBoolector = proveUnintSBV SBV.boolector

proveUnintZ3 :: [Text] -> ProofScript ()
proveUnintZ3 = proveUnintSBV SBV.z3

proveUnintCVC4 :: [Text] -> ProofScript ()
proveUnintCVC4 = proveUnintSBV SBV.cvc4

proveUnintCVC5 :: [Text] -> ProofScript ()
proveUnintCVC5 = proveUnintSBV SBV.cvc5

proveUnintMathSAT :: [Text] -> ProofScript ()
proveUnintMathSAT = proveUnintSBV SBV.mathSAT

proveUnintYices :: [Text] -> ProofScript ()
proveUnintYices = proveUnintSBV SBV.yices


--------------------------------------------------
w4_abc_smtlib2 :: ProofScript ()
w4_abc_smtlib2 = wrapW4Prover ABC [W4_SMTLib2] Prover.proveWhat4_abc []

w4_bitwuzla :: ProofScript ()
w4_bitwuzla = wrapW4Prover Bitwuzla [] Prover.proveWhat4_bitwuzla []

w4_boolector :: ProofScript ()
w4_boolector = wrapW4Prover Boolector [] Prover.proveWhat4_boolector []

w4_z3 :: ProofScript ()
w4_z3 = wrapW4Prover Z3 [] Prover.proveWhat4_z3 []

w4_cvc4 :: ProofScript ()
w4_cvc4 = wrapW4Prover CVC4 [] Prover.proveWhat4_cvc4 []

w4_cvc5 :: ProofScript ()
w4_cvc5 = wrapW4Prover CVC5 [] Prover.proveWhat4_cvc5 []

w4_yices :: ProofScript ()
w4_yices = wrapW4Prover Yices [] Prover.proveWhat4_yices []

w4_unint_bitwuzla :: [Text] -> ProofScript ()
w4_unint_bitwuzla = wrapW4Prover Bitwuzla [] Prover.proveWhat4_bitwuzla

w4_unint_rme :: [Text] -> ProofScript ()
w4_unint_rme = wrapW4Prover RME [] Prover.proveWhat4_rme

w4_unint_boolector :: [Text] -> ProofScript ()
w4_unint_boolector = wrapW4Prover Boolector [] Prover.proveWhat4_boolector

w4_unint_z3 :: [Text] -> ProofScript ()
w4_unint_z3 = wrapW4Prover Z3 [] Prover.proveWhat4_z3

w4_unint_z3_using :: Text -> [Text] -> ProofScript ()
w4_unint_z3_using tactic =
  let tactic' = Text.unpack tactic in
  wrapW4Prover Z3 [W4_Tactic tactic'] (Prover.proveWhat4_z3_using tactic')

w4_unint_cvc4 :: [Text] -> ProofScript ()
w4_unint_cvc4 = wrapW4Prover CVC4 [] Prover.proveWhat4_cvc4

w4_unint_cvc5 :: [Text] -> ProofScript ()
w4_unint_cvc5 = wrapW4Prover CVC5 [] Prover.proveWhat4_cvc5

w4_unint_yices :: [Text] -> ProofScript ()
w4_unint_yices = wrapW4Prover Yices [] Prover.proveWhat4_yices

offline_w4_unint_bitwuzla :: [Text] -> FilePath -> ProofScript ()
offline_w4_unint_bitwuzla unints path =
  wrapW4ProveExporter Prover.proveExportWhat4_bitwuzla unints path ".smt2"

offline_w4_unint_z3 :: [Text] -> FilePath -> ProofScript ()
offline_w4_unint_z3 unints path =
  wrapW4ProveExporter Prover.proveExportWhat4_z3 unints path ".smt2"

offline_w4_unint_cvc4 :: [Text] -> FilePath -> ProofScript ()
offline_w4_unint_cvc4 unints path =
  wrapW4ProveExporter Prover.proveExportWhat4_cvc4 unints path ".smt2"

offline_w4_unint_cvc5 :: [Text] -> FilePath -> ProofScript ()
offline_w4_unint_cvc5 unints path =
  wrapW4ProveExporter Prover.proveExportWhat4_cvc5 unints path ".smt2"

offline_w4_unint_yices :: [Text] -> FilePath -> ProofScript ()
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

offline_unint_smtlib2 :: [Text] -> FilePath -> ProofScript ()
offline_unint_smtlib2 unints path =
  do unintSet <- SV.scriptTopLevel $ resolveNames unints
     proveWithSATExporter Prover.writeSMTLib2 unintSet path "." ".smt2"

offline_verilog :: FilePath -> ProofScript ()
offline_verilog path =
  proveWithSATExporter Prover.writeVerilogSAT mempty path "." ".v"

w4_abc_aiger :: ProofScript ()
w4_abc_aiger = wrapW4Prover ABC [W4_AIGER] Prover.w4AbcAIGER []

w4_abc_verilog :: ProofScript ()
w4_abc_verilog = wrapW4Prover ABC [W4_Verilog] Prover.w4AbcVerilog []

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
    ValidProof _ thm -> SV.recordTheoremProof thm
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
  opts <- getTopLevelPPOpts
  res <- SV.runProofScript script prop goal Nothing (Text.pack nm) True False
  let failProof pst =
         fail $ "prove: " ++ show (length (psGoals pst)) ++ " unsolved subgoal(s)\n"
                          ++ SV.showsProofResult opts res ""
  case res of
    ValidProof _stats thm ->
      do printOutLnTop Debug $ "Valid: " ++ show (ppTerm opts t)
         SV.returnTheoremProof thm
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
     opts <- getTopLevelPPOpts
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
            toNat <- io $ scGlobalDef sc "Prelude.bvToNat"
            vars  <- io $ mapM (scVariable sc) pis
            innerVars <-
              io $ sequence $
              [ scFreshVariable sc ("i_" <> ecShortName ec) (ecType ec) | ec <- pis ]
            t1    <- io $ scApplyAllBeta sc (ttTerm t) vars
            tsz   <- io $ scTupleSelector sc t1 1 2 -- left element
            tbody <- io $ scEqTrue sc =<< scTupleSelector sc t1 2 2 -- rightmost tuple element
            inner_t1 <- io $ scApplyAllBeta sc (ttTerm t) innerVars
            innersz  <- io $ scTupleSelector sc inner_t1 1 2 -- left element

            -- The result type of the theorem.
            --
            --   (x : Vec w Bool) -> p x
            thmResult <- io $
                do t3   <- scGeneralizeExts sc pis tbody
                   _    <- scTypeCheckError sc t3 -- sanity check
                   return t3

            -- The type of the main hypothesis to the induction scheme. This is what
            -- the user will ultimately be asked to prove. Note that this includes
            -- the induction hypothesis.
            --
            --   ((x : Vec w Bool) -> ((y: Vec w Bool) -> is_bvult w y x -> p y) -> p x)
            thmHyp <- io $
                do bvult <- scGlobalDef sc "Prelude.bvult"
                   islt  <- scEqTrue sc =<< scApplyAll sc bvult [wt, innersz, tsz]

                   tinner <- scFun sc islt tbody
                   thyp   <- scGeneralizeTerms sc innerVars tinner

                   touter <- scFun sc thyp tbody
                   scGeneralizeExts sc pis touter

            -- The "motive" we will pass to the 'Nat_complete_induction' principle.
            --
            --      (\ (n:Nat) -> (x:Vec w Bool) -> IsLeNat (bvToNat w x) n -> p x)
            indMotive <- io $
                do indVar <- scFreshVariable sc "inductionVar" natty
                   tsz'   <- scApplyAll sc toNat [wt, tsz]
                   teq    <- scGlobalApply sc "Prelude.IsLeNat" [tsz', indVar]
                   t2     <- scFun sc teq tbody
                   t3     <- scGeneralizeTerms sc vars t2
                   scAbstractTerms sc [indVar] t3

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
                do hVar    <- scFreshVariable sc "H" thmHyp
                   nVar    <- scFreshVariable sc "n" natty
                   hindVar <- scFreshVariable sc "Hind" =<<
                                do m <- scFreshVariable sc "m" natty
                                   lt <- scGlobalApply sc "Prelude.IsLtNat" [m, nVar]
                                   scGeneralizeTerms sc [m] =<< scFun sc lt =<< scApplyBeta sc indMotive m


                   let outersz = tsz
                   natoutersz <- scApplyAll sc toNat [wt, outersz]

                   natinnersz <- scApplyAll sc toNat [wt, innersz]

                   succinnersz <- scGlobalApply sc "Prelude.Succ" [natinnersz]

                   bvltVar <- scFreshVariable sc "Hult" =<< scEqTrue sc =<< scBvULt sc wt innersz outersz

                   leVar   <- scFreshVariable sc "Hle" =<<
                                 scGlobalApply sc "Prelude.IsLeNat" [natoutersz, nVar]

                   refl_inner <- scGlobalApply sc "Prelude.IsLeNat_base" [natinnersz]

                   prf     <- do hyx <- scGlobalApply sc "Prelude.bvultToIsLtNat" [wt,innersz,outersz,bvltVar]
                                 scGlobalApply sc "Prelude.IsLeNat_transitive" [succinnersz, natoutersz, nVar, hyx, leVar]
                   inner   <- do body <- scApplyAll sc hindVar ([natinnersz,prf]++innerVars++[refl_inner])
                                 scAbstractTerms sc (innerVars ++ [bvltVar]) body

                   body <- scApplyAll sc hVar (vars ++ [inner])

                   scAbstractTerms sc ([hVar, nVar, hindVar] ++ vars ++ [leVar]) body

            -- Now we put all the pieces together
            --
            -- \ (Hind : (x : Vec w Bool) -> ((y: Vec w Bool) -> is_bvult w y x -> p y) -> p x) ->
            -- \ (x : Vec x Bool) ->
            --    Nat_complete_induction indMotive (indHypProof Hind) (bvToNat w x) x (IsLeNat_base (bvToNat w x))
            indApp <- io $
                do varH   <- scFreshVariable sc "Hind" thmHyp
                   tsz'   <- scApplyAll sc toNat [wt, tsz]
                   trefl  <- scGlobalApply sc "Prelude.IsLeNat_base" [tsz']
                   indHypArg <- scApplyBeta sc indHypProof varH
                   ind    <- scGlobalApply sc "Prelude.Nat_complete_induction" ([indMotive,indHypArg,tsz'] ++ vars ++ [trefl])
                   ind''  <- scAbstractTerms sc (varH : vars) ind

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
         Just (nm, tp, body) -> checkInductionScheme sc opts (EC nm tp : pis) body
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
                   , show (ppTerm opts ty)
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
  opts <- getTopLevelPPOpts
  printOutLnTop Info (SV.showsSatResult opts result "")

-- | Quick check (random test) a term and print the result. The
-- 'Integer' parameter is the number of random tests to run.
quickCheckPrintPrim :: SharedContext -> Options -> Integer -> TypedTerm -> IO ()
quickCheckPrintPrim sc opts numTests tt =
  do prop <- predicateToProp sc Universal (ttTerm tt)
     satq <- propToSATQuery sc mempty prop
     testGen <- prepareSATQuery sc satq
     runManyTests testGen numTests >>= \case
        Nothing -> printOutLn opts Info $ "All " ++ show numTests ++ " tests passed!"
        Just cex ->
          do let cex' = [ (Text.unpack (vnName x), v) | (x, v) <- cex ]
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

unfold_term :: [Text] -> TypedTerm -> TopLevel TypedTerm
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

term_eval :: [Text] -> TypedTerm -> TopLevel TypedTerm
term_eval unints (TypedTerm schema t0) =
  do sc <- getSharedContext
     unintSet <- resolveNames unints
     what4PushMuxOps <- gets rwWhat4PushMuxOps
     sym <- liftIO $ Common.newSAWCoreExprBuilder sc what4PushMuxOps
     st <- liftIO $ Common.sawCoreState sym
     t1 <- liftIO $ W4Sim.w4EvalTerm sym st sc Map.empty unintSet t0
     pure (TypedTerm schema t1)

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
  do  sc <- getSharedContext
      io (ruleOfProp sc t Nothing) >>= \case
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

check_term :: TypedTerm -> TopLevel ()
check_term tt = do
  sc <- getSharedContext
  opts <- getTopLevelPPOpts
  cenv <- rwCryptol <$> getTopLevelRW
  let t = ttTerm tt
  ty <- io $ scTypeCheckError sc t
  expectedTy <-
    case ttType tt of
      TypedTermSchema schema -> io $ importSchemaCEnv sc cenv schema
      TypedTermKind k -> io $ Cryptol.importKind sc k
      TypedTermOther ty' -> pure ty'
  convertible <- io $ scConvertible sc True ty expectedTy
  unless convertible $
    panic "check_term"
    [ "Term's actual type does not match its attached type:"
    , "Expected: " <> Text.pack (scPrettyTerm opts expectedTy)
    , "Actual: " <> Text.pack (scPrettyTerm opts ty)
    ]
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

freshSymbolicPrim :: Text -> C.Schema -> TopLevel TypedTerm
freshSymbolicPrim x schema@(C.Forall [] [] ct) = do
  sc <- getSharedContext
  cty <- io $ Cryptol.importType sc Cryptol.emptyEnv ct
  tm <- io $ scFreshVariable sc x cty
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
      argMap = IntMap.fromList (zip is args')

  -- TODO, instead of instantiating and then evaluating, we should
  -- evaluate in the context of an EC map instead.  argMap is almost
  -- what we need, but the values syould be @Concrete.CValue@ instead.

  tm' <- scInstantiateExt sc argMap tm
  modmap <- scGetModuleMap sc
  return $ Concrete.evalSharedTerm modmap mempty mempty tm'

envCmd :: TopLevel ()
envCmd = do
  rw <- SV.getMergedEnv
  let avail = rwPrimsAvail rw
      vals = rwValueInfo rw
      keep (_x, (_pos, lc, _rb, _ty, _v, _doc)) = Set.member lc avail
      vals' = filter keep $ Map.assocs vals
      printit (x, (_pos, _lc, _rb, ty, _v, _doc)) = x <> " : " <> PPS.pShowText ty
  opts <- getOptions
  io $ sequence_ [ printOutLn opts Info (Text.unpack $ printit item) | item <- vals' ]

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

failPrim :: Text -> TopLevel SV.Value
failPrim msg = fail $ Text.unpack msg

failsPrim :: TopLevel SV.Value -> TopLevel ()
failsPrim m = do
  topRO <- getTopLevelRO
  topRW <- getTopLevelRW
  x <- liftIO $ Ex.try (runTopLevel m topRO topRW)
  case x of
    Left (ex :: Ex.SomeException) ->
      do liftIO $ TextIO.putStrLn "== Anticipated failure message =="
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

term_theories :: [Text] -> TypedTerm -> TopLevel [Text]
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
      let nms = C.addTNames CryptolPP.defaultPPCfg vars IntMap.empty
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
        C.TNominal nt ts -> C.TNominal nt (fmap (plainSubst s) ts)

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
                        scGlobalApply sc "Cryptol.TCNum" =<< sequence [scNat sc (fromInteger x)]
                      Left C.Inf -> scGlobalApply sc "Cryptol.TCInf" []
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

parseCoreMod :: Text -> Text -> TopLevel Term
parseCoreMod mnm_str input =
  do sc <- getSharedContext
     let base = "<interactive>"
         path = "<interactive>"
     uterm <-
       case parseSAWTerm base path (LText.fromStrict input) of
         Right uterm -> return uterm
         Left err ->
           do let msg = show err
              printOutLnTop Opts.Error msg
              fail msg
     let mnm =
           mkModuleName $ Text.splitOn "." mnm_str
     _ <- io $ scFindModule sc mnm -- Check that mnm exists
     err_or_t <- io $ inferCompleteTermCtx sc (Just mnm) mempty uterm
     case err_or_t of
       Left err -> fail (show err)
       Right x -> pure x

parseCore :: Text -> TopLevel Term
parseCore input = parseCoreMod "Cryptol" input

parse_core :: Text -> TopLevel TypedTerm
parse_core input = do
  t <- parseCore input
  sc <- getSharedContext
  io $ mkTypedTerm sc t

parse_core_mod :: Text -> Text -> TopLevel TypedTerm
parse_core_mod mnm input = do
  t <- parseCoreMod mnm input
  sc <- getSharedContext
  io $ mkTypedTerm sc t

prove_core :: ProofScript () -> Text -> TopLevel Theorem
prove_core script input =
  do sc <- getSharedContext
     t <- parseCore input
     p <- io (termToProp sc t)
     pos <- SV.getPosition
     opts <- getTopLevelPPOpts
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
       ValidProof _ thm -> SV.returnTheoremProof thm
       InvalidProof _ _ pst -> failProof pst
       UnfinishedProof pst  -> failProof pst

core_axiom :: Text -> TopLevel Theorem
core_axiom input =
  do sc <- getSharedContext
     pos <- SV.getPosition
     t <- parseCore input
     p <- io (termToProp sc t)
     db <- SV.getTheoremDB
     (thm, db') <- io (admitTheorem db "core_axiom" p pos "core_axiom")
     SV.putTheoremDB db'
     SV.returnTheoremProof thm

core_thm :: Text -> TopLevel Theorem
core_thm input =
  do t <- parseCore input
     sc <- getSharedContext
     pos <- SV.getPosition
     db <- SV.getTheoremDB
     (thm, db') <- io (proofByTerm sc db t pos "core_thm")
     SV.putTheoremDB db'
     SV.returnTheoremProof thm

specialize_theorem :: Theorem -> [TypedTerm] -> TopLevel Theorem
specialize_theorem thm ts =
  do sc <- getSharedContext
     db <- SV.getTheoremDB
     pos <- SV.getPosition
     what4PushMuxOps <- gets rwWhat4PushMuxOps
     (thm', db') <- io (specializeTheorem sc what4PushMuxOps db pos "specialize_theorem" thm (map ttTerm ts))
     SV.putTheoremDB db'
     SV.returnTheoremProof thm'

get_opt :: Int -> TopLevel Text
get_opt n = do
  argv <- asks roArgv
  nthPrim argv n

get_nopts :: () -> TopLevel Int
get_nopts () = do
  argv <- asks roArgv
  return $ length argv

get_env :: Text -> TopLevel Text
get_env name = do
  mbValue <- io $ Env.lookupEnv (Text.unpack name)
  case mbValue of
    Nothing -> fail $ "Environment variable not found: " ++ Text.unpack name
    Just v -> return $ Text.pack v

cryptol_prims :: TopLevel CEnv.ExtCryptolModule
cryptol_prims =
    CEnv.ECM_CryptolModule
    <$> CryptolModule Map.empty
    <$> Map.fromList <$> traverse parsePrim prims
  where
    prims :: [(Text, Ident, Text)]
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

    noLoc :: Text -> CEnv.InputText
    noLoc x = CEnv.InputText
                { CEnv.inpText = x
                , CEnv.inpFile = "(cryptol_prims)"
                , CEnv.inpLine = 1
                , CEnv.inpCol  = 1 + 2 -- add 2 for dropped {{
                }

    parsePrim :: (Text, Ident, Text) -> TopLevel (C.Name, TypedTerm)
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

cryptol_load :: (FilePath -> IO StrictBS.ByteString) -> FilePath -> TopLevel CEnv.ExtCryptolModule
cryptol_load fileReader path = do
  sc <- getSharedContext
  rw <- getTopLevelRW
  let ce = rwCryptol rw
  let ?fileReader = fileReader
  (m, ce') <- io $ CEnv.loadExtCryptolModule sc ce path
  putTopLevelRW $ rw { rwCryptol = ce' }
  return m

cryptol_extract :: CEnv.ExtCryptolModule -> Text -> TopLevel TypedTerm
cryptol_extract ecm var = do
  sc <- getSharedContext
  rw <- getTopLevelRW
  let ce = rwCryptol rw
  let ?fileReader = StrictBS.readFile
  io $ CEnv.extractDefFromExtCryptolModule sc ce ecm var

cryptol_add_path :: FilePath -> TopLevel ()
cryptol_add_path path =
  do rw <- getTopLevelRW
     let ce = rwCryptol rw
     let me = CEnv.eModuleEnv ce
     let me' = me { C.meSearchPath = path : C.meSearchPath me }
     let ce' = ce { CEnv.eModuleEnv = me' }
     let rw' = rw { rwCryptol = ce' }
     putTopLevelRW rw'

cryptol_add_prim :: Text -> Text -> TypedTerm -> TopLevel ()
cryptol_add_prim mnm nm trm =
  do rw <- getTopLevelRW
     let env = rwCryptol rw
     let prim_name =
           C.PrimIdent (C.textToModName mnm) nm
     let env' =
           env { CEnv.ePrims =
                   Map.insert prim_name (ttTerm trm) (CEnv.ePrims env) }
     putTopLevelRW (rw { rwCryptol = env' })

cryptol_add_prim_type :: Text -> Text -> TypedTerm -> TopLevel ()
cryptol_add_prim_type mnm nm tp =
  do rw <- getTopLevelRW
     let env = rwCryptol rw
     let prim_name =
           C.PrimIdent (C.textToModName mnm) nm
     let env' = env { CEnv.ePrimTypes =
                        Map.insert prim_name (ttTerm tp) (CEnv.ePrimTypes env) }
     putTopLevelRW (rw { rwCryptol = env' })

-- | Call 'Cryptol.importSchema' using a 'CEnv.CryptolEnv'
importSchemaCEnv :: SharedContext -> CEnv.CryptolEnv -> Cryptol.Schema ->
                    IO Term
importSchemaCEnv sc cenv schema =
  do cry_env <- let ?fileReader = StrictBS.readFile in CEnv.mkCryEnv cenv
     Cryptol.importSchema sc cry_env schema

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

set_path_sat_solver :: Text -> TopLevel ()
set_path_sat_solver nm =
  case Text.toLower nm of
    "z3"    -> modify (\rw -> rw{ rwPathSatSolver = PathSat_Z3 })
    "yices" -> modify (\rw -> rw{ rwPathSatSolver = PathSat_Yices })
    _ -> fail $ Text.unpack $ "Unknown path sat solver: " <> nm

summarize_verification :: TopLevel ()
summarize_verification =
  do values <- rwProofs <$> getTopLevelRW
     let jspecs  = [ s | SV.VJVMMethodSpec s <- values ]
         lspecs  = [ s | SV.VLLVMCrucibleMethodSpec s <- values ]
         thms    = [ t | SV.VTheorem t <- values ]
     db <- SV.getTheoremDB
     let summary = computeVerificationSummary db jspecs lspecs thms
     opts <- getTopLevelPPOpts
     nenv <- io . scGetNamingEnv =<< getSharedContext
     io $ putStrLn $ prettyVerificationSummary opts nenv summary

summarize_verification_json :: FilePath -> TopLevel ()
summarize_verification_json fpath =
  do values <- rwProofs <$> getTopLevelRW
     let jspecs  = [ s | SV.VJVMMethodSpec s <- values ]
         lspecs  = [ s | SV.VLLVMCrucibleMethodSpec s <- values ]
         thms    = [ t | SV.VTheorem t <- values ]
     db <- SV.getTheoremDB
     let summary = computeVerificationSummary db jspecs lspecs thms
     io (writeFile fpath (jsonVerificationSummary summary))

writeVerificationSummary :: TopLevel ()
writeVerificationSummary = do
  do
    db <- SV.getTheoremDB
    values <- rwProofs <$> getTopLevelRW
    let jspecs  = [ s | SV.VJVMMethodSpec s <- values ]
        lspecs  = [ s | SV.VLLVMCrucibleMethodSpec s <- values ]
        thms    = [ t | SV.VTheorem t <- values ]
        summary = computeVerificationSummary db jspecs lspecs thms
    opts <- asks roOptions
    dir <- asks roInitWorkDir
    nenv <- io . scGetNamingEnv =<< getSharedContext
    ppOpts <- getTopLevelPPOpts

    case summaryFile opts of
      Nothing -> return ()
      Just f -> let
        f' = if hasDrive f then f else dir </> f
        formatSummary = case summaryFormat opts of
                       JSON -> jsonVerificationSummary
                       Pretty -> prettyVerificationSummary ppOpts nenv
        in io $ writeFile f' $ formatSummary summary

declare_ghost_state ::
  Text ->
  TopLevel SV.Value
declare_ghost_state name =
  do allocator <- getHandleAlloc
     global <- liftIO (freshGlobalVar allocator name knownRepr)
     return (SV.VGhostVar global)

ghost_value ::
  MS.GhostGlobal ->
  TypedTerm ->
  SV.CrucibleSetup ext ()
ghost_value ghost val =
  do loc <- SV.getW4Position "ghost_value"
     tags <- view croTags
     let md = MS.ConditionMetadata
              { MS.conditionLoc = loc
              , MS.conditionTags = tags
              , MS.conditionType = "ghost value"
              , MS.conditionContext = ""
              }
     addCondition (MS.SetupCond_Ghost md ghost val)

-- | Based on the function of the same name in SAWCore.ParserUtils.
-- Unlike that function, this calls 'fail' instead of 'error'.
--
-- XXX: we only need one; unify these once the error handling gets fixed.
readModuleFromFile :: FilePath -> TopLevel (Un.Module, ModuleName)
readModuleFromFile path =
  do base <- liftIO getCurrentDirectory
     txt <- liftIO $ TLIO.readFile path
     case parseSAW base path txt of
       Right m@(Un.Module (Un.PosPair _ mnm) _ _) -> pure (m, mnm)
       Left err -> fail $ "Module parsing failed:\n" ++ show err

load_sawcore_from_file :: FilePath -> TopLevel ()
load_sawcore_from_file mod_filename =
  do sc <- getSharedContext
     (saw_mod, _) <- readModuleFromFile mod_filename
     liftIO $ tcInsertModule sc saw_mod
