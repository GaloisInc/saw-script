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
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE NondecreasingIndentation #-}

module SAWScript.Builtins where

import Data.Foldable (toList)
#if !MIN_VERSION_base(4,8,0)
import Data.Functor
import Control.Applicative
import Data.Monoid
#endif
import Control.Monad.State
import Control.Monad.Reader (ask)
import qualified Control.Exception as Ex
import qualified Data.ByteString.Lazy as BS
import qualified Data.ByteString.Lazy.UTF8 as B
import qualified Data.IntMap as IntMap
import Data.List (isPrefixOf)
import qualified Data.Map as Map
import Data.Maybe
import Data.Monoid ((<>))
import Data.Time.Clock
import System.Directory
import qualified System.Environment
import qualified System.Exit as Exit
import System.IO
import System.IO.Temp (withSystemTempFile)
import System.Process (callCommand, readProcessWithExitCode)
import Text.Printf (printf)
import Text.Read


import qualified Verifier.Java.Codebase as JSS
import qualified Verifier.SAW.Cryptol as Cryptol
import qualified Cryptol.TypeCheck.AST as Cryptol

import Verifier.SAW.Grammar (parseSAWTerm)
import Verifier.SAW.ExternalFormat
import Verifier.SAW.FiniteValue
  ( FiniteType(..), FiniteValue(..)
  , readFiniteValues, readFiniteValue
  , asFiniteTypePure, sizeFiniteType
  , FirstOrderValue(..)
  , toFirstOrderValue, scFirstOrderValue
  )
import qualified Verifier.SAW.Position as Position
import Verifier.SAW.Prelude
import Verifier.SAW.SCTypeCheck
import Verifier.SAW.SharedTerm
import qualified Verifier.SAW.Simulator.Concrete as Concrete
import Verifier.SAW.Prim (rethrowEvalError)
import Verifier.SAW.Recognizer
import Verifier.SAW.Rewriter
import Verifier.SAW.Testing.Random (scRunTestsTFIO, scTestableType)
import qualified Verifier.SAW.Typechecker (checkTerm)
import Verifier.SAW.TypedAST
import qualified Verifier.SAW.UntypedAST as UntypedAST

import qualified SAWScript.CryptolEnv as CEnv
import qualified SAWScript.SBVParser as SBV
import SAWScript.ImportAIG

import SAWScript.AST (getVal, pShow, Located(..))
import SAWScript.Options as Opts
import SAWScript.Proof
import SAWScript.TopLevel
import SAWScript.TypedTerm
import SAWScript.Utils
import SAWScript.SAWCorePrimitives( bitblastPrimitives, sbvPrimitives, concretePrimitives )
import qualified SAWScript.Value as SV
import SAWScript.Value (ProofScript, printOutLnTop)

import SAWScript.Prover.Util(checkBooleanSchema)
import SAWScript.Prover.Mode(ProverMode(..))
import SAWScript.Prover.SolverStats
import SAWScript.Prover.Rewrite(basic_ss)
import qualified SAWScript.Prover.SBV as Prover

import qualified Verifier.SAW.Cryptol.Prelude as CryptolSAW
import qualified Verifier.SAW.Simulator.BitBlast as BBSim
import qualified Verifier.SAW.Simulator.SBV as SBVSim

import qualified Verifier.SAW.Simulator.RME as RME
import qualified Verifier.SAW.Simulator.RME.Base as RME

import qualified Data.ABC as ABC
import qualified Data.SBV.Dynamic as SBV

import qualified Data.ABC.GIA as GIA
import qualified Data.AIG as AIG

import qualified Cryptol.ModuleSystem.Env as C (meSolverConfig)
import qualified Cryptol.TypeCheck as C (SolverConfig)
import qualified Cryptol.TypeCheck.AST as C
import qualified Cryptol.TypeCheck.PP as C (ppWithNames, pp, text, (<+>))
import qualified Cryptol.TypeCheck.Solve as C (defaultReplExpr)
import qualified Cryptol.TypeCheck.Solver.SMT as C (withSolver)
import qualified Cryptol.TypeCheck.Solver.InfNat as C (Nat'(..))
import qualified Cryptol.TypeCheck.Subst as C (apSubst, listSubst)
import qualified Cryptol.Eval.Monad as C (runEval)
import qualified Cryptol.Eval.Type as C (evalType)
import qualified Cryptol.Eval.Value as C (fromVBit, fromWord)
import qualified Cryptol.Utils.Ident as C (packIdent, packModName)
import Cryptol.Utils.PP (pretty)

data BuiltinContext = BuiltinContext { biSharedContext :: SharedContext
                                     , biJavaCodebase  :: JSS.Codebase
                                     , biBasicSS       :: Simpset
                                     }

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
         tcr <- io $ scTypeCheck sc trm
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
          SBV.TRecord bs -> C.tRec [ (C.packIdent n, toCType t) | (n, t) <- bs ]


-- | The 'AIG.Proxy' used by SAWScript.
sawProxy :: AIG.Proxy GIA.Lit GIA.GIA
sawProxy = GIA.proxy

-- | Use ABC's 'dsec' command to equivalence check to terms
-- representing SAIGs. Note that nothing is returned; you must read
-- the output to see what happened.
--
-- TODO: this is a first version. The interface can be improved later,
-- but I don't want too worry to much about generalization before I
-- have more examples. It might be an improvement to take SAIGs as
-- arguments, in the style of 'cecPrim' below. This would require
-- support for latches in the 'AIGNetwork' SAWScript type.
dsecPrint :: SharedContext -> TypedTerm -> TypedTerm -> IO ()
dsecPrint sc t1 t2 = do
  withSystemTempFile ".aig" $ \path1 _handle1 -> do
  withSystemTempFile ".aig" $ \path2 _handle2 -> do
  writeSAIGInferLatches sc path1 t1
  writeSAIGInferLatches sc path2 t2
  callCommand (abcDsec path1 path2)
  where
    -- The '-w' here may be overkill ...
    abcDsec path1 path2 = printf "abc -c 'read %s; dsec -v -w %s;'" path1 path2

cecPrim :: AIGNetwork -> AIGNetwork -> TopLevel SV.ProofResult
cecPrim x y = do
  io $ verifyAIGCompatible x y
  res <- io $ ABC.cec x y
  let stats = solverStats "ABC" 0 -- TODO, count the size of the networks...
  case res of
    ABC.Valid -> return $ SV.Valid stats
    ABC.Invalid bs
      | Just fv <- readFiniteValue (FTVec (fromIntegral (length bs)) FTBit) bs ->
           return $ SV.InvalidMulti stats [("x", toFirstOrderValue fv)]
      | otherwise -> fail "cec: impossible, could not parse counterexample"
    ABC.VerifyUnknown -> fail "cec: unknown result "

loadAIGPrim :: FilePath -> TopLevel AIGNetwork
loadAIGPrim f = do
  exists <- io $ doesFileExist f
  unless exists $ fail $ "AIG file " ++ f ++ " not found."
  et <- io $ loadAIG f
  case et of
    Left err -> fail $ "Reading AIG failed: " ++ err
    Right ntk -> return ntk

saveAIGPrim :: String -> AIGNetwork -> TopLevel ()
saveAIGPrim f n = io $ AIG.writeAiger f n

saveAIGasCNFPrim :: String -> AIGNetwork -> TopLevel ()
saveAIGasCNFPrim f (AIG.Network be ls) =
  case ls of
    [l] -> do _ <- io $ GIA.writeCNF be l f
              return ()
    _ -> fail "save_aig_as_cnf: non-boolean term"

-- | Tranlsate a SAWCore term into an AIG
bitblastPrim :: SharedContext -> Term -> IO AIGNetwork
bitblastPrim sc t = do
  t' <- rewriteEqs sc t
{-
  let s = ttSchema t'
  case s of
    C.Forall [] [] _ -> return ()
    _ -> fail $ "Attempting to bitblast a term with a polymorphic type: " ++ pretty s
-}
  BBSim.withBitBlastedTerm sawProxy sc bitblastPrimitives t' $ \be ls -> do
    return (AIG.Network be (toList ls))

-- | Read an AIG file representing a theorem or an arbitrary function
-- and represent its contents as a @Term@ lambda term. This is
-- inefficient but semantically correct.
readAIGPrim :: FilePath -> TopLevel TypedTerm
readAIGPrim f = do
  sc <- getSharedContext
  exists <- io $ doesFileExist f
  unless exists $ fail $ "AIG file " ++ f ++ " not found."
  opts <- getOptions
  et <- io $ readAIG opts sc f
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

  unless (fvpat == 0) $ fail $ unlines
    [ "pattern term is not closed", show tpat ]

  unless (fvrepl == 0) $ fail $ unlines
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

-- | Write a @Term@ representing a theorem or an arbitrary
-- function to an AIG file.
writeAIG :: SharedContext -> FilePath -> Term -> IO ()
writeAIG sc f t = do
  aig <- bitblastPrim sc t
  ABC.writeAiger f aig

-- | Like @writeAIG@, but takes an additional 'Integer' argument
-- specifying the number of input and output bits to be interpreted as
-- latches. Used to implement more friendly SAIG writers
-- @writeSAIGInferLatches@ and @writeSAIGComputedLatches@.
writeSAIG :: SharedContext -> FilePath -> Term -> Int -> IO ()
writeSAIG sc file tt numLatches = do
  aig <- bitblastPrim sc tt
  GIA.writeAigerWithLatches file aig numLatches

-- | Given a term a type '(i, s) -> (o, s)', call @writeSAIG@ on term
-- with latch bits set to '|s|', the width of 's'.
writeSAIGInferLatches :: SharedContext -> FilePath -> TypedTerm -> IO ()
writeSAIGInferLatches sc file tt = do
  ty <- scTypeOf sc (ttTerm tt)
  s <- getStateType ty
  let numLatches = sizeFiniteType s
  writeSAIG sc file (ttTerm tt) numLatches
  where
    die :: Monad m => String -> m a
    die why = fail $
      "writeSAIGInferLatches: " ++ why ++ ":\n" ++
      "term must have type of the form '(i, s) -> (o, s)',\n" ++
      "where 'i', 's', and 'o' are all fixed-width types,\n" ++
      "but type of term is:\n" ++ (pretty . ttSchema $ tt)

    -- Decompose type as '(i, s) -> (o, s)' and return 's'.
    getStateType :: Term -> IO FiniteType
    getStateType ty = do
      ty' <- scWhnf sc ty
      case ty' of
        (asPi -> Just (_nm, tp, body)) ->
          -- NB: if we get unexpected "state types are different"
          -- failures here than we need to 'scWhnf sc' before calling
          -- 'asFiniteType'.
          case (asFiniteTypePure tp, asFiniteTypePure body) of
            (Just dom, Just rng) ->
              case (dom, rng) of
                (FTTuple [_i, s], FTTuple [_o, s']) ->
                  if s == s' then
                    return s
                  else
                    die "state types are different"
                _ -> die "domain or range not a tuple type"
            _ -> die "domain or range not finite width"
        _ -> die "not a function type"

-- | Like @writeAIGInferLatches@, but takes an additional argument
-- specifying the number of input and output bits to be interpreted as
-- latches.
writeAIGComputedLatches ::
  SharedContext -> FilePath -> Term -> Int -> IO ()
writeAIGComputedLatches sc file term numLatches = do
  writeSAIG sc file term numLatches

writeCNF :: SharedContext -> FilePath -> Term -> IO ()
writeCNF sc f t = do
  AIG.Network be ls <- bitblastPrim sc t
  case ls of
    [l] -> do
      _ <- GIA.writeCNF be l f
      return ()
    _ -> fail "writeCNF: non-boolean term"

write_cnf :: SharedContext -> FilePath -> TypedTerm -> IO ()
write_cnf sc f (TypedTerm schema t) = do
  checkBooleanSchema schema
  writeCNF sc f t

-- | Write a @Term@ representing a theorem to an SMT-Lib version
-- 2 file.
writeSMTLib2 :: SharedContext -> FilePath -> Term -> IO ()
writeSMTLib2 sc f t = writeUnintSMTLib2 [] sc f t

-- | As above, but check that the type is monomorphic and boolean.
write_smtlib2 :: SharedContext -> FilePath -> TypedTerm -> IO ()
write_smtlib2 sc f (TypedTerm schema t) = do
  checkBooleanSchema schema
  writeSMTLib2 sc f t

-- | Write a @Term@ representing a theorem to an SMT-Lib version
-- 2 file, treating some constants as uninterpreted.
writeUnintSMTLib2 :: [String] -> SharedContext -> FilePath -> Term -> IO ()
writeUnintSMTLib2 unints sc f t = do
  (_, _, l) <- Prover.prepSBV sc unints t
  txt <- SBV.generateSMTBenchmark True l
  writeFile f txt

writeCore :: FilePath -> Term -> IO ()
writeCore path t = writeFile path (scWriteExternal t)

readCore :: FilePath -> TopLevel TypedTerm
readCore path = do
  sc <- getSharedContext
  io (mkTypedTerm sc =<< scReadExternal sc =<< readFile path)

withFirstGoal :: (ProofGoal -> TopLevel (a, SolverStats, Maybe ProofGoal)) -> ProofScript a
withFirstGoal f =
  StateT $ \(ProofState goals concl stats) ->
  case goals of
    [] -> fail "ProofScript failed: no subgoal"
    g : gs -> do
      (x, stats', mg') <- f g
      case mg' of
        Nothing -> return (x, ProofState gs concl (stats <> stats'))
        Just g' -> return (x, ProofState (g' : gs) concl (stats <> stats'))

quickcheckGoal :: SharedContext -> Integer -> ProofScript SV.SatResult
quickcheckGoal sc n = do
  opts <- Control.Monad.State.lift getOptions
  withFirstGoal $ \goal -> io $ do
    printOutLn opts Warn $ "WARNING: using quickcheck to prove goal..."
    hFlush stdout
    let tm = goalTerm goal
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
        "term has non-testable type"

assumeValid :: ProofScript SV.ProofResult
assumeValid = withFirstGoal $ \goal -> do
  printOutLnTop Warn $ "WARNING: assuming goal " ++ goalName goal ++ " is valid"
  let stats = solverStats "ADMITTED" (scSharedSize (goalTerm goal))
  return (SV.Valid stats, stats, Nothing)

assumeUnsat :: ProofScript SV.SatResult
assumeUnsat = withFirstGoal $ \goal -> do
  printOutLnTop Warn $ "WARNING: assuming goal " ++ goalName goal ++ " is unsat"
  let stats = solverStats "ADMITTED" (scSharedSize (goalTerm goal))
  return (SV.Unsat stats, stats, Nothing)

trivial :: ProofScript SV.SatResult
trivial = withFirstGoal $ \goal -> do
  checkTrue (goalTerm goal)
  return (SV.Unsat mempty, mempty, Nothing)
  where
    checkTrue :: Term -> TopLevel ()
    checkTrue t =
      case unwrapTermF t of
        Lambda _ _ t' -> checkTrue t'
        FTermF (CtorApp "Prelude.True" []) -> return ()
        _ -> fail "trivial: not a trivial goal"

split_goal :: ProofScript ()
split_goal =
  StateT $ \(ProofState goals concl stats) ->
  case goals of
    [] -> fail "ProofScript failed: no subgoal"
    (ProofGoal Existential _ _ _ _) : _ -> fail "not a universally-quantified goal"
    (ProofGoal Universal num ty name prop) : gs ->
      let (vars, body) = asLambdaList prop in
      case (isGlobalDef "Prelude.and" <@> return <@> return) body of
        Nothing -> fail "split_goal: goal not of form 'Prelude.and _ _'"
        Just (_ :*: p1 :*: p2) ->
          do sc <- getSharedContext
             t1 <- io $ scLambdaList sc vars p1
             t2 <- io $ scLambdaList sc vars p2
             let g1 = ProofGoal Universal num (ty ++ ".left") name t1
             let g2 = ProofGoal Universal num (ty ++ ".right") name t2
             return ((), ProofState (g1 : g2 : gs) concl stats)

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
  printOutLnTop Info $ show (ppTermDepth opts d t)

print_goal :: ProofScript ()
print_goal = withFirstGoal $ \goal -> do
  opts <- getTopLevelPPOpts
  printOutLnTop Info ("Goal " ++ goalName goal ++ ":")
  printOutLnTop Info (scPrettyTerm opts (goalTerm goal))
  return ((), mempty, Just goal)

print_goal_depth :: Int -> ProofScript ()
print_goal_depth n = withFirstGoal $ \goal -> do
  opts <- getTopLevelPPOpts
  printOutLnTop Info ("Goal " ++ goalName goal ++ ":")
  printOutLnTop Info $ show (ppTermDepth opts n (goalTerm goal))
  return ((), mempty, Just goal)

printGoalConsts :: ProofScript ()
printGoalConsts = withFirstGoal $ \goal -> do
  mapM_ (printOutLnTop Info) $ Map.keys (getConstantSet (goalTerm goal))
  return ((), mempty, Just goal)

printGoalSize :: ProofScript ()
printGoalSize = withFirstGoal $ \goal -> do
  let t = goalTerm goal
  printOutLnTop Info $ "Goal shared size: " ++ show (scSharedSize t)
  printOutLnTop Info $ "Goal unshared size: " ++ show (scTreeSize t)
  return ((), mempty, Just goal)

unfoldGoal :: [String] -> ProofScript ()
unfoldGoal names = withFirstGoal $ \goal -> do
  sc <- getSharedContext
  let trm = goalTerm goal
  trm' <- io $ scUnfoldConstants sc names trm
  return ((), mempty, Just (goal { goalTerm = trm' }))

simplifyGoal :: Simpset -> ProofScript ()
simplifyGoal ss = withFirstGoal $ \goal -> do
  sc <- getSharedContext
  let trm = goalTerm goal
  trm' <- io $ rewriteSharedTerm sc ss trm
  return ((), mempty, Just (goal { goalTerm = trm' }))

beta_reduce_goal :: ProofScript ()
beta_reduce_goal = withFirstGoal $ \goal -> do
  sc <- getSharedContext
  let trm = goalTerm goal
  trm' <- io $ betaNormalize sc trm
  return ((), mempty, Just (goal { goalTerm = trm' }))

-- | Bit-blast a @Term@ representing a theorem and check its
-- satisfiability using ABC.
{-
satABCold :: SharedContext -> ProofScript SV.SatResult
satABCold sc = StateT $ \g -> withBE $ \be -> do
  let t = goalTerm g
  t' <- prepForExport sc t
  let (args, _) = asLambdaList t'
      argNames = map fst args
      argTys = map snd args
  shapes <- mapM Old.parseShape argTys
  mbterm <- Old.bitBlast be t'
  case mbterm of
    Right bterm -> do
      case bterm of
        Old.BBool l -> do
          satRes <- ABC.checkSat be l
          case satRes of
            ABC.Unsat -> do
              ft <- scApplyPrelude_False sc
              return (SV.Unsat, g { goalTerm = ft })
            ABC.Sat cex -> do
              let r = liftCexBB shapes cex
              tt <- scApplyPrelude_True sc
              case r of
                Left err -> fail $ "Can't parse counterexample: " ++ err
                Right [v] ->
                  return (SV.Sat v, g { goalTerm = tt })
                Right vs -> do
                  return (SV.SatMulti (zip argNames vs), g { goalTerm = tt })
        _ -> fail "Can't prove non-boolean term."
    Left err -> fail $ "Can't bitblast: " ++ err
-}

returnsBool :: Term -> Bool
returnsBool ((asBoolType . snd . asPiList) -> Just ()) = True
returnsBool _ = False

checkBoolean :: SharedContext -> Term -> IO ()
checkBoolean sc t = do
  ty <- scTypeCheckError sc t
  unless (returnsBool ty) $
    fail $ "Invalid non-boolean type: " ++ show ty

-- | Bit-blast a @Term@ representing a theorem and check its
-- satisfiability using ABC.
satABC :: SharedContext -> ProofScript SV.SatResult
satABC sc = withFirstGoal $ \g -> io $ do
  let t0 = goalTerm g
  TypedTerm schema t <- (bindAllExts sc t0 >>= rewriteEqs sc >>= mkTypedTerm sc)
  checkBooleanSchema schema
  tp <- scWhnf sc =<< scTypeOf sc t
  let (args, _) = asPiList tp
      argNames = map fst args
  BBSim.withBitBlastedPred sawProxy sc bitblastPrimitives t $ \be lit0 shapes -> do
  let lit = case goalQuant g of
        Existential -> lit0
        Universal -> AIG.not lit0
  satRes <- AIG.checkSat be lit
  ft <- scApplyPrelude_False sc
  let stats = solverStats "ABC" (scSharedSize t0)
  case satRes of
    AIG.Unsat ->
      case goalQuant g of
        Existential -> return (SV.Unsat stats, stats, Just (g { goalTerm = ft }))
        Universal -> return (SV.Unsat stats, stats, Nothing)
    AIG.Sat cex -> do
      let r = liftCexBB shapes cex
      case r of
        Left err -> fail $ "Can't parse counterexample: " ++ err
        Right vs
          | length argNames == length vs -> do
            let r' = SV.SatMulti stats (zip argNames (map toFirstOrderValue vs))
            case goalQuant g of
              Existential -> return (r', stats, Nothing)
              Universal -> return (r', stats, Just (g { goalTerm = ft }))
          | otherwise -> fail $ unwords ["ABC SAT results do not match expected arguments", show argNames, show vs]
    AIG.SatUnknown -> fail "Unknown result from ABC"

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

satExternal :: Bool -> SharedContext -> String -> [String]
            -> ProofScript SV.SatResult
satExternal doCNF sc execName args = withFirstGoal $ \g -> io $ do
  t <- rewriteEqs sc (goalTerm g)
  tp <- scWhnf sc =<< scTypeOf sc t
  let cnfName = goalType g ++ show (goalNum g) ++ ".cnf"
      argNames = map fst (fst (asPiList tp))
  checkBoolean sc t
  (path, fh) <- openTempFile "." cnfName
  hClose fh -- Yuck. TODO: allow writeCNF et al. to work on handles.
  let args' = map replaceFileName args
      replaceFileName "%f" = path
      replaceFileName a = a
  BBSim.withBitBlastedPred sawProxy sc bitblastPrimitives t $ \be l0 shapes -> do
  let l = case goalQuant g of
        Existential -> l0
        Universal -> AIG.not l0
  vars <- (if doCNF then GIA.writeCNF else writeAIGWithMapping) be l path
  (_ec, out, err) <- readProcessWithExitCode execName args' ""
  removeFile path
  unless (null err) $
    print $ unlines ["Standard error from SAT solver:", err]
  let ls = lines out
      sls = filter ("s " `isPrefixOf`) ls
      vls = filter ("v " `isPrefixOf`) ls
  ft <- scApplyPrelude_False sc
  let stats = solverStats ("external SAT:" ++ execName) (scSharedSize t)
  case (sls, vls) of
    (["s SATISFIABLE"], _) -> do
      let bs = parseDimacsSolution vars vls
      let r = liftCexBB shapes bs
      case r of
        Left msg -> fail $ "Can't parse counterexample: " ++ msg
        Right vs
          | length argNames == length vs -> do
            let r' = SV.SatMulti stats (zip argNames (map toFirstOrderValue vs))
            case goalQuant g of
              Universal -> return (r', stats, Just (g { goalTerm = ft }))
              Existential -> return (r', stats, Nothing)
          | otherwise -> fail $ unwords ["external SAT results do not match expected arguments", show argNames, show vs]
    (["s UNSATISFIABLE"], []) ->
      case goalQuant g of
        Universal -> return (SV.Unsat stats, stats, Nothing)
        Existential -> return (SV.Unsat stats, stats, Just (g { goalTerm = ft }))
    _ -> fail $ "Unexpected result from SAT solver:\n" ++ out

writeAIGWithMapping :: GIA.GIA s -> GIA.Lit s -> FilePath -> IO [Int]
writeAIGWithMapping be l path = do
  nins <- GIA.inputCount be
  ABC.writeAiger path (ABC.Network be [l])
  return [1..nins]

rewriteEqs :: SharedContext -> Term -> IO Term
rewriteEqs sc t = do
  let eqs = map (mkIdent preludeName)
            [ "eq_Bool", "eq_Nat", "eq_bitvector", "eq_VecBool"
            , "eq_VecVec" ]
  rs <- scEqsRewriteRules sc eqs
  ss <- addRules rs <$> basic_ss sc
  t' <- rewriteSharedTerm sc ss t
  return t'

-- | Bit-blast a @Term@ representing a theorem and check its
-- satisfiability using the RME library.
satRME :: SharedContext -> ProofScript SV.SatResult
satRME sc = withFirstGoal $ \g -> io $ do
  let t0 = goalTerm g
  TypedTerm schema t <- (bindAllExts sc t0 >>= rewriteEqs sc >>= mkTypedTerm sc)
  checkBooleanSchema schema
  tp <- scWhnf sc =<< scTypeOf sc t
  let (args, _) = asPiList tp
      argNames = map fst args
  RME.withBitBlastedPred sc Map.empty t $ \lit0 shapes -> do
  let lit = case goalQuant g of
        Existential -> lit0
        Universal -> RME.compl lit0
  let stats = solverStats "RME" (scSharedSize t0)
  case RME.sat lit of
    Nothing ->
      case goalQuant g of
        Existential -> do ft <- scApplyPrelude_False sc
                          return (SV.Unsat stats, stats, Just (g { goalTerm = ft }))
        Universal -> return (SV.Unsat stats, stats, Nothing)
    Just cex -> do
      let m = Map.fromList cex
      let n = sum (map sizeFiniteType shapes)
      let bs = map (maybe False id . flip Map.lookup m) $ take n [0..]
      let r = liftCexBB shapes bs
      case r of
        Left err -> fail $ "Can't parse counterexample: " ++ err
        Right vs
          | length argNames == length vs -> do
            let r' = SV.SatMulti stats (zip argNames (map toFirstOrderValue vs))
            case goalQuant g of
              Existential -> return (r', stats, Nothing)
              Universal -> return (r', stats, Just g)
          | otherwise -> fail $ unwords ["RME SAT results do not match expected arguments", show argNames, show vs]

codegenSBV :: SharedContext -> FilePath -> [String] -> String -> TypedTerm -> IO ()
codegenSBV sc path unints fname (TypedTerm _schema t) =
  SBVSim.sbvCodeGen sc sbvPrimitives unints mpath fname t
  where mpath = if null path then Nothing else Just path


-- | Bit-blast a @Term@ representing a theorem and check its
-- satisfiability using SBV. (Currently ignores satisfying assignments.)
satSBV :: SBV.SMTConfig -> SharedContext -> ProofScript SV.SatResult
satSBV conf sc = satUnintSBV conf sc []

-- | Bit-blast a @Term@ representing a theorem and check its
-- satisfiability using SBV. (Currently ignores satisfying assignments.)
-- Constants with names in @unints@ are kept as uninterpreted functions.
satUnintSBV :: SBV.SMTConfig -> SharedContext -> [String] -> ProofScript SV.SatResult
satUnintSBV conf sc unints = withFirstGoal $ \g -> io $ do
  let mode = case goalQuant g of
               Existential -> CheckSat
               Universal   -> Prove

  (mb,stats) <- Prover.satUnintSBV conf sc unints mode (goalTerm g)

  let nope r = do ft <- scApplyPrelude_False sc
                  return (r, stats, Just g { goalTerm = ft })

  case (mode,mb) of
    (CheckSat, Just a)  -> return (SV.SatMulti stats a, stats, Nothing)
    (CheckSat, Nothing) -> nope (SV.Unsat stats)
    (Prove, Nothing)    -> return (SV.Unsat stats, stats, Nothing)
    (Prove, Just a)     -> nope (SV.SatMulti stats a)


satBoolector :: SharedContext -> ProofScript SV.SatResult
satBoolector = satSBV SBV.boolector

satZ3 :: SharedContext -> ProofScript SV.SatResult
satZ3 = satSBV SBV.z3

satCVC4 :: SharedContext -> ProofScript SV.SatResult
satCVC4 = satSBV SBV.cvc4

satMathSAT :: SharedContext -> ProofScript SV.SatResult
satMathSAT = satSBV SBV.mathSAT

satYices :: SharedContext -> ProofScript SV.SatResult
satYices = satSBV SBV.yices

satUnintBoolector :: SharedContext -> [String] -> ProofScript SV.SatResult
satUnintBoolector = satUnintSBV SBV.boolector

satUnintZ3 :: SharedContext -> [String] -> ProofScript SV.SatResult
satUnintZ3 = satUnintSBV SBV.z3

satUnintCVC4 :: SharedContext -> [String] -> ProofScript SV.SatResult
satUnintCVC4 = satUnintSBV SBV.cvc4

satUnintMathSAT :: SharedContext -> [String] -> ProofScript SV.SatResult
satUnintMathSAT = satUnintSBV SBV.mathSAT

satUnintYices :: SharedContext -> [String] -> ProofScript SV.SatResult
satUnintYices = satUnintSBV SBV.yices

satWithExporter :: (SharedContext -> FilePath -> Term -> IO ())
                -> SharedContext
                -> String
                -> String
                -> ProofScript SV.SatResult
satWithExporter exporter sc path ext = withFirstGoal $ \g -> io $ do
  t <- case goalQuant g of
         Existential -> return (goalTerm g)
         Universal -> do
           let t0 = goalTerm g
           ty <- scTypeOf sc t0
           let (ts, tf) = asPiList ty
           tf' <- scWhnf sc tf
           case asBoolType tf' of
             Nothing -> fail $ "Invalid non-boolean type: " ++ show ty
             Just () -> return ()
           negTerm (map snd ts) t0
  exporter sc ((path ++ "." ++ goalType g ++ show (goalNum g)) ++ ext) t
  let stats = solverStats ("offline:"++ drop 1 ext)
                          (scSharedSize t)
  case goalQuant g of
    Existential -> return (SV.Unsat stats, stats, Just g)
    Universal -> return (SV.Unsat stats, stats, Nothing)
  where
    negTerm :: [Term] -> Term -> IO Term
    negTerm [] p = scNot sc p
    negTerm (t1 : ts) p = do
      (x, ty, p') <-
        case unwrapTermF p of
          Lambda x ty p' -> return (x, ty, p')
          _ -> do
            p1 <- incVars sc 0 1 p
            x0 <- scLocalVar sc 0
            p' <- scApply sc p1 x0
            return ("x", t1, p')
      scLambda sc x ty =<< negTerm ts p'

satAIG :: SharedContext -> FilePath -> ProofScript SV.SatResult
satAIG sc path = satWithExporter writeAIG sc path ".aig"

satCNF :: SharedContext -> FilePath -> ProofScript SV.SatResult
satCNF sc path = satWithExporter writeCNF sc path ".cnf"

satExtCore :: SharedContext -> FilePath -> ProofScript SV.SatResult
satExtCore sc path = satWithExporter (const writeCore) sc path ".extcore"

satSMTLib2 :: SharedContext -> FilePath -> ProofScript SV.SatResult
satSMTLib2 sc path = satWithExporter writeSMTLib2 sc path ".smt2"

satUnintSMTLib2 :: SharedContext -> [String] -> FilePath -> ProofScript SV.SatResult
satUnintSMTLib2 sc unints path = satWithExporter (writeUnintSMTLib2 unints) sc path ".smt2"

liftCexBB :: [FiniteType] -> [Bool] -> Either String [FiniteValue]
liftCexBB tys bs =
  case readFiniteValues tys bs of
    Nothing -> Left "Failed to lift counterexample"
    Just fvs -> Right fvs

-- | Translate a @Term@ representing a theorem for input to the
-- given validity-checking script and attempt to prove it.
provePrim :: ProofScript SV.SatResult
          -> TypedTerm -> TopLevel SV.ProofResult
provePrim script t = do
  io $ checkBooleanSchema (ttSchema t)
  (r, pstate) <- runStateT script (startProof (ProofGoal Universal 0 "prove" "prove" (ttTerm t)))
  case finishProof pstate of
    (_stats, Just _)  -> return ()
    (_stats, Nothing) -> printOutLnTop Info $ "prove: " ++ show (length (psGoals pstate)) ++ " unsolved subgoal(s)"
  return (SV.flipSatResult r)

provePrintPrim :: ProofScript SV.SatResult
               -> TypedTerm -> TopLevel Theorem
provePrintPrim script t = do
  (r, pstate) <- runStateT script (startProof (ProofGoal Universal 0 "prove" "prove" (ttTerm t)))
  opts <- rwPPOpts <$> getTopLevelRW
  case finishProof pstate of
    (_,Just thm) -> do printOutLnTop Info "Valid"
                       return thm
    (_,Nothing) -> fail $ "prove: " ++ show (length (psGoals pstate)) ++ " unsolved subgoal(s)\n"
                     ++ SV.showsProofResult opts (SV.flipSatResult r) ""

satPrim :: ProofScript SV.SatResult -> TypedTerm
        -> TopLevel SV.SatResult
satPrim script t = do
  io $ checkBooleanSchema (ttSchema t)
  evalStateT script (startProof (ProofGoal Existential 0 "sat" "sat" (ttTerm t)))

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
cryptolSimpset = do
  sc <- getSharedContext
  io $ scSimpset sc cryptolDefs [] []
  where cryptolDefs = filter (not . excluded) $
                      moduleDefs CryptolSAW.cryptolModule
        excluded d = defIdent d `elem` [ "Cryptol.fix" ]

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

addPreludeDefs :: [String] -> Simpset
              -> TopLevel Simpset
addPreludeDefs names ss = do
  sc <- getSharedContext
  defs <- io $ mapM (getDef sc) names -- FIXME: warn if not found
  defRules <- io $ concat <$> (mapM (scDefRewriteRules sc) defs)
  return (addRules defRules ss)
    where qualify = mkIdent (mkModuleName ["Prelude"])
          getDef sc n =
            case findDef (scModule sc) (qualify n) of
              Just d -> return d
              Nothing -> fail $ "Prelude definition " ++ n ++ " not found"

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
addsimp (Theorem t) ss = addRule (ruleOfProp t) ss

addsimp' :: Term -> Simpset -> Simpset
addsimp' t ss = addRule (ruleOfProp t) ss

addsimps :: [Theorem] -> Simpset -> Simpset
addsimps thms ss =
  foldr (\thm -> addRule (ruleOfProp (thmTerm thm))) ss thms

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
  return $ Concrete.evalSharedTerm (scModule sc) concretePrimitives tm'

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
  v <- io $ rethrowEvalError $ return $ SV.evaluateTypedTerm sc t
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
  v <- io $ rethrowEvalError $ return $ SV.evaluateTypedTerm sc t'
  io $ C.runEval SV.quietEvalOpts (C.fromWord "eval_int" v)

-- Predicate on Cryptol types true of integer types, i.e. types
-- @[n]Bit@ for *finite* @n@.
isInteger :: C.Type -> Bool
isInteger (C.tIsSeq -> Just (C.tIsNum -> Just _, C.tIsBit -> True)) = True
isInteger _ = False

eval_list :: TypedTerm -> TopLevel [TypedTerm]
eval_list t = do
  sc <- getSharedContext
  (n, a) <-
    case ttSchema t of
      C.Forall [] [] (C.tIsSeq -> Just (C.tIsNum -> Just n, a)) -> return (n, a)
      _ -> fail "eval_list: not a monomorphic array type"
  n' <- io $ scNat sc (fromInteger n)
  a' <- io $ Cryptol.importType sc Cryptol.emptyEnv a
  idxs <- io $ traverse (scNat sc) [0 .. fromInteger n - 1]
  ts <- io $ traverse (scAt sc n' a' (ttTerm t)) idxs
  return (map (TypedTerm (C.tMono a)) ts)

-- | Default the values of the type variables in a typed term.
defaultTypedTerm :: Options -> SharedContext -> C.SolverConfig -> TypedTerm -> IO TypedTerm
defaultTypedTerm opts sc cfg (TypedTerm schema trm) = do
  mdefault <- C.withSolver cfg (\s -> C.defaultReplExpr s undefined schema)
  let inst = do (soln, _) <- mdefault
                mapM (`lookup` soln) (C.sVars schema)
  case inst of
    Nothing -> return (TypedTerm schema trm)
    Just tys -> do
      let vars = C.sVars schema
      let nms = C.addTNames vars IntMap.empty
      mapM_ (warnDefault nms) (zip vars tys)
      let applyType :: Term -> Cryptol.Type -> IO Term
          applyType t ty = do
            ty' <- Cryptol.importType sc Cryptol.emptyEnv ty
            scApply sc t ty'
      trm' <- foldM applyType trm tys
      let su = C.listSubst (zip (map C.tpVar vars) tys)
      let schema' = C.Forall [] [] (C.apSubst su (C.sType schema))
      return (TypedTerm schema' trm')
  where
    warnDefault ns (x,t) =
      printOutLn opts Info $ show $ C.text "Assuming" C.<+> C.ppWithNames ns (x :: C.TParam) C.<+> C.text "=" C.<+> C.pp t

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
parseCore input = do
  sc <- getSharedContext
  let base = "<interactive>"
      path = "<interactive>"
  let (uterm, errs) = parseSAWTerm base path (B.fromString input)
  mapM_ (printOutLnTop Opts.Error . show) errs
  unless (null errs) $ fail $ show errs
  let imps = [ UntypedAST.Import False (Position.PosPair pos (mkModuleName ["Prelude"])) Nothing Nothing ]
      pos = Position.Pos base path 0 0
  (t, _tp) <- case Verifier.SAW.Typechecker.checkTerm [preludeModule] imps uterm of
    Left err -> fail (show err)
    Right x -> return x
  io $ scSharedTerm sc t

parse_core :: String -> TopLevel TypedTerm
parse_core input = do
  t <- parseCore input
  sc <- getSharedContext
  io $ mkTypedTerm sc t

prove_core :: ProofScript SV.SatResult -> String -> TopLevel Theorem
prove_core script input = do
  t <- parseCore input
  (r', pstate) <- runStateT script (startProof (ProofGoal Universal 0 "prove" "prove" t))
  let r = SV.flipSatResult r'
  opts <- rwPPOpts <$> getTopLevelRW
  case finishProof pstate of
    (_,Just thm) -> return thm
    (_,Nothing)  -> fail $ "prove_core: " ++ show (length (psGoals pstate)) ++ " unsolved subgoal(s)\n"
                      ++ SV.showsProofResult opts r ""

core_axiom :: String -> TopLevel Theorem
core_axiom input = do
  t <- parseCore input
  return (Theorem t)

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

    noLoc :: String -> Located String
    noLoc x = Located x x (PosInternal "cryptol_prims")

    parsePrim :: (String, Ident, String) -> TopLevel (C.Name, TypedTerm)
    parsePrim (n, i, s) = do
      sc <- getSharedContext
      rw <- getTopLevelRW
      let cenv = rwCryptol rw
      let mname = C.packModName ["Prims"]
      (n', cenv') <- io $ CEnv.declareName cenv mname n
      s' <- io $ CEnv.parseSchema cenv' (noLoc s)
      t' <- io $ scGlobalDef sc i
      putTopLevelRW $ rw { rwCryptol = cenv' }
      return (n', TypedTerm s' t')
