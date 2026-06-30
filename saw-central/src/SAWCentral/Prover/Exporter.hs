{-# Language CPP #-}
{-# Language GADTs #-}
{-# Language ImplicitParams #-}
{-# Language NamedFieldPuns #-}
{-# Language OverloadedStrings #-}
{-# Language ViewPatterns #-}
{-# Language ExplicitForAll #-}
{-# Language FlexibleContexts #-}
{-# Language ScopedTypeVariables #-}
{-# Language TypeApplications #-}
{-# Language TupleSections #-}
module SAWCentral.Prover.Exporter
  ( proveWithSATExporter
  , proveWithPropExporter

    -- * External formats
  , writeAIG
  , writeAIGviaVerilog
  , writeAIG_SATviaVerilog
  , writeAIG_SAT
  , writeSAIG
  , writeSAIGInferLatches
  , writeAIGComputedLatches
  , writeCNF
  , writeCNFviaVerilog
  , writeCNF_SATviaVerilog
  , write_cnf
  , write_cnf_external
  , writeSMTLib2
  , writeSMTLib2What4
  , write_smtlib2
  , write_w4_smtlib2
  , writeRocqCryptolPrimitivesForSAWCore
  , writeLeanCryptolPrimitivesForSAWCore
  , writeRocqCryptolModule
  , writeRocqSAWCorePrelude
  , writeLeanSAWCorePrelude
  , writeRocqTerm
  , rocqTranslationConfiguration
  , writeRocqProp
  , writeLeanTerm
  , leanTranslationConfiguration
  , writeLeanProp
  , writeLeanCryptolModule
  , dumpLeanResidualPrimitives
  , iterateNormalizeToFixedPoint
  , scNormalizeForLean
  , scNormalizeForLeanMaxIters
  , discoverNatRecReachers
  , auditPreludePrimitivesForLean
  , auditOpaqueBuiltinsCoveredBySpecialTreatment
  , writeCore
  , writeVerilog
  , writeVerilogSAT
  , write_verilog
  , writeCoreProp

    -- * Misc
  , bitblastPrim
  ) where

import Data.Foldable(toList)
import qualified Data.Foldable as Foldable

import Control.Monad (unless)
import Control.Monad.Except (runExceptT)
import Control.Monad.State (gets, liftIO)
import Data.IORef (newIORef, readIORef, modifyIORef')
import qualified Data.AIG as AIG
import qualified Data.ByteString as BS
import Data.Maybe (mapMaybe)
import Data.Parameterized.Nonce (globalNonceGenerator)
import Data.Parameterized.Some (Some(..))
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import System.Directory (createDirectoryIfMissing, removeFile)
import System.FilePath (takeBaseName, takeDirectory)
import System.IO
import System.IO.Temp(emptySystemTempFile)
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Vector as V
import Prettyprinter (vcat)
import Prettyprinter.Render.Text

import Lang.JVM.ProcessUtils (readProcessExitIfFailure)

import SAWCore.ExternalFormat(scWriteExternal)
import SAWCore.FiniteValue
import qualified Data.IntMap as IntMap
import SAWCore.Module (emptyModule, moduleDecls,
                       allModuleDefs, defBody, defName)
import SAWCore.Name (VarName(..), mkModuleName,
                     nameIndex, nameInfo,
                     toAbsoluteName,
                     identName, identModule)
import SAWCore.Term.Functor (FlatTermF(..), recursorDataType)
import SAWCore.Recognizer (asPi, asGlobalApply, asNat, asBool)
import SAWCore.Prelude (preludeModule)
import SAWCore.SATQuery
import SAWCore.SharedTerm as SC

import CryptolSAWCore.Cryptol (refreshCryptolEnv)
import CryptolSAWCore.CryptolEnv (initCryptolEnv, loadCryptolModule)
import CryptolSAWCore.Prelude (cryptolModule, scLoadPreludeModule, scLoadCryptolModule)
import CryptolSAWCore.TypedTerm

import qualified SAWCoreRocq.Rocq as Rocq
import qualified Language.Rocq.AST as Rocq
import qualified SAWCoreLean.Lean as Lean
import qualified SAWCoreLean.SpecialTreatment as Lean
import qualified Language.Lean.AST as Lean
import qualified SAWCoreAIG.BitBlast as BBSim
import qualified SAWCore.Simulator.Value as Sim
import qualified SAWCoreWhat4.What4 as W4Sim
import qualified SAWCoreSBV.SBV as SBV
import qualified SAWCoreWhat4.What4 as W -- XXX duplicate!?
import SAWCoreWhat4.ReturnTrip (newSAWCoreExprBuilder, sawCoreState)

import qualified SAWCore.Parser.AST as Un

import SAWCentral.Proof
  (Prop, Sequent, propSize, sequentSharedSize, propToTerm, predicateToSATQuery, sequentToSATQuery)
import SAWCentral.Prover.SolverStats
import SAWCentral.Prover.Util
import SAWCentral.Prover.What4
import SAWCentral.Value

import qualified What4.Interface as W4
import qualified What4.Expr.Builder as W4
import What4.Config (extendConfig, getOptionSetting, setOpt)
import What4.Interface (getConfiguration, IsSymExprBuilder)
import What4.Protocol.SMTLib2 (writeDefaultSMT2)
import What4.Protocol.SMTLib2.Response (smtParseOptions)
import What4.Protocol.VerilogWriter (exprsVerilog)
import What4.Solver.Adapter
import qualified What4.SWord as W4Sim

proveWithSATExporter ::
  (FilePath -> SATQuery -> TopLevel a) ->
  Set VarIndex ->
  FilePath ->
  Sequent ->
  TopLevel SolverStats
proveWithSATExporter exporter unintSet path goal =
  do sc <- getSharedContext
     satq <- io $ sequentToSATQuery sc unintSet goal
     _ <- exporter path satq
     let stats = solverStats ("offline: " <> Text.pack path) (sequentSharedSize goal)
     return stats


proveWithPropExporter ::
  (FilePath -> Prop -> TopLevel a) ->
  FilePath ->
  Prop ->
  TopLevel SolverStats
proveWithPropExporter exporter path goal =
  do _ <- exporter path goal
     let stats = solverStats ("offline: " <> Text.pack path) (propSize goal)
     return stats

--------------------------------------------------------------------------------

writeAIG_SAT ::
  FilePath ->
  SATQuery ->
  TopLevel [(VarName, FiniteType)]
writeAIG_SAT f satq =
  do AIGProxy proxy <- getProxy
     sc <- getSharedContext
     io $ BBSim.withBitBlastedSATQuery proxy sc mempty satq $ \g l vars ->
         do AIG.writeAiger f (AIG.Network g [l])
            return vars

-- | Write a @Term@ representing a an arbitrary function to an AIG file.
writeAIG :: FilePath -> Term -> TopLevel ()
writeAIG f t = do
  do sc <- getSharedContext
     AIGProxy proxy <- getProxy
     aig <- io $ bitblastPrim proxy sc t
     io $ AIG.writeAiger f aig

withABCVerilog :: FilePath -> Term -> (FilePath -> String) -> TopLevel ()
withABCVerilog fileName t buildCmd =
  do verilogFile <- io $ emptySystemTempFile (takeBaseName fileName ++ ".v")
     sc <- getSharedContext
     write_verilog sc verilogFile t
     io $
       do (out, err) <- readProcessExitIfFailure "abc" ["-q", buildCmd verilogFile]
          unless (null out) $ putStrLn "ABC output:" >> putStrLn out
          unless (null err) $ putStrLn "ABC errors:" >> putStrLn err
          removeFile verilogFile

-- | Write a @SATQuery@ to an AIG file by using ABC to convert a Verilog
-- file.
writeAIG_SATviaVerilog :: FilePath -> SATQuery -> TopLevel ()
writeAIG_SATviaVerilog f query =
  do sc <- getSharedContext
     t <- io (satQueryAsTerm sc query)
     writeAIGviaVerilog f t

-- | Write a @Term@ representing a an arbitrary function to an AIG file
-- by using ABC to convert a Verilog file.
writeAIGviaVerilog :: FilePath -> Term -> TopLevel ()
writeAIGviaVerilog aigFile t =
  withABCVerilog aigFile t $
      \verilogFile -> "%read " ++ verilogFile ++ "; %blast; &write " ++ aigFile

-- | Write a @SATQuery@ to a CNF file by using ABC to convert a Verilog
-- file.
writeCNF_SATviaVerilog :: FilePath -> SATQuery -> TopLevel ()
writeCNF_SATviaVerilog f query =
  do sc <- getSharedContext
     t <- io (satQueryAsTerm sc query)
     writeCNFviaVerilog f t

-- | Write a @Term@ representing a an arbitrary function to a CNF file
-- by using ABC to convert a Verilog file.
writeCNFviaVerilog :: FilePath -> Term -> TopLevel ()
writeCNFviaVerilog cnfFile t =
  withABCVerilog cnfFile t $
      \verilogFile -> "%read " ++ verilogFile ++ "; %blast; &write_cnf " ++ cnfFile

-- | Like @writeAIG@, but takes an additional 'Integer' argument
-- specifying the number of input and output bits to be interpreted as
-- latches. Used to implement more friendly SAIG writers
-- @writeSAIGInferLatches@ and @writeSAIGComputedLatches@.
writeSAIG :: FilePath -> Term -> Int -> TopLevel ()
writeSAIG file tt numLatches = do
  do sc <- getSharedContext
     AIGProxy proxy <- getProxy
     aig <- io $ bitblastPrim proxy sc tt
     io $ AIG.writeAigerWithLatches file aig numLatches

-- | Given a term a type '(i, s) -> (o, s)', call @writeSAIG@ on term
-- with latch bits set to '|s|', the width of 's'.
writeSAIGInferLatches :: TypedTerm -> TopLevel (FilePath -> IO ())
writeSAIGInferLatches tt = do
  sc <- getSharedContext
  ty <- io $ scTypeOf sc (ttTerm tt)
  s <- getStateType sc ty
  let numLatches = sizeFiniteType s
  AIGProxy proxy <- getProxy
  return $ \file ->
    do aig <- bitblastPrim proxy sc (ttTerm tt)
       AIG.writeAigerWithLatches file aig numLatches
  where
    die :: String -> TopLevel a
    die why = do
     sc <- getSharedContext
     tt' <- io $ prettyTypedTermType sc (ttType tt)
     throwTopLevel $
      "writeSAIGInferLatches: " ++ why ++ ":\n" ++
      "term must have type of the form '(i, s) -> (o, s)',\n" ++
      "where 'i', 's', and 'o' are all fixed-width types,\n" ++
      "but type of term is:\n" ++ show tt'

    -- Decompose type as '(i, s) -> (o, s)' and return 's'.
    getStateType :: SharedContext -> Term -> TopLevel FiniteType
    getStateType sc ty = do
      ty' <- io $ scWhnf sc ty
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
writeAIGComputedLatches :: FilePath -> Term -> Int -> TopLevel ()
writeAIGComputedLatches file term numLatches =
  writeSAIG file term numLatches

writeCNF :: FilePath -> SATQuery -> TopLevel ()
writeCNF f satq =
  do sc <- getSharedContext
     AIGProxy proxy <- getProxy
     _ <- io $ BBSim.withBitBlastedSATQuery proxy sc mempty satq $ \g l _vars -> AIG.writeCNF g l f
     return ()

write_cnf :: FilePath -> TypedTerm -> TopLevel ()
write_cnf f (TypedTerm schema t) = do
  sc <- getSharedContext
  io $ checkBooleanSchema sc schema
  satq <- io (predicateToSATQuery sc mempty t)
  writeCNF f satq

write_cnf_external :: FilePath -> TypedTerm -> TopLevel ()
write_cnf_external f (TypedTerm schema t) = do
  sc <- getSharedContext
  io $ checkBooleanSchema sc schema
  writeCNFviaVerilog f t

-- | Write a @Term@ representing a predicate (i.e. a monomorphic
-- function returning a boolean) to an SMT-Lib version 2 file. The goal
-- is to pass the term through as directly as possible, so we interpret
-- it as an existential.
write_smtlib2 :: FilePath -> TypedTerm -> TopLevel ()
write_smtlib2 f (TypedTerm schema t) = do
  sc <- getSharedContext
  io $ checkBooleanSchema sc schema
  satq <- io $ predicateToSATQuery sc mempty t
  writeSMTLib2 f satq

-- | Write a @Term@ representing a predicate (i.e. a monomorphic
-- function returning a boolean) to an SMT-Lib version 2 file. The goal
-- is to pass the term through as directly as possible, so we interpret
-- it as an existential. This version uses What4 instead of SBV.
write_w4_smtlib2 :: FilePath -> TypedTerm -> TopLevel ()
write_w4_smtlib2 f (TypedTerm schema t) = do
  sc <- getSharedContext
  io $ checkBooleanSchema sc schema
  satq <- io $ predicateToSATQuery sc mempty t
  writeSMTLib2What4 f satq

-- | Write a SAT query to an SMT-Lib version 2 file.
writeSMTLib2 :: FilePath -> SATQuery -> TopLevel ()
writeSMTLib2 f satq = getSharedContext >>= \sc -> io $
  do (_, _, l) <- SBV.sbvSATQuery sc mempty satq
     txt <- SBV.generateSMTBenchmarkSat l
     writeFile f txt

-- | Write a SAT query an SMT-Lib version 2 file.
-- This version uses What4 instead of SBV.
writeSMTLib2What4 :: FilePath -> SATQuery -> TopLevel ()
writeSMTLib2What4 f satq = do
  sc <- getSharedContext
  what4PushMuxOps <- gets rwWhat4PushMuxOps
  io $ do
     sym <- W4.newExprBuilder W4.FloatRealRepr St globalNonceGenerator
     (_varMap, lits) <- W.w4Solve sym sc satq
     let cfg = getConfiguration sym
     extendConfig smtParseOptions cfg
     pushMuxOpsSetting <- getOptionSetting W4.pushMuxOpsOption cfg
     _ <- setOpt pushMuxOpsSetting what4PushMuxOps
     withFile f WriteMode $ \h ->
       writeDefaultSMT2 () "Offline SMTLib2" defaultWriteSMTLIB2Features Nothing sym h lits

writeCore :: FilePath -> Term -> TopLevel ()
writeCore path t = io $ writeFile path (scWriteExternal t)

write_verilog :: SharedContext -> FilePath -> Term -> TopLevel ()
write_verilog sc path t = io $ writeVerilog sc path t

writeVerilogSAT :: FilePath -> SATQuery -> TopLevel [(VarName, FiniteType)]
writeVerilogSAT path satq = do
  sc <- getSharedContext
  io $ do
     sym <- newSAWCoreExprBuilder sc False
     -- For SAT checking, we don't care what order the variables are in,
     -- but only that we can correctly keep track of the connection
     -- between inputs and assignments.
     let varList  = Map.toList (satVariables satq)
     let argNames = map fst varList
     let argTys = map snd varList
     (vars, bvals) <- W.w4Solve sym sc satq
     bval <- W4.andAllOf sym traverse bvals
     let f fot = case toFiniteType fot of
                   Nothing -> fail $ "writeVerilogSAT: Unsupported argument type " ++ show fot
                   Just ft -> return ft
     let argSValues = map (snd . snd) vars
     let argSValueNames = zip argSValues (map vnName argNames)
     argTys' <- traverse f argTys
     let mkInput (v, nm) = map (,nm) <$> flattenSValue sym v
     ins <- concat <$> mapM mkInput argSValueNames
     edoc <- runExceptT $ exprsVerilog sym ins [Some bval] "f"
     case edoc of
       Left err -> fail $ "Failed to translate to Verilog: " ++ err
       Right doc -> do
         h <- openFile path WriteMode
         hPutDoc h doc
         hPutStrLn h ""
         hClose h
     return (zip argNames argTys')

flattenSValue :: IsSymExprBuilder sym => sym -> W4Sim.SValue sym -> IO [Some (W4.SymExpr sym)]
flattenSValue _ (Sim.VBool b) = return [Some b]
flattenSValue _ (Sim.VWord (W4Sim.DBV w)) = return [Some w]
flattenSValue sym (Sim.VCtorApp 0 _ [l, r]) =
  do lv <- Sim.force l
     rv <- Sim.force r
     ls <- flattenSValue sym lv
     rs <- flattenSValue sym rv
     return (ls ++ rs)
flattenSValue sym (Sim.VVector ts) =
  do vs <- mapM Sim.force ts
     let getBool (Sim.VBool b) = Just b
         getBool _ = Nothing
         mbs = V.map getBool vs
     case sequence mbs of
       Just bs ->
         do w <- W4Sim.bvPackBE sym bs
            case w of
              W4Sim.DBV bv -> return [Some bv]
              W4Sim.ZBV -> return []
       Nothing -> concat <$> mapM (flattenSValue sym) vs
flattenSValue _ sval = fail $ "write_verilog: unsupported result type: " ++ show sval

writeVerilog :: SharedContext -> FilePath -> Term -> IO ()
writeVerilog sc path t = do
  sym <- newSAWCoreExprBuilder sc False
  let st = sawCoreState sym
  -- For writing Verilog in the general case, it's convenient for any
  -- lambda-bound inputs to appear first in the module input list, in
  -- order, followed by free variables (probably in the order seen
  -- during traversal, because that's at least _a_ deterministic order).
  (argNames, args, _, sval) <- W4Sim.w4EvalAny sym st sc mempty mempty t
  es <- flattenSValue sym sval
  let mkInput (v, nm) = map (, Text.pack nm) <$> flattenSValue sym v
  ins <- concat <$> mapM mkInput (zip args argNames)
  edoc <- runExceptT $ exprsVerilog sym ins es "f"
  case edoc of
    Left err -> fail $ "Failed to translate to Verilog: " ++ err
    Right doc -> do
      h <- openFile path WriteMode
      hPutDoc h doc
      hPutStrLn h ""
      hClose h

writeCoreProp :: FilePath -> Prop -> TopLevel ()
writeCoreProp path t =
  do sc <- getSharedContext
     tm <- io (propToTerm sc t)
     io $ writeFile path (scWriteExternal tm)

rocqTranslationConfiguration ::
  [(Text, Text)] ->
  [Text] ->
  Rocq.TranslationConfiguration
rocqTranslationConfiguration renamings skips = Rocq.TranslationConfiguration
  { Rocq.constantRenaming = map (\(a, b) -> (Text.unpack a, Text.unpack b)) renamings
  , Rocq.constantSkips = map Text.unpack skips
  , Rocq.monadicTranslation = False
  , Rocq.postPreamble = []
  , Rocq.vectorModule = "SAWCoreVectorsAsRocqVectors"
  }

withImportSAWCorePrelude :: Rocq.TranslationConfiguration  -> Rocq.TranslationConfiguration
withImportSAWCorePrelude config@(Rocq.TranslationConfiguration { Rocq.postPreamble }) =
  config { Rocq.postPreamble = postPreamble ++ unlines
   [ "From CryptolToRocq Require Import SAWCorePrelude."
   ]
  }

withImportSAWCorePreludeExtra :: Rocq.TranslationConfiguration  -> Rocq.TranslationConfiguration
withImportSAWCorePreludeExtra config@(Rocq.TranslationConfiguration { Rocq.postPreamble }) =
  config { Rocq.postPreamble = postPreamble ++ unlines
   [ "From CryptolToRocq Require Import SAWCorePreludeExtra."
   ]
  }


withImportCryptolPrimitivesForSAWCore ::
  Rocq.TranslationConfiguration  -> Rocq.TranslationConfiguration
withImportCryptolPrimitivesForSAWCore config@(Rocq.TranslationConfiguration { Rocq.postPreamble }) =
  config { Rocq.postPreamble = postPreamble ++ unlines
   [ "From CryptolToRocq Require Import CryptolPrimitivesForSAWCore."
   ]
  }

withImportCryptolPrimitivesForSAWCoreExtra ::
  Rocq.TranslationConfiguration  -> Rocq.TranslationConfiguration
withImportCryptolPrimitivesForSAWCoreExtra config@(Rocq.TranslationConfiguration { Rocq.postPreamble }) =
  config { Rocq.postPreamble = postPreamble ++ unlines
   [ "From CryptolToRocq Require Import CryptolPrimitivesForSAWCoreExtra."
   ]
  }


writeRocqTerm ::
  Text ->
  [(Text, Text)] ->
  [Text] ->
  FilePath ->
  Term ->
  TopLevel ()
writeRocqTerm name notations skips path t = do
  let configuration =
        withImportCryptolPrimitivesForSAWCore $
        withImportSAWCorePrelude $
        rocqTranslationConfiguration notations skips
  sc <- getSharedContext
  mm <- io $ scGetModuleMap sc
  tp <- io $ scTypeOf sc t
  case Rocq.translateTermAsDeclImports configuration mm (Rocq.Ident (Text.unpack name)) t tp of
    Left err -> do
      err' <- liftIO $ Rocq.ppTranslationError sc err
      throwTopLevel $ "Error translating: " ++ Text.unpack err'
    Right doc -> io $ case path of
      ""  -> print doc
      "-" -> print doc
      _   -> writeFile path (show doc)

writeRocqProp ::
  Text ->
  [(Text, Text)] ->
  [Text] ->
  FilePath ->
  Prop ->
  TopLevel ()
writeRocqProp name notations skips path t =
  do sc <- getSharedContext
     tm <- io (propToTerm sc t)
     writeRocqTerm name notations skips path tm

leanTranslationConfiguration ::
  [(Text, Text)] ->
  [Text] ->
  Lean.TranslationConfiguration
leanTranslationConfiguration renamings skips = Lean.TranslationConfiguration
  { Lean.constantRenaming = map (\(a, b) -> (Text.unpack a, Text.unpack b)) renamings
  , Lean.constantSkips = map Text.unpack skips
  }

-- | Normalize a SAWCore 'Term' for Lean emission: iterate SAWCore's
-- 'scNormalize' to a fixed point so every unfoldable 'Constant'
-- gets expanded, not just those that trigger a beta/recursor
-- reduction at the call site.
--
-- Why iterate. A single 'scNormalize' pass only expands the
-- constants that appear at a beta/recursor redex — a 'Constant nm'
-- whose body is itself a constant application (e.g. @ecReverse =
-- finNumRec <motive> reverse@) halts after one step because the
-- unfolded body isn't re-memoized. For polymorphic Cryptol terms
-- this leaves dangling references to the Cryptol prelude. Iterating
-- lets one pass unfold 'ecReverse' and the next pass unfold
-- 'finNumRec', and so on, converging when no further unfolding
-- occurs. SAWCore non-'fix' defs form a DAG — mutual recursion
-- requires 'fix', which is 'primitive' and never unfolds — so
-- convergence is guaranteed. The iteration bound is belt-and-
-- suspenders against future changes that might violate that
-- invariant.
--
-- Unlike 'normalize_term_opaque' we do /not/ automatically include
-- the 'SAWCore.Simulator.Concrete.constMap' primitives in the
-- opaque set. Those entries mark defs whose /evaluator/
-- implementation is Haskell-native (so SAW's concrete interpreter
-- uses them instead of the SAWCore definition when executing
-- terms). For Lean translation we want the SAWCore definition
-- unfolded; there's no concrete evaluator involved.
scNormalizeForLean :: SharedContext -> [Text] -> Term -> IO Term
scNormalizeForLean sc opaque t = do
  userIdxs <- mconcat <$> traverse (SC.scResolveName sc) opaque
  derivedIdxs <- discoverNatRecReachers sc
  enumEncIdxs <- discoverEnumEncodingReachers sc
  builtinIdxs <- mconcat <$> traverse (SC.scResolveName sc) leanOpaqueBuiltins
  let opaqueSet = Set.unions
        [ derivedIdxs
        , enumEncIdxs
        , Set.fromList userIdxs
        , Set.fromList builtinIdxs ]
  let unfold nm = Set.notMember (nameIndex nm) opaqueSet
  -- Compose the literal-fold pass with scNormalize. Folding before
  -- normalization lets recognizers like ite/Either.rec see concrete
  -- Bool / Nat values produced by addNat/subNat/intLe/etc. and reduce
  -- their scrutinees in the SAME normalize iteration. The fixed-point
  -- loop then handles transitive simplifications (e.g. constant-fold
  -- exposes a beta redex, which exposes another constant-fold).
  let step term = scLiteralFold sc term >>= SC.scNormalize sc unfold
  iterateNormalizeToFixedPoint scNormalizeForLeanMaxIters step t

-- | Constant-fold Nat/Int/Bool literal applications at translation
-- time. Walks the term bottom-up and replaces specific patterns with
-- their evaluated result when all relevant arguments are concrete
-- literals. Soundness: each fold rule mirrors SAW's documented
-- semantics for the operation; a folded result is provably equal to
-- the unfolded form by SAW's evaluation rules.
--
-- Why this matters for emission: SAW emits e.g. `addNat 1 32`,
-- `subNat (subNat 33 1) 0`, `intLe (natToInt 0) (natToInt 0)`,
-- `ite Bool true t e`, all over the place — Cryptol's size
-- arithmetic, bounded comprehensions, and `! N` last-element indexing
-- generate these. Without folding, the emitted Lean is bloated and
-- has Either.rec / atWithDefault / gen-of-reverse wrappers that are
-- semantically dead but syntactically opaque to discharge tactics
-- (`bv_decide`, `simp` lemma matching, etc.).
--
-- Operations folded:
--   - Nat: addNat, subNat (saturating), mulNat, minNat, maxNat,
--     equalNat (→ Bool), ltNat (→ Bool), leNat (→ Bool), expNat,
--     pred, doubleNat, divNat, modNat (when divisor /= 0).
--   - Int: intAdd, intSub, intMul, intNeg, intLe (→ Bool),
--     intLt (→ Bool), intEq (→ Bool), natToInt (when arg is Nat lit).
--   - Bool eliminator: `ite α (true|false) t e` → t/e, and the
--     same for the iteDep wrapper. Substitutes the chosen branch
--     directly without invoking Bool#rec — that's the L-16 concern,
--     and a substitution at the SAWCore level doesn't expose the
--     recursor's case order.
scLiteralFold :: SharedContext -> Term -> IO Term
scLiteralFold sc t0 = do
  cache <- newIORef IntMap.empty
  let go :: Term -> IO Term
      go t = do
        m <- readIORef cache
        case IntMap.lookup (termIndex t) m of
          Just t' -> pure t'
          Nothing -> do
            t' <- recurse t
            t'' <- tryFold t'
            modifyIORef' cache (IntMap.insert (termIndex t) t'')
            pure t''
      recurse t = case unwrapTermF t of
        FTermF ftf -> SC.scFlatTermF sc =<< traverse go ftf
        App f x -> do
          f' <- go f
          x' <- go x
          SC.scApply sc f' x'
        -- For Lambda/Pi: do NOT recurse into the binder type. The
        -- body's free Variables carry the binder's original type;
        -- folding the binder type would change it and invalidate
        -- those Variable references (manifests as "scLambda:
        -- variable typing context mismatch"). Only fold inside the
        -- body — that's where almost all literal-level operations
        -- live anyway. Type expressions are mostly static.
        Lambda nm a b -> do
          b' <- go b
          SC.scLambda sc nm a b'
        Pi nm a b -> do
          b' <- go b
          SC.scPi sc nm a b'
        Variable {} -> pure t
        Constant {} -> pure t
      tryFold t
        -- Nat ops with both args literal Nat.
        | Just [a, b] <- asGlobalApply "Prelude.addNat" t
        , Just an <- asNat a, Just bn <- asNat b
        = SC.scNat sc (an + bn)
        | Just [a, b] <- asGlobalApply "Prelude.subNat" t
        , Just an <- asNat a, Just bn <- asNat b
        = SC.scNat sc (if an >= bn then an - bn else 0)
        | Just [a, b] <- asGlobalApply "Prelude.mulNat" t
        , Just an <- asNat a, Just bn <- asNat b
        = SC.scNat sc (an * bn)
        | Just [a, b] <- asGlobalApply "Prelude.minNat" t
        , Just an <- asNat a, Just bn <- asNat b
        = SC.scNat sc (min an bn)
        | Just [a, b] <- asGlobalApply "Prelude.maxNat" t
        , Just an <- asNat a, Just bn <- asNat b
        = SC.scNat sc (max an bn)
        | Just [a, b] <- asGlobalApply "Prelude.expNat" t
        , Just an <- asNat a, Just bn <- asNat b
        = SC.scNat sc (an ^ bn)
        | Just [a, b] <- asGlobalApply "Prelude.divNat" t
        , Just an <- asNat a, Just bn <- asNat b
        , bn /= 0
        = SC.scNat sc (an `div` bn)
        | Just [a, b] <- asGlobalApply "Prelude.modNat" t
        , Just an <- asNat a, Just bn <- asNat b
        , bn /= 0
        = SC.scNat sc (an `mod` bn)
        | Just [n] <- asGlobalApply "Prelude.pred" t
        , Just nv <- asNat n
        = SC.scNat sc (if nv == 0 then 0 else nv - 1)
        | Just [n] <- asGlobalApply "Prelude.doubleNat" t
        , Just nv <- asNat n
        = SC.scNat sc (2 * nv)
        -- Nat predicates → Bool.
        | Just [a, b] <- asGlobalApply "Prelude.equalNat" t
        , Just an <- asNat a, Just bn <- asNat b
        = SC.scBool sc (an == bn)
        | Just [a, b] <- asGlobalApply "Prelude.ltNat" t
        , Just an <- asNat a, Just bn <- asNat b
        = SC.scBool sc (an < bn)
        | Just [a, b] <- asGlobalApply "Prelude.leNat" t
        , Just an <- asNat a, Just bn <- asNat b
        = SC.scBool sc (an <= bn)
        -- Integer ops on natToInt-of-Nat-literal.
        | Just [a, b] <- asGlobalApply "Prelude.intAdd" t
        , Just ai <- asIntegerLit a, Just bi <- asIntegerLit b
        = scIntegerLit sc (ai + bi)
        | Just [a, b] <- asGlobalApply "Prelude.intSub" t
        , Just ai <- asIntegerLit a, Just bi <- asIntegerLit b
        = scIntegerLit sc (ai - bi)
        | Just [a, b] <- asGlobalApply "Prelude.intMul" t
        , Just ai <- asIntegerLit a, Just bi <- asIntegerLit b
        = scIntegerLit sc (ai * bi)
        | Just [a] <- asGlobalApply "Prelude.intNeg" t
        , Just ai <- asIntegerLit a
        = scIntegerLit sc (negate ai)
        | Just [a, b] <- asGlobalApply "Prelude.intEq" t
        , Just ai <- asIntegerLit a, Just bi <- asIntegerLit b
        = SC.scBool sc (ai == bi)
        | Just [a, b] <- asGlobalApply "Prelude.intLe" t
        , Just ai <- asIntegerLit a, Just bi <- asIntegerLit b
        = SC.scBool sc (ai <= bi)
        | Just [a, b] <- asGlobalApply "Prelude.intLt" t
        , Just ai <- asIntegerLit a, Just bi <- asIntegerLit b
        = SC.scBool sc (ai < bi)
        | Just [n] <- asGlobalApply "Prelude.intToNat" t
        , Just nv <- asIntegerLit n
        , nv >= 0
        = SC.scNat sc (fromInteger nv)
        -- ite/iteDep with a literal Bool condition: substitute the
        -- chosen branch. We keep the SAW-Prelude `Prelude.ite` /
        -- `Prelude.iteDep` opaque elsewhere (L-16) — this rule
        -- doesn't unfold the definition, just selects the right
        -- branch when the condition is concrete. No Bool#rec exposed.
        | Just [_α, b, x, _y] <- asGlobalApply "Prelude.ite" t
        , Just True <- asBool b
        = pure x
        | Just [_α, b, _x, y] <- asGlobalApply "Prelude.ite" t
        , Just False <- asBool b
        = pure y
        | Just [_p, b, x, _y] <- asGlobalApply "Prelude.iteDep" t
        , Just True <- asBool b
        = pure x
        | Just [_p, b, _x, y] <- asGlobalApply "Prelude.iteDep" t
        , Just False <- asBool b
        = pure y
        | otherwise = pure t
      -- Recognize an Integer literal expression: natToInt of a Nat
      -- literal, or intNeg of an Integer literal. Returns the
      -- represented mathematical Integer.
      asIntegerLit u
        | Just [n] <- asGlobalApply "Prelude.natToInt" u
        , Just nv <- asNat n
        = Just (toInteger nv)
        | Just [i] <- asGlobalApply "Prelude.intNeg" u
        , Just iv <- asIntegerLit i
        = Just (negate iv)
        | otherwise = Nothing
  go t0

-- | Build an Integer literal SAWCore Term from a Haskell Integer.
-- Uses `natToInt` for non-negative values and `intNeg (natToInt …)`
-- for negative — exactly the shape SAW emits for Integer constants.
scIntegerLit :: SharedContext -> Integer -> IO Term
scIntegerLit sc i
  | i >= 0    = SC.scNatToInt sc =<< SC.scNat sc (fromInteger i)
  | otherwise = do nat <- SC.scNat sc (fromInteger (- i))
                   nti <- SC.scNatToInt sc nat
                   SC.scGlobalApply sc "Prelude.intNeg" [nti]

-- | The hard cap on 'scNormalize' iterations inside
-- 'iterateNormalizeToFixedPoint'. Real workloads reach the fixed
-- point in 1-2 iterations; the cap is a safety net for translator
-- bugs or genuinely-recursive definitions the Lean backend can't
-- specialize. Pinned by L-6 of the lockdown.
scNormalizeForLeanMaxIters :: Int
scNormalizeForLeanMaxIters = 100

-- | Iterate a normaliser to a fixed point, capped at @maxIters@.
-- Equality is checked via 'termIndex' — SAWCore's hash-cons
-- guarantees that two terms with the same index are physically
-- identical. Throws via 'fail' (loud, propagates through 'TopLevel')
-- if the cap is reached without convergence.
--
-- Exposed for the L-6 lockdown smoketest, which exercises the cap
-- by passing a mock normaliser that never converges.
iterateNormalizeToFixedPoint ::
  Int -> (Term -> IO Term) -> Term -> IO Term
iterateNormalizeToFixedPoint maxIters norm t0 = loop (0 :: Int) t0
  where
    loop n current
      | n >= maxIters =
          fail $
            "scNormalizeForLean exceeded " ++ show maxIters
            ++ " iterations without reaching a fixed point; this is"
            ++ " a translator bug or a genuinely-recursive definition"
            ++ " the Lean backend can't specialize."
      | otherwise = do
          next <- norm current
          if termIndex next == termIndex current
            then pure current
            else loop (n + 1) next

-- | Walk a SAWCore 'Term' depth-first collecting every 'Constant'
-- reference's fully-qualified name. Term sharing is honoured: a
-- subterm visited via more than one path is only walked once.
--
-- Exposed so 'dumpLeanResidualPrimitives' below can show the
-- post-normalization primitive surface.
collectConstantNames :: Term -> IO (Set Text)
collectConstantNames t0 = do
  visited   <- newIORef Set.empty
  collected <- newIORef Set.empty
  let go :: Term -> IO ()
      go t = do
        seen <- readIORef visited
        let i = termIndex t
        unless (i `Set.member` seen) $ do
          modifyIORef' visited (Set.insert i)
          case unwrapTermF t of
            Constant nm ->
              modifyIORef' collected
                (Set.insert (toAbsoluteName (nameInfo nm)))
            tf -> Foldable.traverse_ go tf
  go t0
  readIORef collected

-- | Walk a 'Term' after 'scNormalizeForLean' and report which
-- SAWCore names survived. Useful when adding new Cryptol demos:
-- the surviving names are the ones that need a 'SpecialTreatment'
-- entry plus a corresponding declaration in
-- 'CryptolToLean.SAWCorePrimitives'.
--
-- Output is grouped: names already covered by 'leanOpaqueBuiltins'
-- (and therefore expected to survive) come first; the rest are
-- candidates for a new SpecialTreatment entry.
dumpLeanResidualPrimitives :: [Text] -> Term -> TopLevel ()
dumpLeanResidualPrimitives skips t = do
  sc <- getSharedContext
  io $ do
    t' <- scNormalizeForLean sc skips t
    surviving <- collectConstantNames t'
    -- Compute the 'expected' set from leanOpaqueBuiltins. We list
    -- short names there; SAWCore renders qualified names as
    -- 'Prelude::short@core' (the '@core' suffix marks the
    -- SAWCore-core namespace). Match against the basename, after
    -- stripping any '@...' suffix and module prefix.
    let basename qn =
          let stripNs = Text.takeWhile (/= '@') qn
              afterColon = Text.takeWhileEnd (/= ':') stripNs
          in afterColon
        isExpected nm = basename nm `elem` leanOpaqueBuiltins
        (expected, unexpected) =
          Set.partition isExpected surviving
    putStrLn "=== Residual SAW primitives after scNormalize ==="
    putStrLn ""
    putStrLn "## Already in leanOpaqueBuiltins (expected residuals):"
    Foldable.for_ (Set.toAscList expected) $ \n ->
      putStrLn ("  " <> Text.unpack n)
    putStrLn ""
    putStrLn "## Other surviving constants:"
    putStrLn "(these are either inductive constructors / recursors,"
    putStrLn " primitives that should be kept opaque without unfolding,"
    putStrLn " or candidates for a new SpecialTreatment + axiom.)"
    Foldable.for_ (Set.toAscList unexpected) $ \n ->
      putStrLn ("  " <> Text.unpack n)

-- | Walk the SAW Prelude's primitives (defs with no body) and
-- report which ones lack a 'SpecialTreatment' entry on the Lean
-- side. Returns @(coveredCount, missingNames)@.
--
-- A SAW primitive without a 'SpecialTreatment' entry hits the
-- 'defaultTreatmentFor' fallback in 'SAWCoreLean.SpecialTreatment',
-- which is now `UseReject` — so the runtime contract is loud. The
-- audit's role is to catch *missing entries* at SAW-init time, so
-- adding a new Prelude primitive without either a mapping or a
-- documented `reject` entry shows up as a smoketest regression
-- rather than a per-user surprise during translation.
--
-- Design principle (audit 2026-05-07): NEVER drop errors. Every
-- Prelude primitive must have an explicit treatment — `mapsTo`
-- (real mapping), `replace` (collapse to a literal/term), or
-- `reject` (deliberate refusal with a reason). There is no silent
-- fall-through: previously, primitives we deferred lived on a
-- separate `leanIntentionallyUnmappedPrimitives` allow-list that
-- suppressed only the smoketest, leaving the runtime path emitting
-- dangling Lean references. Those entries are now `reject` entries
-- in 'SAWCoreLean.SpecialTreatment.sawCorePreludeSpecialTreatmentMap'
-- with documented reasons.
auditPreludePrimitivesForLean ::
  SharedContext -> Lean.TranslationConfiguration -> IO (Int, [Text])
auditPreludePrimitivesForLean sc config = do
  mm <- scGetModuleMap sc
  let stmap = Lean.specialTreatmentMap config
      preludeMap = Map.findWithDefault Map.empty
                     (mkModuleName ["Prelude"]) stmap
      isInPrelude d = case nameInfo (defName d) of
        ModuleIdentifier i -> identModule i == mkModuleName ["Prelude"]
        _                  -> False
      isPrimitive d = case defBody d of
        Nothing -> True
        Just _  -> False
      preludePrims = filter isPrimitive (filter isInPrelude (allModuleDefs mm))
      shortName d = case nameInfo (defName d) of
        ModuleIdentifier i -> Text.pack (identName i)
        _                  -> toAbsoluteName (nameInfo (defName d))
      hasEntry d = case nameInfo (defName d) of
        ModuleIdentifier i -> Map.member (identName i) preludeMap
        _                  -> False
      mapped = filter hasEntry preludePrims
      unmapped = [ shortName d | d <- preludePrims, not (hasEntry d) ]
  pure (length mapped, unmapped)

-- | L-14 companion: audit that every entry in 'leanOpaqueBuiltins'
-- which names a SAW Prelude def has a SpecialTreatment entry. This
-- catches the 'divNat/modNat' bug class: a def is opaque-builtined
-- (body kept opaque so normalization doesn't expose it) but has no
-- SpecialTreatment mapping, so the translator emits it with its
-- raw SAW Prelude namespace — which doesn't resolve at Lean
-- elaboration time.
--
-- Only checks Prelude-namespaced entries. Cryptol-prelude or
-- Extra-module entries (e.g. @iteDep@, @streamScanl@) are handled
-- by their own SpecialTreatment routes and don't go through the
-- Prelude map.
auditOpaqueBuiltinsCoveredBySpecialTreatment ::
  SharedContext -> Lean.TranslationConfiguration -> IO [Text]
auditOpaqueBuiltinsCoveredBySpecialTreatment sc config = do
  mm <- scGetModuleMap sc
  let stmap = Lean.specialTreatmentMap config
      preludeMap = Map.findWithDefault Map.empty
                     (mkModuleName ["Prelude"]) stmap
      isInPrelude d = case nameInfo (defName d) of
        ModuleIdentifier i -> identModule i == mkModuleName ["Prelude"]
        _                  -> False
      preludeDefs = filter isInPrelude (allModuleDefs mm)
      preludeDefName d = case nameInfo (defName d) of
        ModuleIdentifier i -> Just (identName i)
        _                  -> Nothing
      preludeDefNames :: [String]
      preludeDefNames = [ n | d <- preludeDefs, Just n <- [preludeDefName d] ]
      -- Every 'leanOpaqueBuiltins' entry that IS a Prelude def but
      -- lacks a SpecialTreatment entry is a bug: translated terms
      -- referencing it will emit an unresolved name.
      missing :: [Text]
      missing =
        [ s
        | s <- leanOpaqueBuiltins
        , Text.unpack s `elem` preludeDefNames
        , not (Map.member (Text.unpack s) preludeMap)
        , Text.unpack s `notElem` leanOpaqueBuiltinsIntentionallyUnmapped ]
  pure missing

-- | Exception list for 'auditOpaqueBuiltinsCoveredBySpecialTreatment'.
--
-- Most entries in 'leanOpaqueBuiltins' are there to keep their SAW
-- Prelude bodies opaque during normalization. That's safe ONLY if
-- we also have a SpecialTreatment mapping that routes references
-- to a Lean function — otherwise the translator emits a raw SAW
-- Prelude name that doesn't resolve.
--
-- The entries below are opaque-builtined but deliberately not
-- mapped, because they're unreachable in any Cryptol-emitted
-- code. Each one either:
--   - Wraps an unsound recursor (Nat#rec, Pos#rec, ...) which
--     L-3 / L-5 already reject, so no Cryptol-emitted term can
--     route through it.
--   - Is part of SAW's `Pos` / `Z` number-theoretic bridge,
--     which Cryptol doesn't expose.
--
-- If a future demo or user-written Cryptol does reach one of
-- these, the Lean elaboration will fail with "unknown identifier
-- divNat" (or whatever) — diagnostic enough for the user to
-- realise this corner is unsupported. Adding a real mapping is
-- then a deliberate Phase 6+ extension.
leanOpaqueBuiltinsIntentionallyUnmapped :: [String]
leanOpaqueBuiltinsIntentionallyUnmapped =
  [ -- SAW Pos (positive-integer) arithmetic. Cryptol doesn't
    -- expose these; they're internal to SAW's Nat*Int bridge.
    "posInc", "posAdd", "posMul", "posCmp", "posSub", "posEq"
  , "posLe", "posLt", "posExp"
    -- SAW Z (signed-integer) bridge. Similar: internal, not
    -- Cryptol-reachable.
  , "BitM", "dblZ", "subNZ", "ZtoNat"
    -- Nat#rec wrappers. L-3 rejects direct Nat#rec use; these
    -- wrappers can only surface via parse_core or hand-constructed
    -- SAW terms, both of which are out-of-scope.
  , "Nat__rec", "Nat_cases", "Nat_cases2", "natCase", "if0Nat"
  , "AccessibleNat_all"
  ]

-- NOTE (audit 2026-05-07): a previous version of this module
-- defined `leanIntentionallyUnmappedPrimitives :: [String]` listing
-- ~40 Prelude primitives we hadn't yet mapped, and the audit above
-- subtracted those from the "missing" report. The runtime contract
-- was lossy: an "intentionally unmapped" primitive still emitted a
-- dangling `CryptolToLean.SAWCorePrelude.foo` reference that
-- Lean rejected as "unknown identifier" — silent at SAW time, loud
-- only at lake-build time. The list violated the project's "never
-- drop errors" principle: it was an allow-list for silent
-- passthrough.
--
-- Each entry is now an explicit `reject "<reason>"` SpecialTreatment
-- in 'SAWCoreLean.SpecialTreatment.sawCorePreludeSpecialTreatmentMap',
-- so the runtime path also rejects loudly at SAW-translation time
-- with a documented reason. The audit's role is unchanged: it
-- catches new Prelude additions that lack ANY treatment (mapped or
-- rejected) at SAW-init time.

-- | Walk the SAW module map at translator-startup, finding every
-- 'Def' whose body /directly/ contains a 'Recursor' over an
-- "unsound recursor" datatype: @Prelude.Nat@, @Prelude.Pos@,
-- @Prelude.Z@, @Prelude.AccessibleNat@, @Prelude.AccessiblePos@.
-- Such defs must stay opaque under 'scNormalizeForLean', because
-- if their bodies expand the inner @<DT>#rec@ would surface in
-- the translated output where the Lean side has no equivalence-
-- preserving target.
--
-- "Directly" matters: a def @f x = Succ x@ doesn't need to be
-- opaque even though it references @Succ@ which itself uses
-- @Nat#rec@, because @Succ@'s opacity already prevents the
-- recursor from surfacing during normalization. Marking @f@
-- opaque too would over-conservatively block legitimate
-- normalization — observed regressing test_arithmetic.t11 (sext)
-- when the walker recursed through 'Constant' references.
--
-- The walk memoises term subterm-indices but does NOT recurse
-- through 'Constant' references — only through structural
-- subterms (App, Lambda, Pi, FlatTermF children).
--
-- L-3 lockdown: pre-L-3, only @Nat@ and @Pos@ were detected here,
-- and the textual @leanOpaqueBuiltins@ list backstopped the
-- @Z@/@AccessibleNat@/@AccessiblePos@ cases. The textual list is
-- a hand-maintained safety net — if a future SAWCore Prelude
-- addition introduces a new def using one of those recursors,
-- the auto-derive must catch it without a manual list edit.
-- L-3 promotes all five datatypes into the auto-derived check.
discoverNatRecReachers :: SharedContext -> IO (Set VarIndex)
discoverNatRecReachers sc = do
  mm <- scGetModuleMap sc
  let preludeName = mkModuleName ["Prelude"]
      unsoundRecursorDatatypes = Set.fromList $ map (mkIdent preludeName)
        [ "Nat", "Pos", "Z", "AccessibleNat", "AccessiblePos" ]
      isTargetRecursor nm =
        case nameInfo nm of
          ModuleIdentifier i -> i `Set.member` unsoundRecursorDatatypes
          _                  -> False

  -- Walk a Term, returning whether it directly contains a target
  -- recursor. Stops at 'Constant' references (their internals are
  -- the responsibility of the referenced def's own check).
  termCache <- newIORef IntMap.empty
  let
    reachesTerm :: Term -> IO Bool
    reachesTerm t = do
      let i = termIndex t
      cache <- readIORef termCache
      case IntMap.lookup i cache of
        Just b  -> pure b
        Nothing -> do
          modifyIORef' termCache (IntMap.insert i False)
          b <- case unwrapTermF t of
                 FTermF (Recursor crec) ->
                   pure (isTargetRecursor (recursorDataType crec))
                 Constant _ ->
                   pure False  -- don't peek inside other defs
                 tf ->
                   Foldable.foldlM
                     (\acc sub -> if acc then pure True
                                          else reachesTerm sub)
                     False
                     tf
          modifyIORef' termCache (IntMap.insert i b)
          pure b

  results <- Foldable.foldlM
    (\acc d -> case defBody d of
        Just body -> do
          hit <- reachesTerm body
          if hit
            then pure (Set.insert (nameIndex (defName d)) acc)
            else pure acc
        Nothing -> pure acc)
    Set.empty
    (allModuleDefs mm)
  pure results

-- | Walk the SAW module map and find every 'Def' whose body
-- /directly/ uses 'Prelude.ListSort' or 'Prelude.FunsTo' — SAW's
-- internal encoding for Cryptol algebraic enum case-analysis. The
-- bodies of these defs use sort-1 type-level machinery that
-- 'scNormalize' doesn't handle robustly: unfolding paths through
-- 'ListSort__rec' / 'FunsTo__rec' produces lambda terms with
-- typing contexts that don't unify, triggering SAWCore's
-- 'VariableContextMismatch' check inside 'scLambda'.
--
-- Audit (2026-05-07): without this, any Cryptol module containing
-- @enum Color = Red | Green | Blue@ (or similar algebraic enum)
-- crashed @write_lean_cryptol_module@ with a SAWCore-internal
-- panic. With it, the user-elaborated enum-type defs (e.g.
-- @Color__TY@) stay opaque under normalize, and the translator
-- then sees them as Cryptol-namespace unmapped idents — triggering
-- the CG-1 'UseReject' default for a clean SAW-time diagnostic
-- ("Cryptol primitive `Color__TY` has no SAW-core-lean mapping…").
--
-- This is an ERGONOMIC gate (analogous to 'leanOpaqueBuiltins')
-- not a soundness one. The principled fix is for SAWCore /
-- 'scNormalize' to handle these encodings without the typing-context
-- panic, OR for the Lean backend to add native algebraic-enum
-- mappings (CG-5 in long-term-plan). Until then, this keeps the
-- failure surface predictable.
--
-- The walk follows 'discoverNatRecReachers' — same pattern, just a
-- different target-recursor set, no recursion through 'Constant'
-- references.
discoverEnumEncodingReachers :: SharedContext -> IO (Set VarIndex)
discoverEnumEncodingReachers sc = do
  mm <- scGetModuleMap sc
  let preludeName = mkModuleName ["Prelude"]
      enumEncodingDatatypes = Set.fromList $ map (mkIdent preludeName)
        [ "ListSort", "FunsTo" ]
      isTargetRecursor nm =
        case nameInfo nm of
          ModuleIdentifier i -> i `Set.member` enumEncodingDatatypes
          _                  -> False

  termCache <- newIORef IntMap.empty
  let
    reachesTerm :: Term -> IO Bool
    reachesTerm t = do
      let i = termIndex t
      cache <- readIORef termCache
      case IntMap.lookup i cache of
        Just b  -> pure b
        Nothing -> do
          modifyIORef' termCache (IntMap.insert i False)
          b <- case unwrapTermF t of
                 FTermF (Recursor crec) ->
                   pure (isTargetRecursor (recursorDataType crec))
                 Constant _ ->
                   pure False
                 tf ->
                   Foldable.foldlM
                     (\acc sub -> if acc then pure True
                                          else reachesTerm sub)
                     False
                     tf
          modifyIORef' termCache (IntMap.insert i b)
          pure b

  Foldable.foldlM
    (\acc d -> case defBody d of
        Just body -> do
          hit <- reachesTerm body
          if hit
            then pure (Set.insert (nameIndex (defName d)) acc)
            else pure acc
        Nothing -> pure acc)
    Set.empty
    (allModuleDefs mm)

-- | A textual list of SAW names that should stay opaque under
-- 'scNormalizeForLean' for ERGONOMIC reasons — soundness is
-- already covered post-L-3 by 'discoverNatRecReachers' (every def
-- that directly contains a recursor over Nat / Pos / Z /
-- AccessibleNat / AccessiblePos). What's left here is opacity
-- needed to keep the surface clean:
--
--   - 'bvNot' / 'bvAnd' / 'bvOr' / 'bvXor' / 'bvEq' use 'map' /
--     'bvZipWith' / 'vecEq' over Bool ops; we want them treated as
--     atomic Lean axioms instead of expanding into Vec machinery.
--   - 'Pair_fst' / 'Pair_snd' use 'Pair__rec' / 'PairType#rec';
--     we keep them opaque so the projection emits a clean axiom
--     call rather than an inline recursor application.
--   - 'ZtoNat' references 'Z_cases' (which IS auto-derived opaque
--     under L-3); without keeping 'ZtoNat' opaque too, scNormalize
--     would unfold it to a Z_cases-using surface that has no
--     direct Lean target. Soundness is unaffected — Z#rec doesn't
--     surface — but the Lean elaborator wouldn't have an entry for
--     Z_cases. Same shape for 'subNZ' and 'subNat'.
--
-- The Nat / Pos arithmetic entries (addNat, posSub, etc.) are now
-- redundant under L-3's auto-derive — kept as a documented
-- sentinel so a refactor that loses the auto-derive doesn't
-- silently regress. The L-3 smoketest pins their auto-derived
-- inclusion.
leanOpaqueBuiltins :: [Text]
leanOpaqueBuiltins =
  [ -- Constructors/wrappers whose bodies use Nat#rec internally
    "Succ"
    -- Pos operations (body: Pos#rec or recursive over Pos)
  , "posInc"
  , "posAdd"
  , "posMul"
  , "posCmp"
  , "posSub"
  , "posEq"
  , "posLe"
  , "posLt"
  , "posExp"
  , "BitM"
  , "dblZ"
    -- Z bridge
  , "subNZ"
  , "ZtoNat"
    -- Nat arithmetic (body: Nat#rec)
  , "addNat"
  , "subNat"
  , "mulNat"
  , "divNat"
  , "modNat"
  , "divModNat"
  , "expNat"
  , "widthNat"
  , "doubleNat"
  , "equalNat"
  , "leNat"
  , "ltNat"
  , "minNat"
  , "maxNat"
  , "pred"
    -- Nat case/rec wrappers
  , "Nat__rec"
  , "Nat_cases"
  , "Nat_cases2"
  , "natCase"
  , "if0Nat"
  , "AccessibleNat_all"
    -- Bitvector defs whose body uses 'map' / 'bvZipWith' / 'vecEq'
    -- over individual Bool ops; we provide top-level axioms for
    -- them in CryptolToLean.SAWCorePrimitives, so unfolding into
    -- the Bool-level Vec machinery is exactly what we want to
    -- prevent.
  , "bvNot"
  , "bvAnd"
  , "bvOr"
  , "bvXor"
  , "bvEq"
    -- Pair projection defs whose body uses Pair__rec / PairType#rec
  , "Pair_fst"
  , "Pair_snd"
    -- L-16: Bool eliminator wrappers. SAW's Bool#rec arg order is
    -- (motive, trueCase, falseCase, scrutinee) — True first, since
    -- SAW's Bool data declaration is 'True; False;'. Lean's
    -- auto-generated Bool.rec is the opposite (False first). The
    -- handwritten 'iteDep' / 'ite' / etc. in
    -- 'CryptolToLean.SAWCorePreludeExtra' permute the args, so a
    -- SpecialTreatment-routed reference is correct. But if
    -- scNormalize unfolds these defs (their bodies use Bool#rec1
    -- with SAW's True-first order), the surface contains a bare
    -- 'Bool#rec' that the translator emits as '@Bool.rec' with
    -- args in SAW order — and Lean reads them in its order,
    -- silently swapping the cases. Keep the wrappers opaque so
    -- the surface stays at the wrapper level and routes through
    -- the correct permutation. Pinned by L-16 regression test.
  , "iteDep", "ite", "iteDep_True", "iteDep_False"
    -- Phase 5c / Slice C: streamScanl is the only SAW Prelude def
    -- that uses Prelude.fix in its body (line ~2077 of
    -- Prelude.sawcore). Phase 5's StreamCorec recognizer would
    -- match the unfolded shape, but routing each use through a
    -- per-call mkStreamFix expansion is verbose; keeping the def
    -- opaque and routing via the handwritten Lean equivalent in
    -- SAWCorePreludeExtra (with rfl-proven streamScanl_zero /
    -- streamScanl_succ lemmas) mirrors Rocq's approach and gives
    -- downstream proofs a named target.
  , "streamScanl"
    -- not / and / or / xor / boolEq defs use ite internally; once
    -- ite is opaque (above), these unfold one step to ite and stop
    -- there, routing via the SpecialTreatment ite mapping to our
    -- handwritten Lean wrapper. So they don't need to be opaque
    -- themselves — the chain stops at ite.
  ]

-- Helper: write a file, creating parent directories as needed. The
-- @write_lean_*@ commands accept paths like @out/Foo.lean@ where the
-- caller hasn't created @out/@ yet; without this, plain @writeFile@
-- raises an unhelpful "does not exist" IOException buried in saw's
-- output. Mirrors the user expectation set by @mkdir -p@-style CLIs.
writeLeanFile :: FilePath -> String -> IO ()
writeLeanFile path contents = do
  createDirectoryIfMissing True (takeDirectory path)
  writeFile path contents

writeLeanTerm ::
  Text ->
  [(Text, Text)] ->
  [Text] ->
  FilePath ->
  Term ->
  TopLevel ()
writeLeanTerm name notations skips path t = do
  let configuration = leanTranslationConfiguration notations skips
  sc <- getSharedContext
  mm <- io $ scGetModuleMap sc
  t' <- io $ scNormalizeForLean sc skips t
  tp <- io $ scTypeOf sc t'
  case Lean.translateTermAsDeclImports configuration mm (Lean.Ident (Text.unpack name)) t' tp of
    Left err -> do
      err' <- liftIO $ Lean.ppTranslationError sc err
      throwTopLevel $ "Error translating: " ++ Text.unpack err'
    Right doc -> io $ case path of
      ""  -> print doc
      "-" -> print doc
      _   -> writeLeanFile path (show doc)

writeLeanProp ::
  Text ->
  [(Text, Text)] ->
  [Text] ->
  FilePath ->
  Prop ->
  TopLevel ()
writeLeanProp name notations skips path t = do
  let configuration = leanTranslationConfiguration notations skips
  sc <- getSharedContext
  mm <- io $ scGetModuleMap sc
  tmRaw <- io (propToTerm sc t)
  -- Goals from `llvm_verify` (and other Crucible-driven verification
  -- entry points) carry free SAWCore Variables — the symbolic inputs
  -- introduced by `llvm_fresh_var` etc. Without abstraction, the
  -- saw-core-lean translator hits LocalVarOutOfBounds because the
  -- variable references aren't bound by any Pi in scope. Abstract
  -- them into outer Pi binders so the translator sees a closed term.
  -- Goals from `prove_print` over a closed Cryptol lambda have no
  -- free variables, so this is a no-op for that path.
  tm <- io $ do
          let frees = SC.getAllVars tmRaw
          if null frees
            then pure tmRaw
            else SC.scPiList sc frees tmRaw
  tm' <- io $ scNormalizeForLean sc skips tm
  tp  <- io $ scTypeOf sc tm'
  case Lean.translateGoalAsDeclImports configuration mm (Lean.Ident (Text.unpack name)) tm' tp of
    Left err -> do
      err' <- liftIO $ Lean.ppTranslationError sc err
      throwTopLevel $ "Error translating: " ++ Text.unpack err'
    Right doc -> io $ case path of
      ""  -> print doc
      "-" -> print doc
      _   -> writeLeanFile path (show doc)

-- | Translate a Cryptol source file to a Lean 4 file. Mirrors
-- 'writeRocqCryptolModule'. Loads both SAW preludes into a fresh
-- context, loads the user's .cry file, and walks the resulting
-- 'CryptolModule'. The translated defs land inside a
-- @namespace <basename> … end <basename>@ block.
writeLeanCryptolModule ::
  FilePath ->            -- ^ path to the @.cry@ file
  FilePath ->            -- ^ path to write the Lean output to
  [(Text, Text)] ->      -- ^ notation substitutions
  [Text] ->              -- ^ identifiers to skip
  TopLevel ()
writeLeanCryptolModule inputFile outputFile notations skips = do
  sc <- io mkSharedContext
  () <- io $ scLoadPreludeModule sc
  () <- io $ scLoadCryptolModule sc
  let ?fileReader = BS.readFile
  env <- io $ initCryptolEnv sc
  cryptolPrimitivesForSAWCoreModule <-
    io $ scFindModule sc nameOfCryptolPrimitivesForSAWCoreModule
  (cm, _) <- io $ loadCryptolModule sc env inputFile
  import_env <- io $ refreshCryptolEnv env
  mm <- io $ scGetModuleMap sc
  let ?mm = mm
  let cryptolPreludeDecls =
        map Lean.Ident $
        mapMaybe Lean.moduleDeclName
          (moduleDecls cryptolPrimitivesForSAWCoreModule)
  let configuration = leanTranslationConfiguration notations skips
  let nm = Lean.Ident (takeBaseName inputFile)
  let normalize = scNormalizeForLean sc skips
  res <- io $ Lean.translateCryptolModule sc import_env nm configuration
           normalize cryptolPreludeDecls cm
  -- Audit M-3 (2026-05-06): translator failures must propagate via
  -- @throwTopLevel@ (consistent with @writeLeanTerm@ /
  -- @writeLeanProp@). The previous code just printed the error and
  -- returned successfully, so a downstream @lake build@ would
  -- elaborate against a missing or stale output and report
  -- "success" to the user.
  case res of
    Left err -> do
      err' <- io $ Lean.ppTranslationError sc err
      throwTopLevel $ "Error translating Cryptol module: " ++ Text.unpack err'
    Right cmDoc -> io $ do
      let doc = vcat [ Lean.preamble False configuration, cmDoc ]
      case outputFile of
        ""  -> print doc
        "-" -> print doc
        _   -> writeLeanFile outputFile (show doc)

-- | Write out a representation of a Cryptol module in Gallina syntax for Rocq.
writeRocqCryptolModule ::
  -- | Path to module to export
  FilePath ->
  -- | Path for output Rocq file
  FilePath ->
  -- | Pairs of notation substitutions: operator on the left will be replaced
  -- with the identifier on the right
  [(Text, Text)] ->
  -- | List of identifiers to skip during translation
  [Text] ->
  TopLevel ()
writeRocqCryptolModule inputFile outputFile notations skips = io $ do
  sc  <- mkSharedContext
  ()  <- scLoadPreludeModule sc
  ()  <- scLoadCryptolModule sc
  let ?fileReader = BS.readFile
  env <- initCryptolEnv sc
  cryptolPrimitivesForSAWCoreModule <- scFindModule sc nameOfCryptolPrimitivesForSAWCoreModule
  (cm, _) <- loadCryptolModule sc env inputFile
               -- NOTE: implementation of loadCryptolModule, now uses this default:
               --   defaultPrimitiveOptions = ImportPrimitiveOptions{allowUnknownPrimitives=True}
  import_env <- refreshCryptolEnv env
  mm <- scGetModuleMap sc
  let ?mm = mm
  let cryptolPreludeDecls =
        map Rocq.Ident $
        mapMaybe Rocq.moduleDeclName (moduleDecls cryptolPrimitivesForSAWCoreModule)
  let configuration =
        withImportCryptolPrimitivesForSAWCoreExtra $
        withImportCryptolPrimitivesForSAWCore $
        withImportSAWCorePreludeExtra $
        withImportSAWCorePrelude $
        rocqTranslationConfiguration notations skips
  let nm = Rocq.Ident (takeBaseName inputFile)
  res <- Rocq.translateCryptolModule sc import_env nm configuration cryptolPreludeDecls cm
  case res of
    Left err -> do
      err' <- Rocq.ppTranslationError sc err
      putStrLn $ Text.unpack err'
    Right cmDoc -> do
      let doc = vcat [ Rocq.preamble configuration, cmDoc ]
      case outputFile of
        ""  -> print doc
        "-" -> print doc
        _   -> writeFile outputFile $ show doc

nameOfSAWCorePrelude :: Un.ModuleName
nameOfSAWCorePrelude = Un.moduleName preludeModule

nameOfCryptolPrimitivesForSAWCoreModule :: Un.ModuleName
nameOfCryptolPrimitivesForSAWCoreModule = Un.moduleName cryptolModule

writeRocqSAWCorePrelude ::
  FilePath ->
  [(Text, Text)] ->
  [Text] ->
  IO ()
writeRocqSAWCorePrelude outputFile notations skips = do
  sc  <- mkSharedContext
  ()  <- scLoadPreludeModule sc
  mm  <- scGetModuleMap sc
  m   <- scFindModule sc nameOfSAWCorePrelude
  let configuration = rocqTranslationConfiguration notations skips
  m'  <- Rocq.translateSAWModule sc configuration mm m
  let doc = vcat [ Rocq.preamble configuration, m']
  case outputFile of
    ""  -> print doc
    "-" -> print doc
    _   -> writeFile outputFile $ show doc

-- | Auto-emit the SAWCore Prelude module as a Lean file. Each
-- 'ModuleDecl' is dispatched per its 'atDefSite' treatment in
-- 'SAWCoreLean.SpecialTreatment': mappings to the hand-written
-- support library emit a one-line comment; auto-emitted entries
-- run through 'translateDef' / 'translateDataType' using Phase 2's
-- universe machinery; opt-in 'realize'-style replacements emit
-- verbatim Lean source.
writeLeanSAWCorePrelude ::
  FilePath ->
  [(Text, Text)] ->
  [Text] ->
  IO ()
writeLeanSAWCorePrelude outputFile notations skips = do
  sc  <- mkSharedContext
  ()  <- scLoadPreludeModule sc
  mm  <- scGetModuleMap sc
  m   <- scFindModule sc nameOfSAWCorePrelude
  let configuration = leanTranslationConfiguration notations skips
  m'  <- Lean.translateSAWModule sc configuration mm m
  let doc = vcat [ Lean.preamble False configuration, m' ]
  case outputFile of
    ""  -> print doc
    "-" -> print doc
    _   -> writeLeanFile outputFile (show doc)

writeRocqCryptolPrimitivesForSAWCore ::
  FilePath ->
  [(Text, Text)] ->
  [Text] ->
  IO ()
writeRocqCryptolPrimitivesForSAWCore cryFile notations skips = do
  sc <- mkSharedContext
  () <- scLoadPreludeModule sc
  () <- scLoadCryptolModule sc
  () <- scLoadModule sc (emptyModule (mkModuleName ["CryptolPrimitivesForSAWCore"]))
  m  <- scFindModule sc nameOfCryptolPrimitivesForSAWCoreModule
  mm <- scGetModuleMap sc
  let configuration =
        withImportSAWCorePreludeExtra $
        withImportSAWCorePrelude $
        rocqTranslationConfiguration notations skips
  m' <- Rocq.translateSAWModule sc configuration mm m 
  let doc = vcat [ Rocq.preamble configuration, m']
  case cryFile of
    ""  -> print doc
    "-" -> print doc
    _   -> writeFile cryFile $ show doc

-- | Auto-emit cryptol-saw-core's Cryptol.sawcore module as a Lean file.
-- Mirrors 'writeRocqCryptolPrimitivesForSAWCore' using the Lean SAW-module
-- walker and the checked Lean support-library preamble.
writeLeanCryptolPrimitivesForSAWCore ::
  FilePath ->
  [(Text, Text)] ->
  [Text] ->
  IO ()
writeLeanCryptolPrimitivesForSAWCore outputFile notations skips = do
  sc <- mkSharedContext
  () <- scLoadPreludeModule sc
  () <- scLoadCryptolModule sc
  () <- scLoadModule sc (emptyModule (mkModuleName ["CryptolPrimitivesForSAWCore"]))
  m  <- scFindModule sc nameOfCryptolPrimitivesForSAWCoreModule
  mm <- scGetModuleMap sc
  let configuration = leanTranslationConfiguration notations skips
  m' <- Lean.translateSAWModule sc configuration mm m
  let doc = vcat [ Lean.preamble False configuration, m' ]
  case outputFile of
    ""  -> print doc
    "-" -> print doc
    _   -> writeLeanFile outputFile (show doc)

-- | Tranlsate a SAWCore term into an AIG
bitblastPrim :: (AIG.IsAIG l g) => AIG.Proxy l g -> SharedContext -> Term -> IO (AIG.Network l g)
bitblastPrim proxy sc t = do
{-
  let s = ttSchema t'
  case s of
    C.Forall [] [] _ -> return ()
    _ -> fail $ "Attempting to bitblast a term with a polymorphic type: " ++ pretty s
-}
  BBSim.withBitBlastedTerm proxy sc mempty t $ \be ls -> do
    return (AIG.Network be (toList ls))
