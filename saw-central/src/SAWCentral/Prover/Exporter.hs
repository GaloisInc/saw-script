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
  , writeRocqCryptolModule
  , writeRocqSAWCorePrelude
  , writeRocqTerm
  , rocqTranslationConfiguration
  , writeRocqProp
  , writeLeanTerm
  , leanTranslationConfiguration
  , writeLeanProp
  , writeLeanCryptolModule
  , dumpLeanResidualPrimitives
  , iterateNormalizeToFixedPoint
  , polymorphismResidual
  , scNormalizeForLeanMaxIters
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
import System.Directory (removeFile)
import System.FilePath (takeBaseName)
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
                     toAbsoluteName)
import SAWCore.Term.Functor (FlatTermF(..), recursorDataType)
import SAWCore.Recognizer (asPi)
import SAWCore.Term.Functor (Sort(TypeSort))
import SAWCore.Prelude (preludeModule)
import SAWCore.SATQuery
import SAWCore.SharedTerm as SC

import CryptolSAWCore.Cryptol (refreshCryptolEnv)
import qualified Cryptol.ModuleSystem.Name as Cryptol
import qualified Cryptol.Utils.Ident as Cryptol
import CryptolSAWCore.CryptolEnv (initCryptolEnv, loadCryptolModule)
import CryptolSAWCore.Prelude (cryptolModule, scLoadPreludeModule, scLoadCryptolModule)
import CryptolSAWCore.TypedTerm

import qualified SAWCoreRocq.Rocq as Rocq
import qualified Language.Rocq.AST as Rocq
import qualified SAWCoreLean.Lean as Lean
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
  builtinIdxs <- mconcat <$> traverse (SC.scResolveName sc) leanOpaqueBuiltins
  let opaqueSet = Set.unions
        [ derivedIdxs
        , Set.fromList userIdxs
        , Set.fromList builtinIdxs ]
  let unfold nm = Set.notMember (nameIndex nm) opaqueSet
  iterateNormalizeToFixedPoint scNormalizeForLeanMaxIters
                               (SC.scNormalize sc unfold)
                               t

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

-- | Walk the SAW module map at translator-startup, finding every
-- 'Def' whose body /directly/ contains a 'Recursor' over
-- @Prelude.Nat@ or @Prelude.Pos@. Such defs must stay opaque under
-- 'scNormalizeForLean', because if their bodies expand the inner
-- 'Nat#rec' / 'Pos#rec' would surface and trip the
-- 'UnsoundRecursor' guard in 'SAWCoreLean.Term'.
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
discoverNatRecReachers :: SharedContext -> IO (Set VarIndex)
discoverNatRecReachers sc = do
  mm <- scGetModuleMap sc
  let preludeNat = mkIdent (mkModuleName ["Prelude"]) "Nat"
      preludePos = mkIdent (mkModuleName ["Prelude"]) "Pos"
      isTargetRecursor nm =
        case nameInfo nm of
          ModuleIdentifier i -> i == preludeNat || i == preludePos
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

-- | A textual safety-net for SAW names that should stay opaque
-- under 'scNormalizeForLean'. Most of these are also covered by
-- the auto-derived 'discoverNatRecReachers' (every def that
-- directly contains 'Nat#rec' / 'Pos#rec'); the list also keeps
-- a backstop for adjacent reductions:
--
--   - 'subNat' / 'subNZ' / 'ZtoNat' surface 'Z#rec' when unfolded
--     ('Z' is a separate SAWCore inductive). The auto-derive only
--     looks for Nat/Pos, so we list these explicitly.
--   - 'bvNot' / 'bvAnd' / 'bvOr' / 'bvXor' / 'bvEq' use 'map' /
--     'bvZipWith' / 'vecEq' over Bool ops; we want them treated as
--     atomic Lean axioms instead of expanding into Vec machinery.
--   - 'Pair_fst' / 'Pair_snd' use 'Pair__rec' / 'PairType#rec';
--     we keep them opaque so the projection emits a clean axiom
--     call rather than an inline recursor application.
--
-- Most of the Nat / Pos arithmetic entries are redundant under
-- the auto-derive; we leave them as a documented sentinel so that
-- a refactor that loses the auto-derive doesn't silently regress.
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
  ]

-- | After normalization, refuse terms whose type binds a universe
-- strictly above @sort 0@. Ordinary type-polymorphic binders
-- (@sort 0 → ...@, corresponding to Cryptol @{a}@ over types) are
-- fine: Lean treats them as plain @Type@-valued parameters and
-- there's no cross-universe unification for us to resolve.
-- Universe-polymorphic binders (@sort k@ for @k ≥ 1@) would need
-- the P4/P6 machinery we've parked — decision D3 in
-- 'doc/2026-04-23_stage3-translator-sketch.md'.
-- Returns @Just msg@ explaining the refusal, or 'Nothing' if the
-- type only binds @Type 0@ / non-sort parameters.
--
-- L-1 lockdown: the walk is full-tree, not just the outer pi-spine.
-- A nested binder like @(f : (α : sort 1) → β) → γ@ has its
-- @sort 1@ inside an argument type — `asPiList` would step right
-- past it. We memoise on `termIndex` to keep the cost linear in the
-- shared-DAG size of the type term.
polymorphismResidual :: Term -> IO (Maybe String)
polymorphismResidual tp = do
  visited <- newIORef Set.empty
  collected <- newIORef ([] :: [String])
  let go :: Term -> IO ()
      go t = do
        seen <- readIORef visited
        let i = termIndex t
        unless (i `Set.member` seen) $ do
          modifyIORef' visited (Set.insert i)
          case unwrapTermF t of
            Pi nm a b -> do
              case asSort a of
                Just (TypeSort k) | k > 0 ->
                  modifyIORef' collected
                    ((Text.unpack (vnName nm) ++ " : sort " ++ show k) :)
                _ -> pure ()
              go a
              go b
            tf -> Foldable.traverse_ go tf
  go tp
  bad <- reverse <$> readIORef collected
  pure $ case bad of
    [] -> Nothing
    _  -> Just $
      "Refusing to translate a term that binds a universe strictly above "
      ++ "Type 0 after normalization. Lean's specialization backend "
      ++ "handles Type 0 polymorphism but not universe polymorphism (see "
      ++ "doc/2026-04-23_stage3-translator-sketch.md D3). "
      ++ "Problematic binders: " ++ show bad

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
  mResidual <- io (polymorphismResidual tp)
  case mResidual of
    Just msg -> throwTopLevel msg
    Nothing  -> pure ()
  case Lean.translateTermAsDeclImports configuration mm (Lean.Ident (Text.unpack name)) t' tp of
    Left err -> do
      err' <- liftIO $ Lean.ppTranslationError sc err
      throwTopLevel $ "Error translating: " ++ Text.unpack err'
    Right doc -> io $ case path of
      ""  -> print doc
      "-" -> print doc
      _   -> writeFile path (show doc)

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
  tm  <- io (propToTerm sc t)
  tm' <- io $ scNormalizeForLean sc skips tm
  tp  <- io $ scTypeOf sc tm'
  mResidual <- io (polymorphismResidual tp)
  case mResidual of
    Just msg -> throwTopLevel msg
    Nothing  -> pure ()
  case Lean.translateGoalAsDeclImports configuration mm (Lean.Ident (Text.unpack name)) tm' tp of
    Left err -> do
      err' <- liftIO $ Lean.ppTranslationError sc err
      throwTopLevel $ "Error translating: " ++ Text.unpack err'
    Right doc -> io $ case path of
      ""  -> print doc
      "-" -> print doc
      _   -> writeFile path (show doc)

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
  (cm@(CryptolModule _ tm), _) <- io $ loadCryptolModule sc env inputFile
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
  -- L-12 lockdown. writeLeanTerm and writeLeanProp gate every
  -- emitted term through polymorphismResidual; the module-walk
  -- path historically didn't, so a Cryptol module containing a
  -- universe-polymorphic def would skip the gate at SAW time and
  -- surface the divergence only at Lean elaboration. Run the
  -- same check on each Cryptol def's normalized type before
  -- translation. Fail loud at the first offender — surfacing
  -- the offending name in the diagnostic.
  io $ Foldable.forM_ (Map.toList tm) $ \(cname, ttm) -> do
    tp     <- ttTypeAsTerm sc import_env ttm
    tpNorm <- normalize tp
    res    <- polymorphismResidual tpNorm
    case res of
      Just msg ->
        fail $ "Cryptol def " ++ show (Cryptol.unpackIdent (Cryptol.nameIdent cname))
               ++ " in " ++ inputFile ++ ": " ++ msg
      Nothing -> pure ()
  res <- io $ Lean.translateCryptolModule sc import_env nm configuration
           normalize cryptolPreludeDecls cm
  io $ case res of
    Left err -> do
      err' <- Lean.ppTranslationError sc err
      putStrLn (Text.unpack err')
    Right cmDoc -> do
      let doc = vcat [ Lean.preamble configuration, cmDoc ]
      case outputFile of
        ""  -> print doc
        "-" -> print doc
        _   -> writeFile outputFile (show doc)

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
