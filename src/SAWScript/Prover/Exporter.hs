{-# Language GADTs #-}
{-# Language ImplicitParams #-}
{-# Language OverloadedStrings #-}
{-# Language ViewPatterns #-}
{-# Language ExplicitForAll #-}
{-# Language FlexibleContexts #-}
{-# Language TypeApplications #-}
module SAWScript.Prover.Exporter
  ( proveWithSATExporter
  , proveWithPropExporter

    -- * External formats
  , writeAIG
  , writeAIG_SAT
  , writeSAIG
  , writeSAIGInferLatches
  , writeAIGComputedLatches
  , writeCNF
  , write_cnf
  , writeSMTLib2
  , writeSMTLib2What4
  , write_smtlib2
  , write_smtlib2_w4
  , writeCoqCryptolPrimitivesForSAWCore
  , writeCoqCryptolModule
  , writeCoqSAWCorePrelude
  , writeCoqTerm
  , writeCoqProp
  , writeCore
  , writeVerilog
  , writeVerilogSAT
  , write_verilog
  , writeCoreProp

    -- * Misc
  , bitblastPrim
  ) where

import Data.Foldable(toList)

import Control.Monad.Except (runExceptT, throwError)
import Control.Monad.IO.Class (liftIO)
import qualified Data.AIG as AIG
import qualified Data.ByteString as BS
import Data.Parameterized.Nonce (globalNonceGenerator)
import Data.Set (Set)
import qualified Data.SBV.Dynamic as SBV
import System.IO
import Data.Text.Prettyprint.Doc.Render.Text
import Prettyprinter (vcat)

import Cryptol.Utils.PP(pretty)

import Verifier.SAW.CryptolEnv (initCryptolEnv, loadCryptolModule)
import Verifier.SAW.Cryptol.Prelude (cryptolModule, scLoadPreludeModule, scLoadCryptolModule)
import Verifier.SAW.ExternalFormat(scWriteExternal)
import Verifier.SAW.FiniteValue
import Verifier.SAW.Module (emptyModule, moduleDecls)
import Verifier.SAW.Prelude (preludeModule)
import Verifier.SAW.Recognizer (asPi)
import Verifier.SAW.SATQuery
import Verifier.SAW.SharedTerm as SC
import qualified Verifier.SAW.Translation.Coq as Coq
import Verifier.SAW.TypedAST (mkModuleName)
import Verifier.SAW.TypedTerm
import qualified Verifier.SAW.Simulator.BitBlast as BBSim
import qualified Verifier.SAW.Simulator.Value as Sim
import qualified Verifier.SAW.Simulator.What4 as W4Sim
import qualified Verifier.SAW.Simulator.SBV as SBV
import qualified Verifier.SAW.Simulator.What4 as W

import qualified Verifier.SAW.UntypedAST as Un

import SAWScript.Crucible.Common
import SAWScript.Proof (Prop, propSize, propToTerm, predicateToSATQuery, propToSATQuery)
import SAWScript.Prover.SolverStats
import SAWScript.Prover.Util
import SAWScript.Prover.What4
import SAWScript.Value

import qualified What4.Expr.Builder as W4
import What4.Protocol.SMTLib2 (writeDefaultSMT2)
import What4.Protocol.VerilogWriter (exprVerilog)
import What4.Solver.Adapter
import qualified What4.SWord as W4Sim

proveWithSATExporter ::
  (SharedContext -> FilePath -> SATQuery -> TopLevel ()) ->
  Set VarIndex ->
  String ->
  Prop ->
  TopLevel SolverStats
proveWithSATExporter exporter unintSet path goal =
  do sc <- getSharedContext
     satq <- io $ propToSATQuery sc unintSet goal
     exporter sc path satq
     let stats = solverStats ("offline: "++ path) (propSize goal)
     return stats


proveWithPropExporter ::
  (SharedContext -> FilePath -> Prop -> TopLevel ()) ->
  String ->
  Prop ->
  TopLevel SolverStats
proveWithPropExporter exporter path goal =
  do sc <- getSharedContext
     exporter sc path goal
     let stats = solverStats ("offline: "++ path) (propSize goal)
     return stats

--------------------------------------------------------------------------------

writeAIG_SAT :: (AIG.IsAIG l g) => AIG.Proxy l g -> SharedContext -> FilePath -> SATQuery -> TopLevel ()
writeAIG_SAT proxy sc f satq = io $
  do t  <- satQueryAsTerm sc satq
     BBSim.withBitBlastedPred proxy sc mempty t $ \g l _vars -> do
       AIG.writeAiger f (AIG.Network g [l])

-- | Write a @Term@ representing a an arbitrary function to an AIG file.
writeAIG :: (AIG.IsAIG l g) => AIG.Proxy l g -> SharedContext -> FilePath -> Term -> TopLevel ()
writeAIG proxy sc f t = do
  io $ do
    aig <- bitblastPrim proxy sc t
    AIG.writeAiger f aig

-- | Like @writeAIG@, but takes an additional 'Integer' argument
-- specifying the number of input and output bits to be interpreted as
-- latches. Used to implement more friendly SAIG writers
-- @writeSAIGInferLatches@ and @writeSAIGComputedLatches@.
writeSAIG :: (AIG.IsAIG l g) => AIG.Proxy l g -> SharedContext -> FilePath -> Term -> Int -> TopLevel ()
writeSAIG proxy sc file tt numLatches = do
  liftIO $ do
    aig <- bitblastPrim proxy sc tt
    AIG.writeAigerWithLatches file aig numLatches

-- | Given a term a type '(i, s) -> (o, s)', call @writeSAIG@ on term
-- with latch bits set to '|s|', the width of 's'.
writeSAIGInferLatches :: (AIG.IsAIG l g) => AIG.Proxy l g -> SharedContext -> FilePath -> TypedTerm -> TopLevel ()
writeSAIGInferLatches proxy sc file tt = do
  ty <- io $ scTypeOf sc (ttTerm tt)
  s <- getStateType ty
  let numLatches = sizeFiniteType s
  writeSAIG proxy sc file (ttTerm tt) numLatches
  where
    die :: String -> TopLevel a
    die why = throwTopLevel $
      "writeSAIGInferLatches: " ++ why ++ ":\n" ++
      "term must have type of the form '(i, s) -> (o, s)',\n" ++
      "where 'i', 's', and 'o' are all fixed-width types,\n" ++
      "but type of term is:\n" ++ (pretty . ttSchema $ tt)

    -- Decompose type as '(i, s) -> (o, s)' and return 's'.
    getStateType :: Term -> TopLevel FiniteType
    getStateType ty = do
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
writeAIGComputedLatches ::
  (AIG.IsAIG l g) => AIG.Proxy l g -> SharedContext -> FilePath -> Term -> Int -> TopLevel ()
writeAIGComputedLatches proxy sc file term numLatches =
  writeSAIG proxy sc file term numLatches

writeCNF :: (AIG.IsAIG l g) => AIG.Proxy l g -> SharedContext -> FilePath -> SATQuery -> TopLevel ()
writeCNF proxy sc f satq = io $
  do t  <- satQueryAsTerm sc satq
     _ <- BBSim.withBitBlastedPred proxy sc mempty t $ \g l _vars -> AIG.writeCNF g l f
     return ()

write_cnf :: SharedContext -> FilePath -> TypedTerm -> TopLevel ()
write_cnf sc f (TypedTerm schema t) = do
  liftIO $ checkBooleanSchema schema
  AIGProxy proxy <- getProxy
  satq <- io (predicateToSATQuery sc mempty t)
  writeCNF proxy sc f satq

-- | Write a @Term@ representing a predicate (i.e. a monomorphic
-- function returning a boolean) to an SMT-Lib version 2 file. The goal
-- is to pass the term through as directly as possible, so we interpret
-- it as an existential.
write_smtlib2 :: SharedContext -> FilePath -> TypedTerm -> TopLevel ()
write_smtlib2 sc f (TypedTerm schema t) = do
  io $ checkBooleanSchema schema
  satq <- io $ predicateToSATQuery sc mempty t
  writeSMTLib2 sc f satq

-- | Write a @Term@ representing a predicate (i.e. a monomorphic
-- function returning a boolean) to an SMT-Lib version 2 file. The goal
-- is to pass the term through as directly as possible, so we interpret
-- it as an existential. This version uses What4 instead of SBV.
write_smtlib2_w4 :: SharedContext -> FilePath -> TypedTerm -> TopLevel ()
write_smtlib2_w4 sc f (TypedTerm schema t) = do
  io $ checkBooleanSchema schema
  satq <- io $ predicateToSATQuery sc mempty t
  writeSMTLib2What4 sc f satq

-- | Write a SAT query to an SMT-Lib version 2 file.
writeSMTLib2 :: SharedContext -> FilePath -> SATQuery -> TopLevel ()
writeSMTLib2 sc f satq = io $
  do (_, _, l) <- SBV.sbvSATQuery sc mempty satq
     let isSat = True -- l is encoded as an existential formula
     txt <- SBV.generateSMTBenchmark isSat l
     writeFile f txt

-- | Write a SAT query an SMT-Lib version 2 file.
-- This version uses What4 instead of SBV.
writeSMTLib2What4 :: SharedContext -> FilePath -> SATQuery -> TopLevel ()
writeSMTLib2What4 sc f satq = io $
  do sym <- W4.newExprBuilder W4.FloatRealRepr St globalNonceGenerator
     (_argNames, _labels, lit) <- W.w4Solve sym sc satq
     withFile f WriteMode $ \h ->
       writeDefaultSMT2 () "Offline SMTLib2" defaultWriteSMTLIB2Features sym h [lit]

writeCore :: FilePath -> Term -> TopLevel ()
writeCore path t = io $ writeFile path (scWriteExternal t)

write_verilog :: SharedContext -> FilePath -> Term -> TopLevel ()
write_verilog sc path t = io $ writeVerilog sc path t

writeVerilogSAT :: SharedContext -> FilePath -> SATQuery -> TopLevel ()
writeVerilogSAT sc path satq = io $
  do t <- satQueryAsTerm sc satq
     writeVerilog sc path t

writeVerilog :: SharedContext -> FilePath -> Term -> IO ()
writeVerilog sc path t = do
  sym <- newSAWCoreBackend sc
  st  <- sawCoreState sym
  (_, (_, bval)) <- W4Sim.w4EvalAny sym st sc mempty mempty t
  edoc <- runExceptT $
    case bval of
      Sim.VBool b -> exprVerilog sym b "f"
      Sim.VWord (W4Sim.DBV w) -> exprVerilog sym w "f"
      _ -> throwError $ "write_verilog: unsupported result type: " ++ show bval
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

coqTranslationConfiguration ::
  [(String, String)] ->
  [String] ->
  Coq.TranslationConfiguration
coqTranslationConfiguration notations skips = Coq.TranslationConfiguration
  { Coq.notations          = notations
  , Coq.monadicTranslation = False
  , Coq.skipDefinitions    = skips
  , Coq.vectorModule       = "SAWCoreVectorsAsCoqVectors"
  }

writeCoqTerm ::
  String ->
  [(String, String)] ->
  [String] ->
  FilePath ->
  Term ->
  TopLevel ()
writeCoqTerm name notations skips path t = do
  let configuration = coqTranslationConfiguration notations skips
  case Coq.translateTermAsDeclImports configuration name t of
    Left err -> throwTopLevel $ "Error translating: " ++ show err
    Right doc -> io $ case path of
      "" -> print doc
      _ -> writeFile path (show doc)

writeCoqProp ::
  String ->
  [(String, String)] ->
  [String] ->
  FilePath ->
  Prop ->
  TopLevel ()
writeCoqProp name notations skips path t =
  do sc <- getSharedContext
     tm <- io (propToTerm sc t)
     writeCoqTerm name notations skips path tm

writeCoqCryptolModule ::
  FilePath ->
  FilePath ->
  [(String, String)] ->
  [String] ->
  TopLevel ()
writeCoqCryptolModule inputFile outputFile notations skips = io $ do
  sc  <- mkSharedContext
  ()  <- scLoadPreludeModule sc
  ()  <- scLoadCryptolModule sc
  let ?fileReader = BS.readFile
  env <- initCryptolEnv sc
  cryptolPrimitivesForSAWCoreModule <- scFindModule sc nameOfCryptolPrimitivesForSAWCoreModule
  (cm, _) <- loadCryptolModule sc env inputFile
  let cryptolPreludeDecls = map Coq.moduleDeclName (moduleDecls cryptolPrimitivesForSAWCoreModule)
  let configuration = coqTranslationConfiguration notations skips
  case Coq.translateCryptolModule configuration cryptolPreludeDecls cm of
    Left e -> putStrLn $ show e
    Right cmDoc ->
      writeFile outputFile
      (show . vcat $ [ Coq.preamble configuration
                     , "From CryptolToCoq Require Import SAWCorePrelude."
                     , "Import SAWCorePrelude."
                     , "From CryptolToCoq Require Import CryptolPrimitivesForSAWCore."
                     , "Import CryptolPrimitives."
                     , "From CryptolToCoq Require Import CryptolPrimitivesForSAWCoreExtra."
                     , ""
                     , cmDoc
                     ])

nameOfSAWCorePrelude :: Un.ModuleName
nameOfSAWCorePrelude = Un.moduleName preludeModule

nameOfCryptolPrimitivesForSAWCoreModule :: Un.ModuleName
nameOfCryptolPrimitivesForSAWCoreModule = Un.moduleName cryptolModule

writeCoqSAWCorePrelude ::
  FilePath ->
  [(String, String)] ->
  [String] ->
  IO ()
writeCoqSAWCorePrelude outputFile notations skips = do
  sc  <- mkSharedContext
  ()  <- scLoadPreludeModule sc
  m   <- scFindModule sc nameOfSAWCorePrelude
  let configuration = coqTranslationConfiguration notations skips
  let doc = Coq.translateSAWModule configuration m
  writeFile outputFile (show . vcat $ [ Coq.preamble configuration, doc ])

writeCoqCryptolPrimitivesForSAWCore ::
  FilePath ->
  [(String, String)] ->
  [String] ->
  IO ()
writeCoqCryptolPrimitivesForSAWCore outputFile notations skips = do
  sc <- mkSharedContext
  () <- scLoadPreludeModule sc
  () <- scLoadCryptolModule sc
  () <- scLoadModule sc (emptyModule (mkModuleName ["CryptolPrimitivesForSAWCore"]))
  m  <- scFindModule sc nameOfCryptolPrimitivesForSAWCoreModule
  let configuration = coqTranslationConfiguration notations skips
  let doc = Coq.translateSAWModule configuration m
  let extraPreamble = vcat $
        [ "From CryptolToCoq Require Import SAWCorePrelude."
        , "Import SAWCorePrelude."
        ]
  writeFile outputFile (show . vcat $ [ Coq.preamblePlus configuration extraPreamble
                                      , doc
                                      ])

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
