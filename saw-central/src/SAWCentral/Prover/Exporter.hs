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
  , write_smtlib2_w4
  , writeCoqCryptolPrimitivesForSAWCore
  , writeCoqCryptolModule
  , writeCoqSAWCorePrelude
  , writeCoqTerm
  , coqTranslationConfiguration
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

import Control.Monad (unless)
import Control.Monad.Except (runExceptT)
import Control.Monad.State (gets)
import qualified Data.AIG as AIG
import qualified Data.ByteString as BS
import Data.Maybe (mapMaybe)
import Data.Parameterized.Nonce (globalNonceGenerator)
import Data.Parameterized.Some (Some(..))
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.SBV.Dynamic as SBV
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

import CryptolSAWCore.CryptolEnv (initCryptolEnv, loadCryptolModule, mkCryEnv)
import CryptolSAWCore.Prelude (cryptolModule, scLoadPreludeModule, scLoadCryptolModule)
import SAWCore.ExternalFormat(scWriteExternal)
import SAWCore.FiniteValue
import SAWCore.Module (emptyModule, moduleDecls)
import SAWCore.Name (mkModuleName, ecShortName)
import SAWCore.Prelude (preludeModule)
import SAWCore.Recognizer (asPi)
import SAWCore.SATQuery
import SAWCore.SharedTerm as SC
import qualified SAWCoreCoq.Coq as Coq
import qualified Language.Coq.AST as Coq
import CryptolSAWCore.TypedTerm
import qualified SAWCoreAIG.BitBlast as BBSim
import qualified SAWCore.Simulator.Value as Sim
import qualified SAWCoreWhat4.What4 as W4Sim
import qualified SAWCoreSBV.SBV as SBV
import qualified SAWCoreWhat4.What4 as W -- XXX duplicate!?

import qualified SAWCore.Parser.AST as Un

import SAWCentral.Crucible.Common
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
  TopLevel [(ExtCns Term, FiniteType)]
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
    die why = throwTopLevel $
      "writeSAIGInferLatches: " ++ why ++ ":\n" ++
      "term must have type of the form '(i, s) -> (o, s)',\n" ++
      "where 'i', 's', and 'o' are all fixed-width types,\n" ++
      "but type of term is:\n" ++ (show . ppTypedTermType . ttType $ tt)

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
  io $ checkBooleanSchema schema
  sc <- getSharedContext
  satq <- io (predicateToSATQuery sc mempty t)
  writeCNF f satq

write_cnf_external :: FilePath -> TypedTerm -> TopLevel ()
write_cnf_external f (TypedTerm schema t) = do
  io $ checkBooleanSchema schema
  writeCNFviaVerilog f t

-- | Write a @Term@ representing a predicate (i.e. a monomorphic
-- function returning a boolean) to an SMT-Lib version 2 file. The goal
-- is to pass the term through as directly as possible, so we interpret
-- it as an existential.
write_smtlib2 :: FilePath -> TypedTerm -> TopLevel ()
write_smtlib2 f (TypedTerm schema t) = do
  sc <- getSharedContext
  io $ checkBooleanSchema schema
  satq <- io $ predicateToSATQuery sc mempty t
  writeSMTLib2 f satq

-- | Write a @Term@ representing a predicate (i.e. a monomorphic
-- function returning a boolean) to an SMT-Lib version 2 file. The goal
-- is to pass the term through as directly as possible, so we interpret
-- it as an existential. This version uses What4 instead of SBV.
write_smtlib2_w4 :: FilePath -> TypedTerm -> TopLevel ()
write_smtlib2_w4 f (TypedTerm schema t) = do
  sc <- getSharedContext
  io $ checkBooleanSchema schema
  satq <- io $ predicateToSATQuery sc mempty t
  writeSMTLib2What4 f satq

-- | Write a SAT query to an SMT-Lib version 2 file.
writeSMTLib2 :: FilePath -> SATQuery -> TopLevel ()
writeSMTLib2 f satq = getSharedContext >>= \sc -> io $
  do (_, _, l) <- SBV.sbvSATQuery sc mempty satq
#if MIN_VERSION_sbv(10,0,0)
     txt <- SBV.generateSMTBenchmarkSat l
#else
     let isSat = True -- l is encoded as an existential formula
     txt <- SBV.generateSMTBenchmark isSat l
#endif
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

writeVerilogSAT :: FilePath -> SATQuery -> TopLevel [(ExtCns Term, FiniteType)]
writeVerilogSAT path satq = getSharedContext >>= \sc -> io $
  do sym <- newSAWCoreExprBuilder sc False
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
     let argSValueNames = zip argSValues (map ecShortName argNames)
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
flattenSValue sym (Sim.VPair l r) =
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
  st  <- sawCoreState sym
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

coqTranslationConfiguration ::
  [(Text, Text)] ->
  [Text] ->
  Coq.TranslationConfiguration
coqTranslationConfiguration renamings skips = Coq.TranslationConfiguration
  { Coq.constantRenaming = map (\(a, b) -> (Text.unpack a, Text.unpack b)) renamings
  , Coq.constantSkips = map Text.unpack skips
  , Coq.monadicTranslation = False
  , Coq.postPreamble = []
  , Coq.vectorModule = "SAWCoreVectorsAsCoqVectors"
  }

withImportSAWCorePrelude :: Coq.TranslationConfiguration  -> Coq.TranslationConfiguration
withImportSAWCorePrelude config@(Coq.TranslationConfiguration { Coq.postPreamble }) =
  config { Coq.postPreamble = postPreamble ++ unlines
   [ "From CryptolToCoq Require Import SAWCorePrelude."
   , "Import SAWCorePrelude."
   ]
  }

withImportSAWCorePreludeExtra :: Coq.TranslationConfiguration  -> Coq.TranslationConfiguration
withImportSAWCorePreludeExtra config@(Coq.TranslationConfiguration { Coq.postPreamble }) =
  config { Coq.postPreamble = postPreamble ++ unlines
   [ "From CryptolToCoq Require Import SAWCorePreludeExtra."
   ]
  }


withImportCryptolPrimitivesForSAWCore ::
  Coq.TranslationConfiguration  -> Coq.TranslationConfiguration
withImportCryptolPrimitivesForSAWCore config@(Coq.TranslationConfiguration { Coq.postPreamble }) =
  config { Coq.postPreamble = postPreamble ++ unlines
   [ "From CryptolToCoq Require Import CryptolPrimitivesForSAWCore."
   , "Import CryptolPrimitivesForSAWCore."
   ]
  }

withImportCryptolPrimitivesForSAWCoreExtra ::
  Coq.TranslationConfiguration  -> Coq.TranslationConfiguration
withImportCryptolPrimitivesForSAWCoreExtra config@(Coq.TranslationConfiguration { Coq.postPreamble }) =
  config { Coq.postPreamble = postPreamble ++ unlines
   [ "From CryptolToCoq Require Import CryptolPrimitivesForSAWCoreExtra."
   ]
  }


writeCoqTerm ::
  Text ->
  [(Text, Text)] ->
  [Text] ->
  FilePath ->
  Term ->
  TopLevel ()
writeCoqTerm name notations skips path t = do
  let configuration =
        withImportCryptolPrimitivesForSAWCore $
        withImportSAWCorePrelude $
        coqTranslationConfiguration notations skips
  sc <- getSharedContext
  mm <- io $ scGetModuleMap sc
  tp <- io $ scTypeOf sc t
  case Coq.translateTermAsDeclImports configuration mm (Coq.Ident (Text.unpack name)) t tp of
    Left err -> throwTopLevel $ "Error translating: " ++ show err
    Right doc -> io $ case path of
      "" -> print doc
      _ -> writeFile path (show doc)

writeCoqProp ::
  Text ->
  [(Text, Text)] ->
  [Text] ->
  FilePath ->
  Prop ->
  TopLevel ()
writeCoqProp name notations skips path t =
  do sc <- getSharedContext
     tm <- io (propToTerm sc t)
     writeCoqTerm name notations skips path tm

-- | Write out a representation of a Cryptol module in Gallina syntax for Coq.
writeCoqCryptolModule ::
  -- | Path to module to export
  FilePath ->
  -- | Path for output Coq file
  FilePath ->
  -- | Pairs of notation substitutions: operator on the left will be replaced
  -- with the identifier on the right
  [(Text, Text)] ->
  -- | List of identifiers to skip during translation
  [Text] ->
  TopLevel ()
writeCoqCryptolModule inputFile outputFile notations skips = io $ do
  sc  <- mkSharedContext
  ()  <- scLoadPreludeModule sc
  ()  <- scLoadCryptolModule sc
  let ?fileReader = BS.readFile
  env <- initCryptolEnv sc
  cryptolPrimitivesForSAWCoreModule <- scFindModule sc nameOfCryptolPrimitivesForSAWCoreModule
  (cm, _) <- loadCryptolModule sc env inputFile
               -- NOTE: implementation of loadCryptolModule, now uses this default:
               --   defaultPrimitiveOptions = ImportPrimitiveOptions{allowUnknownPrimitives=True}
  cry_env <- mkCryEnv env
  mm <- scGetModuleMap sc
  let ?mm = mm
  let cryptolPreludeDecls =
        map Coq.Ident $
        mapMaybe Coq.moduleDeclName (moduleDecls cryptolPrimitivesForSAWCoreModule)
  let configuration =
        withImportCryptolPrimitivesForSAWCoreExtra $
        withImportCryptolPrimitivesForSAWCore $
        withImportSAWCorePreludeExtra $
        withImportSAWCorePrelude $
        coqTranslationConfiguration notations skips
  let nm = Coq.Ident (takeBaseName inputFile)
  res <- Coq.translateCryptolModule sc cry_env nm configuration cryptolPreludeDecls cm
  case res of
    Left e -> putStrLn $ show e
    Right cmDoc ->
      writeFile outputFile
      (show . vcat $ [ Coq.preamble configuration, cmDoc])

nameOfSAWCorePrelude :: Un.ModuleName
nameOfSAWCorePrelude = Un.moduleName preludeModule

nameOfCryptolPrimitivesForSAWCoreModule :: Un.ModuleName
nameOfCryptolPrimitivesForSAWCoreModule = Un.moduleName cryptolModule

writeCoqSAWCorePrelude ::
  FilePath ->
  [(Text, Text)] ->
  [Text] ->
  IO ()
writeCoqSAWCorePrelude outputFile notations skips = do
  sc  <- mkSharedContext
  ()  <- scLoadPreludeModule sc
  mm  <- scGetModuleMap sc
  m   <- scFindModule sc nameOfSAWCorePrelude
  let configuration = coqTranslationConfiguration notations skips
  let doc = Coq.translateSAWModule configuration mm m
  writeFile outputFile (show . vcat $ [ Coq.preamble configuration, doc ])

writeCoqCryptolPrimitivesForSAWCore ::
  FilePath ->
  [(Text, Text)] ->
  [Text] ->
  IO ()
writeCoqCryptolPrimitivesForSAWCore cryFile notations skips = do
  sc <- mkSharedContext
  () <- scLoadPreludeModule sc
  () <- scLoadCryptolModule sc
  () <- scLoadModule sc (emptyModule (mkModuleName ["CryptolPrimitivesForSAWCore"]))
  m  <- scFindModule sc nameOfCryptolPrimitivesForSAWCoreModule
  mm <- scGetModuleMap sc
  let configuration =
        withImportSAWCorePreludeExtra $
        withImportSAWCorePrelude $
        coqTranslationConfiguration notations skips
  let doc = Coq.translateSAWModule configuration mm m
  writeFile cryFile (show . vcat $ [ Coq.preamble configuration
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
