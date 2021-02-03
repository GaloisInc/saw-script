{-# Language GADTs #-}
{-# Language ImplicitParams #-}
{-# Language OverloadedStrings #-}
{-# Language ViewPatterns #-}
{-# Language ExplicitForAll #-}
{-# Language FlexibleContexts #-}
{-# Language TypeApplications #-}
module SAWScript.Prover.Exporter
  ( proveWithExporter
  , adaptExporter

    -- * External formats
  , writeAIG
  , writeSAIG
  , writeSAIGInferLatches
  , writeAIGComputedLatches
  , writeCNF
  , write_cnf
  , writeSMTLib2
  , writeSMTLib2What4
  , write_smtlib2
  , write_smtlib2_w4
  , writeUnintSMTLib2
  , writeUnintSMTLib2What4
  , writeCoqCryptolPrimitivesForSAWCore
  , writeCoqCryptolModule
  , writeCoqSAWCorePrelude
  , writeCoqTerm
  , writeCoqProp
  , writeCore
  , writeVerilog
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
import Verifier.SAW.Recognizer (asPi, asPiList, asEqTrue)
import Verifier.SAW.SharedTerm as SC
import qualified Verifier.SAW.Translation.Coq as Coq
import Verifier.SAW.TypedAST (mkModuleName)
import Verifier.SAW.TypedTerm
import qualified Verifier.SAW.Simulator.BitBlast as BBSim
import qualified Verifier.SAW.Simulator.Value as Sim
import qualified Verifier.SAW.Simulator.What4 as W4Sim

import qualified Verifier.SAW.UntypedAST as Un

import SAWScript.Crucible.Common
import SAWScript.Proof (Prop(..), predicateToProp, Quantification(..), propToPredicate)
import SAWScript.Prover.SolverStats
import SAWScript.Prover.Rewrite
import SAWScript.Prover.Util
import SAWScript.Prover.What4
import SAWScript.Prover.SBV (prepNegatedSBV)
import SAWScript.Value

import qualified What4.Interface as W4
import qualified What4.Expr.Builder as W4
import What4.Protocol.SMTLib2 (writeDefaultSMT2)
import What4.Protocol.VerilogWriter (exprVerilog)
import What4.Solver.Adapter
import qualified What4.SWord as W4Sim

proveWithExporter ::
  (SharedContext -> FilePath -> Prop -> TopLevel ()) ->
  String ->
  Prop ->
  TopLevel SolverStats
proveWithExporter exporter path goal =
  do sc <- getSharedContext
     exporter sc path goal
     let stats = solverStats ("offline: "++ path) (scSharedSize (unProp goal))
     return stats

-- | Converts an old-style exporter (which expects to take a predicate
-- as an argument) into a new-style one (which takes a pi-type proposition).
adaptExporter ::
  (SharedContext -> FilePath -> Term -> TopLevel ()) ->
  (SharedContext -> FilePath -> Prop -> TopLevel ())
adaptExporter exporter sc path (Prop goal) =
  do let (args, concl) = asPiList goal
     p <-
       case asEqTrue concl of
         Just p -> return p
         Nothing -> throwTopLevel "adaptExporter: expected EqTrue"
     p' <- io $ scNot sc p -- is this right?
     t <- io $ scLambdaList sc args p'
     exporter sc path t


--------------------------------------------------------------------------------

-- | Write a @Term@ representing a theorem or an arbitrary
-- function to an AIG file.
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

writeCNF :: (AIG.IsAIG l g) => AIG.Proxy l g -> SharedContext -> FilePath -> Term -> TopLevel ()
writeCNF proxy sc f t = do
  AIG.Network be ls <- io $ bitblastPrim proxy sc t
  case ls of
    [l] -> do
      _ <- io $ AIG.writeCNF be l f
      return ()
    _ -> throwTopLevel "writeCNF: non-boolean term"

write_cnf :: SharedContext -> FilePath -> TypedTerm -> TopLevel ()
write_cnf sc f (TypedTerm schema t) = do
  liftIO $ checkBooleanSchema schema
  AIGProxy proxy <- getProxy
  writeCNF proxy sc f t

-- | Write a proposition to an SMT-Lib version 2 file. Because @Prop@ is
-- assumed to have universally quantified variables, it will be negated.
writeSMTLib2 :: SharedContext -> FilePath -> Prop -> TopLevel ()
writeSMTLib2 sc f t = writeUnintSMTLib2 mempty sc f t

-- | Write a proposition to an SMT-Lib version 2 file. Because @Prop@ is
-- assumed to have universally quantified variables, it will be negated.
-- This version uses What4 instead of SBV.
writeSMTLib2What4 :: SharedContext -> FilePath -> Prop -> TopLevel ()
writeSMTLib2What4 sc f t = writeUnintSMTLib2What4 mempty sc f t

-- | Write a @Term@ representing a predicate (i.e. a monomorphic
-- function returning a boolean) to an SMT-Lib version 2 file. The goal
-- is to pass the term through as directly as possible, so we interpret
-- it as an existential.
write_smtlib2 :: SharedContext -> FilePath -> TypedTerm -> TopLevel ()
write_smtlib2 sc f (TypedTerm schema t) = do
  io $ checkBooleanSchema schema
  p <- io $ predicateToProp sc Existential [] t
  writeSMTLib2 sc f p

-- | Write a @Term@ representing a predicate (i.e. a monomorphic
-- function returning a boolean) to an SMT-Lib version 2 file. The goal
-- is to pass the term through as directly as possible, so we interpret
-- it as an existential. This version uses What4 instead of SBV.
write_smtlib2_w4 :: SharedContext -> FilePath -> TypedTerm -> TopLevel ()
write_smtlib2_w4 sc f (TypedTerm schema t) = do
  io $ checkBooleanSchema schema
  p <- io $ predicateToProp sc Existential [] t
  writeUnintSMTLib2What4 mempty sc f p

-- | Write a proposition to an SMT-Lib version 2 file, treating some
-- constants as uninterpreted. Because @Prop@ is assumed to have
-- universally quantified variables, it will be negated.
writeUnintSMTLib2 :: Set VarIndex -> SharedContext -> FilePath -> Prop -> TopLevel ()
writeUnintSMTLib2 unintSet sc f p = io $
  do (_, _, l) <- prepNegatedSBV sc unintSet p
     let isSat = True -- l is encoded as an existential formula
     txt <- SBV.generateSMTBenchmark isSat l
     writeFile f txt

-- | Write a proposition to an SMT-Lib version 2 file, treating some
-- constants as uninterpreted. Because @Prop@ is assumed to have
-- universally quantified variables, it will be negated. This version
-- uses What4 instead of SBV.
writeUnintSMTLib2What4 :: Set VarIndex -> SharedContext -> FilePath -> Prop -> TopLevel ()
writeUnintSMTLib2What4 unints sc f goal = io $
  do sym <- W4.newExprBuilder W4.FloatRealRepr St globalNonceGenerator
     term <- propToPredicate sc goal
     (_, _, (_,lit0)) <- prepWhat4 sym sc unints term
     lit <- W4.notPred sym lit0 -- for symmetry with `prepNegatedSBV` above
     withFile f WriteMode $ \h ->
       writeDefaultSMT2 () "Offline SMTLib2" defaultWriteSMTLIB2Features sym h [lit]

writeCore :: FilePath -> Term -> TopLevel ()
writeCore path t = io $ writeFile path (scWriteExternal t)

write_verilog :: SharedContext -> FilePath -> Term -> TopLevel ()
write_verilog sc path t = io $ writeVerilog sc path t

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
writeCoreProp path (Prop t) = io $ writeFile path (scWriteExternal t)

coqTranslationConfiguration ::
  [(String, String)] ->
  [String] ->
  Coq.TranslationConfiguration
coqTranslationConfiguration notations skips = Coq.TranslationConfiguration
  { Coq.notations          = notations
  , Coq.monadicTranslation = False
  , Coq.skipDefinitions    = skips
  , Coq.vectorModule       = "SAWVectorsAsCoqVectors"
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
writeCoqProp name notations skips path (Prop t) =
  writeCoqTerm name notations skips path t

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
  t' <- rewriteEqs sc t
{-
  let s = ttSchema t'
  case s of
    C.Forall [] [] _ -> return ()
    _ -> fail $ "Attempting to bitblast a term with a polymorphic type: " ++ pretty s
-}
  BBSim.withBitBlastedTerm proxy sc mempty t' $ \be ls -> do
    return (AIG.Network be (toList ls))
