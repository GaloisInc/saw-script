{-# Language ViewPatterns #-}
module SAWScript.Prover.Exporter
  ( satWithExporter
  , adaptExporter

    -- * External formats
  , writeAIG
  , writeSAIG
  , writeSAIGInferLatches
  , writeAIGComputedLatches
  , writeCNF
  , write_cnf
  , writeSMTLib2
  , write_smtlib2
  , writeUnintSMTLib2
  , writeCore

    -- * Misc
  , bitblastPrim
  ) where

import Data.Foldable(toList)

import Control.Monad.IO.Class (liftIO)
import qualified Data.AIG as AIG
import qualified Data.SBV.Dynamic as SBV

import Cryptol.Utils.PP(pretty)

import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedTerm
import Verifier.SAW.FiniteValue
import Verifier.SAW.Recognizer (asPi, asPiList, asEqTrue)
import Verifier.SAW.ExternalFormat(scWriteExternal)
import qualified Verifier.SAW.Simulator.BitBlast as BBSim


import SAWScript.SAWCorePrimitives( bitblastPrimitives )
import SAWScript.Prover.SolverStats
import SAWScript.Prover.Rewrite
import SAWScript.Prover.Util
import SAWScript.Prover.SBV(prepSBV)
import SAWScript.Value


satWithExporter ::
  (SharedContext -> FilePath -> Term -> IO ()) ->
  String ->
  SharedContext ->
  Term ->
  IO SolverStats
satWithExporter exporter path sc goal =
  do exporter sc path goal
     let stats = solverStats ("offline: "++ path) (scSharedSize goal)
     return stats

-- | Converts an old-style exporter (which expects to take a predicate
-- as an argument) into a new-style one (which takes a pi-type proposition).
adaptExporter ::
  (SharedContext -> FilePath -> Term -> IO ()) ->
  (SharedContext -> FilePath -> Term -> IO ())
adaptExporter exporter sc path goal =
  do let (args, concl) = asPiList goal
     p <- asEqTrue concl
     p' <- scNot sc p
     t <- scLambdaList sc args p'
     exporter sc path t


--------------------------------------------------------------------------------

-- | Write a @Term@ representing a theorem or an arbitrary
-- function to an AIG file.
writeAIG :: (AIG.IsAIG l g) => AIG.Proxy l g -> SharedContext -> FilePath -> Term -> IO ()
writeAIG proxy sc f t = do
  liftIO $ do
    aig <- bitblastPrim proxy sc t
    AIG.writeAiger f aig

-- | Like @writeAIG@, but takes an additional 'Integer' argument
-- specifying the number of input and output bits to be interpreted as
-- latches. Used to implement more friendly SAIG writers
-- @writeSAIGInferLatches@ and @writeSAIGComputedLatches@.
writeSAIG :: (AIG.IsAIG l g) => AIG.Proxy l g -> SharedContext -> FilePath -> Term -> Int -> IO ()
writeSAIG proxy sc file tt numLatches = do
  liftIO $ do
    aig <- bitblastPrim proxy sc tt
    AIG.writeAigerWithLatches file aig numLatches

-- | Given a term a type '(i, s) -> (o, s)', call @writeSAIG@ on term
-- with latch bits set to '|s|', the width of 's'.
writeSAIGInferLatches :: (AIG.IsAIG l g) => AIG.Proxy l g -> SharedContext -> FilePath -> TypedTerm -> IO ()
writeSAIGInferLatches proxy sc file tt = do
  ty <- scTypeOf sc (ttTerm tt)
  s <- getStateType ty
  let numLatches = sizeFiniteType s
  writeSAIG proxy sc file (ttTerm tt) numLatches
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
  (AIG.IsAIG l g) => AIG.Proxy l g -> SharedContext -> FilePath -> Term -> Int -> IO ()
writeAIGComputedLatches proxy sc file term numLatches =
  writeSAIG proxy sc file term numLatches

writeCNF :: (AIG.IsAIG l g) => AIG.Proxy l g -> SharedContext -> FilePath -> Term -> IO ()
writeCNF proxy sc f t = do
  AIG.Network be ls <- bitblastPrim proxy sc t
  case ls of
    [l] -> do
      _ <- AIG.writeCNF be l f
      return ()
    _ -> fail "writeCNF: non-boolean term"

write_cnf :: SharedContext -> FilePath -> TypedTerm -> TopLevel ()
write_cnf sc f (TypedTerm schema t) = do
  liftIO $ checkBooleanSchema schema
  AIGProxy proxy <- getProxy
  io $ writeCNF proxy sc f t

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
  (_, _, l) <- prepSBV sc unints t
  txt <- SBV.generateSMTBenchmark True l
  writeFile f txt

writeCore :: FilePath -> Term -> IO ()
writeCore path t = writeFile path (scWriteExternal t)


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
  BBSim.withBitBlastedTerm proxy sc bitblastPrimitives t' $ \be ls -> do
    return (AIG.Network be (toList ls))


