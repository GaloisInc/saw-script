{-# Language ViewPatterns #-}
module SAWScript.Prover.Exporter
  ( satWithExporter

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

import qualified Data.ABC.GIA as GIA
import qualified Data.AIG as AIG
import qualified Data.ABC as ABC
import qualified Data.SBV.Dynamic as SBV

import Cryptol.Utils.PP(pretty)

import Verifier.SAW.SharedTerm
import Verifier.SAW.Term.Functor(unwrapTermF)
import Verifier.SAW.TypedTerm
import Verifier.SAW.FiniteValue
import Verifier.SAW.Recognizer(asPi, asPiList, asBoolType)
import Verifier.SAW.ExternalFormat(scWriteExternal)
import qualified Verifier.SAW.Simulator.BitBlast as BBSim


import SAWScript.SAWCorePrimitives( bitblastPrimitives )
import SAWScript.ImportAIG
import SAWScript.Prover.Mode(ProverMode(..))
import SAWScript.Prover.SolverStats
import SAWScript.Prover.Rewrite
import SAWScript.Prover.Util
import SAWScript.Prover.SBV(prepSBV)


satWithExporter :: (SharedContext -> FilePath -> Term -> IO ())
                -> String
                -> SharedContext
                -> ProverMode
                -> Term
                -> IO SolverStats
satWithExporter exporter path sc mode t0 =
  do t <- case mode of
            CheckSat -> return t0
            Prove ->
              do ty <- scTypeOf sc t0
                 let (ts, tf) = asPiList ty
                 tf' <- scWhnf sc tf
                 case asBoolType tf' of
                   Nothing -> fail $ "Invalid non-boolean type: " ++ show ty
                   Just () -> return ()
                 negTerm (map snd ts) t0

     exporter sc path t
     let stats = solverStats ("offline: "++ path) (scSharedSize t)
     return stats

  where
  negTerm :: [Term] -> Term -> IO Term
  negTerm [] p = scNot sc p
  negTerm (t1 : ts) p =
    do (x, ty, p') <- case unwrapTermF p of
                        Lambda x ty p' -> return (x, ty, p')
                        _ -> do
                          p1 <- incVars sc 0 1 p
                          x0 <- scLocalVar sc 0
                          p' <- scApply sc p1 x0
                          return ("x", t1, p')
       scLambda sc x ty =<< negTerm ts p'


--------------------------------------------------------------------------------

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
  (_, _, l) <- prepSBV sc unints t
  txt <- SBV.generateSMTBenchmark True l
  writeFile f txt

writeCore :: FilePath -> Term -> IO ()
writeCore path t = writeFile path (scWriteExternal t)


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


