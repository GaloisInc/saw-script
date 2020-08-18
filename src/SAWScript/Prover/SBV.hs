module SAWScript.Prover.SBV
  ( proveUnintSBV
  , SBV.SMTConfig
  , SBV.z3, SBV.cvc4, SBV.yices, SBV.mathSAT, SBV.boolector
  , prepNegatedSBV
  ) where

import System.Directory

import           Data.Maybe
import           Data.Map ( Map )
import qualified Data.Map as Map
import qualified Data.Vector as V
import           Control.Monad

import qualified Data.SBV.Dynamic as SBV
import qualified Data.SBV.Internals as SBV

import qualified Verifier.SAW.Simulator.SBV as SBVSim

import Verifier.SAW.SharedTerm
import Verifier.SAW.FiniteValue
import Verifier.SAW.Recognizer(asPi, asPiList)

import SAWScript.Proof(Prop, propToPredicate)
import SAWScript.Prover.SolverStats
import SAWScript.Prover.Rewrite(rewriteEqs)


-- | Bit-blast a proposition and check its validity using SBV.
-- Constants with names in @unints@ are kept as uninterpreted
-- functions.
proveUnintSBV ::
  SBV.SMTConfig {- ^ SBV configuration -} ->
  [String]      {- ^ Uninterpreted functions -} ->
  Maybe Integer {- ^ Timeout in milliseconds -} ->
  SharedContext {- ^ Context for working with terms -} ->
  Prop          {- ^ A proposition to be proved -} ->
  IO (Maybe [(String, FirstOrderValue)], SolverStats)
    -- ^ (example/counter-example, solver statistics)
proveUnintSBV conf unints timeout sc term =
  do p <- findExecutable . SBV.executable $ SBV.solver conf
     unless (isJust p) . fail $ mconcat
       [ "Unable to locate the executable \""
       , SBV.executable $ SBV.solver conf
       , "\" needed to run the solver "
       , show . SBV.name $ SBV.solver conf
       ]

     (t', mlabels, lit) <- prepNegatedSBV sc unints term

     tp <- scWhnf sc =<< scTypeOf sc t'
     let (args, _) = asPiList tp
         (labels, argNames) = unzip [ (l, n) | (Just l, n) <- zip mlabels (map fst args) ]

         script = do
           maybe (return ()) SBV.setTimeOut timeout
           lit
     SBV.SatResult r <- SBV.satWith conf script

     let stats = solverStats ("SBV->" ++ show (SBV.name (SBV.solver conf)))
                             (scSharedSize t')
     case r of

       SBV.Satisfiable {} ->
         do let dict = SBV.getModelDictionary r
                r'   = getLabels labels dict argNames
            return (r', stats)

       SBV.SatExtField {} -> fail "Prover returned model in extension field"

       SBV.Unsatisfiable {} -> return (Nothing, stats)

       SBV.Unknown {} -> fail "Prover returned Unknown"

       SBV.ProofError _ ls _ -> fail . unlines $ "Prover returned error: " : ls

-- | Convert a saw-core proposition to a logically-negated SBV
-- symbolic boolean formula with existentially quantified variables.
-- The returned formula is suitable for checking satisfiability. The
-- specified function names are left uninterpreted.
prepNegatedSBV ::
  SharedContext ->
  [String] {- ^ Uninterpreted function names -} ->
  Prop     {- ^ Proposition to prove -} ->
  IO (Term, [Maybe SBVSim.Labeler], SBV.Symbolic SBV.SVal)
prepNegatedSBV sc unints goal =
  do t0 <- propToPredicate sc goal
     -- Abstract over all non-function ExtCns variables
     let nonFun e = fmap ((== Nothing) . asPi) (scWhnf sc (ecType e))
     exts <- filterM nonFun (getAllExts t0)

     t' <- scAbstractExts sc exts t0 >>= rewriteEqs sc

     (labels, lit) <- SBVSim.sbvSolve sc mempty unints t'
     let lit' = liftM SBV.svNot lit
     return (t', labels, lit')




getLabels ::
  [SBVSim.Labeler] ->
  Map String SBV.CV ->
  [String] -> Maybe [(String,FirstOrderValue)]

getLabels ls d argNames
  | length argNames == length xs = Just (zip argNames xs)
  | otherwise = error $ unwords
                [ "SBV SAT results do not match expected arguments "
                , show argNames, show xs]

  where
  xs = fmap getLabel ls

  getLabel (SBVSim.BoolLabel s)    = FOVBit (SBV.cvToBool (d Map.! s))
  getLabel (SBVSim.IntegerLabel s) = FOVInt (cvToInteger (d Map.! s))

  getLabel (SBVSim.WordLabel s)    = FOVWord (cvKind cv) (cvToInteger cv)
    where cv = d Map.! s

  getLabel (SBVSim.VecLabel ns)
    | V.null ns = error "getLabel of empty vector"
    | otherwise = fovVec t vs
    where vs = map getLabel (V.toList ns)
          t  = firstOrderTypeOf (head vs)

  getLabel (SBVSim.TupleLabel ns) = FOVTuple $ map getLabel (V.toList ns)
  getLabel (SBVSim.RecLabel ns) = FOVRec $ fmap getLabel ns

  cvKind cv =
    case SBV.kindOf cv of
      SBV.KBounded _ k -> fromIntegral k
      _                -> error "cvKind"

  cvToInteger cv =
    case SBV.cvVal cv of
      SBV.CInteger i -> i
      _               -> error "cvToInteger"
