module SAWScript.Prover.SBV
  ( satUnintSBV
  , SBV.SMTConfig
  , SBV.z3, SBV.cvc4, SBV.yices, SBV.mathSAT, SBV.boolector
  , prepSBV
  ) where

import           Data.Map ( Map )
import qualified Data.Map as Map
import qualified Data.Vector as V
import           Control.Monad(filterM,liftM)

import qualified Data.SBV.Dynamic as SBV

import qualified Verifier.SAW.Simulator.SBV as SBVSim

import Verifier.SAW.SharedTerm
import Verifier.SAW.FiniteValue
import Verifier.SAW.TypedTerm(TypedTerm(..), mkTypedTerm)
import Verifier.SAW.Recognizer(asPi, asPiList)

import Verifier.SAW.Cryptol.Prims (sbvPrims)


import SAWScript.Prover.Mode(ProverMode(..))
import SAWScript.Prover.SolverStats
import SAWScript.Prover.Rewrite(rewriteEqs)
import SAWScript.Prover.Util(checkBooleanSchema)



-- | Bit-blast a @Term@ representing a theorem and check its
-- satisfiability using SBV.
-- Constants with names in @unints@ are kept as uninterpreted functions.
satUnintSBV ::
  SBV.SMTConfig {- ^ SBV configuration -} ->
  [String]      {- ^ Uninterpreted functions -} ->
  SharedContext {- ^ Context for working with terms -} ->
  ProverMode    {- ^ Prove/check -} ->
  Term          {- ^ A boolean term to be proved/checked. -} ->
  IO (Maybe [(String,FirstOrderValue)], SolverStats)
    -- ^ (example/counter-example, solver statistics)
satUnintSBV conf unints sc mode term =
  do (t', labels, lit0) <- prepSBV sc unints term

     let lit = case mode of
                 CheckSat -> lit0
                 Prove    -> liftM SBV.svNot lit0

     tp <- scWhnf sc =<< scTypeOf sc t'
     let (args, _) = asPiList tp
         argNames = map fst args
     SBV.SatResult r <- SBV.satWith conf lit

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

       SBV.ProofError _ ls -> fail . unlines $ "Prover returned error: " : ls


prepSBV :: SharedContext -> [String] -> Term
        -> IO (Term, [SBVSim.Labeler], SBV.Symbolic SBV.SVal)
prepSBV sc unints t0 = do
  -- Abstract over all non-function ExtCns variables
  let nonFun e = fmap ((== Nothing) . asPi) (scWhnf sc (ecType e))
  exts <- filterM nonFun (getAllExts t0)

  TypedTerm schema t' <-
      scAbstractExts sc exts t0 >>= rewriteEqs sc >>= mkTypedTerm sc

  checkBooleanSchema schema
  (labels, lit) <- SBVSim.sbvSolve sc sbvPrims unints t'
  return (t', labels, lit)




getLabels ::
  [SBVSim.Labeler] ->
  Map String SBV.CW ->
  [String] -> Maybe [(String,FirstOrderValue)]

getLabels ls d argNames
  | length argNames == length xs = Just (zip argNames xs)
  | otherwise = error $ unwords
                [ "SBV SAT results do not match expected arguments "
                , show argNames, show xs]

  where
  xs = fmap getLabel ls

  getLabel (SBVSim.BoolLabel s)    = FOVBit (SBV.cwToBool (d Map.! s))
  getLabel (SBVSim.IntegerLabel s) = FOVInt (cwToInteger (d Map.! s))

  getLabel (SBVSim.WordLabel s)    = FOVWord (cwKind cw) (cwToInteger cw)
    where cw = d Map.! s

  getLabel (SBVSim.VecLabel ns)
    | V.null ns = error "getLabel of empty vector"
    | otherwise = fovVec t vs
    where vs = map getLabel (V.toList ns)
          t  = firstOrderTypeOf (head vs)

  getLabel (SBVSim.TupleLabel ns) = FOVTuple $ map getLabel (V.toList ns)
  getLabel (SBVSim.RecLabel ns) = FOVRec $ fmap getLabel ns

  cwKind cw =
    case SBV.kindOf cw of
      SBV.KBounded _ k -> fromIntegral k
      _                -> error "cwKind"

  cwToInteger cw =
    case SBV.cwVal cw of
      SBV.CWInteger i -> i
      _               -> error "cwToInteger"


