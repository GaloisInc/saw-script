{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
module SAWScript.TestEval where

import Data.Bits
import Data.Map ( Map )
import qualified Data.Map as Map
import Data.Vector ( Vector )
import qualified Data.Vector as V

import Verifier.SAW.Evaluator
import Verifier.SAW.ParserUtils ( readModuleFromFile )
import Verifier.SAW.Prelude
import qualified Verifier.SAW.SBVParser as SBV
import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedAST

runTest :: IO ()
runTest =
    do sawScriptModule <- readModuleFromFile [preludeModule] "examples/prelude.sawcore"
       (sc :: SharedContext s) <- mkSharedContext sawScriptModule
       let global = evalGlobal sawScriptModule (allPrims global)
       let t = Term (FTermF (GlobalDef "SAWScriptPrelude.test"))
       runSC (fromValue (evalTerm global [] t :: Value s)) sc

sawScriptPrims :: forall s. (Ident -> Value s) -> Map Ident (Value s)
sawScriptPrims global = Map.fromList
  [ ("SAWScriptPrelude.topBind", toValue
      (topBind :: () -> () -> SC s (Value s) -> (Value s -> SC s (Value s)) -> SC s (Value s)))
  , ("SAWScriptPrelude.topReturn", toValue
      (topReturn :: () -> Value s -> SC s (Value s)))
  , ("SAWScriptPrelude.loadSBV", toValue
      (loadSBV :: FilePath -> SC s (SharedTerm s)))
  --, ("SAWScriptPrelude.loadAIG", toValue
  --    (loadAIG :: FilePath -> SC s (SharedTerm s)))
  , ("SAWScriptPrelude.termGlobal", toValue
      (termGlobal :: String -> SC s (SharedTerm s)))
  , ("SAWScriptPrelude.termTrue", toValue (termTrue :: SC s (SharedTerm s)))
  , ("SAWScriptPrelude.termFalse", toValue (termFalse :: SC s (SharedTerm s)))
  , ("SAWScriptPrelude.termNat", toValue
      (termNat :: Integer -> SC s (SharedTerm s)))
  , ("SAWScriptPrelude.termVec", toValue
      (termVec :: Integer -> SharedTerm s -> Vector (SharedTerm s) -> SC s (SharedTerm s)))
  , ("SAWScriptPrelude.termTuple", toValue
      (termTuple :: Integer -> Vector (SharedTerm s) -> SC s (SharedTerm s)))
  , ("SAWScriptPrelude.termRecord", toValue
      (termRecord :: Integer -> Vector (String, SharedTerm s) -> SC s (SharedTerm s)))
  , ("SAWScriptPrelude.termSelect", toValue
      (termSelect :: SharedTerm s -> String -> SC s (SharedTerm s)))
  , ("SAWScriptPrelude.termLocalVar", toValue
      (termLocalVar :: Integer -> SharedTerm s -> SC s (SharedTerm s)))
  , ("SAWScriptPrelude.termGlobal", toValue
      (termGlobal :: String -> SC s (SharedTerm s)))
  , ("SAWScriptPrelude.termLambda", toValue
      (termLambda :: String -> SharedTerm s -> SharedTerm s -> SC s (SharedTerm s)))
  , ("SAWScriptPrelude.loadSBV", toValue
      (loadSBV :: FilePath -> SC s (SharedTerm s)))
  , ("SAWScriptPrelude.termApp", toValue
      (termApp :: SharedTerm s -> SharedTerm s -> SC s (SharedTerm s)))
  , ("SAWScriptPrelude.print", toValue
      (myPrint :: () -> Value s -> SC s ()))
  , ("SAWScriptPrelude.bvNatIdent", toValue ("Prelude.bvNat" :: String))
  , ("SAWScript.predNat", toValue (pred :: Integer -> Integer))
  , ("SAWScript.isZeroNat", toValue ((== 0) :: Integer -> Bool))
  , ("SAWScriptPrelude.p384_safe_product_path", toValue p384_safe_product_path)
  , ("SAWScriptPrelude.evaluate", toValue (evaluate global :: () -> SharedTerm s -> Value s))
  , ("Prelude.append", toValue
      (myAppend :: Int -> Int -> () -> Value s -> Value s -> Value s))
  ]

allPrims :: (Ident -> Value s) -> Map Ident (Value s)
allPrims global = Map.union preludePrims (sawScriptPrims global)

--topReturn :: (a :: sort 0) -> a -> TopLevel a;
topReturn :: () -> Value s -> SC s (Value s)
topReturn _ = return

--topBind :: (a b :: sort 0) -> TopLevel a -> (a -> TopLevel b) -> TopLevel b;
topBind :: () -> () -> SC s (Value s) -> (Value s -> SC s (Value s)) -> SC s (Value s)
topBind _ _ = (>>=)

-- TODO: Add argument for uninterpreted-function map
loadSBV :: FilePath -> SC s (SharedTerm s)
loadSBV path =
    mkSC $ \sc -> do
      pgm <- SBV.loadSBV path
      SBV.parseSBVPgm sc (\_ _ -> Nothing) pgm

-- Implementations of SharedTerm primitives
termTrue :: SC s (SharedTerm s)
termTrue = mkSC $ \sc -> scCtorApp sc "Prelude.True" []

termFalse :: SC s (SharedTerm s)
termFalse = mkSC $ \sc -> scCtorApp sc "Prelude.False" []

{-
loadAIG :: FilePath -> SC s (SharedTerm s)
loadAIG path =
    mkSC $ \sc -> do
      n <- createNetwork
      freeNetwork n
      error "not yet implemented"
-}

termNat :: Integer -> SC s (SharedTerm s)
termNat n = mkSC $ \sc -> scNat sc n

termVec :: Integer -> SharedTerm s -> Vector (SharedTerm s) -> SC s (SharedTerm s)
termVec _ t v = mkSC $ \sc -> scVector sc t (V.toList v)

-- TODO: termGet

termTuple :: Integer -> Vector (SharedTerm s) -> SC s (SharedTerm s)
termTuple _ tv = mkSC $ \sc -> scTuple sc (V.toList tv)

termRecord :: Integer -> Vector (String, SharedTerm s) -> SC s (SharedTerm s)
termRecord _ v = mkSC $ \sc -> scMkRecord sc (Map.fromList (V.toList v))

termSelect :: SharedTerm s -> String -> SC s (SharedTerm s)
termSelect t s = mkSC $ \sc -> scRecordSelect sc t s

termLocalVar :: Integer -> SharedTerm s -> SC s (SharedTerm s)
termLocalVar n t = mkSC $ \sc -> scLocalVar sc (fromInteger n) t

termGlobal :: String -> SC s (SharedTerm s)
termGlobal name = mkSC $ \sc -> scGlobalDef sc (parseIdent name)

termLambda :: String -> SharedTerm s -> SharedTerm s -> SC s (SharedTerm s)
termLambda s t1 t2 = mkSC $ \sc -> scLambda sc s t1 t2

termApp :: SharedTerm s -> SharedTerm s -> SC s (SharedTerm s)
termApp t1 t2 = mkSC $ \sc -> scApply sc t1 t2

-- evaluate :: (a :: sort 0) -> Term -> a;
evaluate :: (Ident -> Value s) -> () -> SharedTerm s -> Value s
evaluate global _ = evalSharedTerm global

p384_safe_product_path :: String
p384_safe_product_path = "examples/p384_safe_product.sbv"
-- (x, y) -> uext(x) * uext(y)
-- ([384], [384]) -> [768]

myPrint :: () -> Value s -> SC s ()
myPrint _ v = mkSC $ const (print v)

-- append :: (m n :: Nat) -> (e :: sort 0) -> Vec m e -> Vec n e -> Vec (addNat m n) e;
myAppend :: Int -> Int -> () -> Value s -> Value s -> Value s
myAppend _ _ _ (VWord a x) (VWord b y) = VWord (a + b) (x .|. shiftL y b)
myAppend _ _ _ (VVector xv) (VVector yv) = VVector ((V.++) xv yv)
myAppend _ _ _ _ _ = error "Prelude.append: malformed arguments"
