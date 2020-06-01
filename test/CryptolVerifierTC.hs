module Main where

import qualified Verifier.SAW.Cryptol as C
import           Verifier.SAW.SharedTerm
import qualified Verifier.SAW.Cryptol.Prelude as C

main :: IO ()
main =
  do sc <- mkSharedContext
     C.scLoadPreludeModule sc
     C.scLoadCryptolModule sc
     putStrLn "Loaded!"
