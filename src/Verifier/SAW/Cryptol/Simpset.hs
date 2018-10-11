{- |
Module      : Verifier.SAW.Cryptol.Simpset
Copyright   : Galois, Inc. 2018
License     : BSD3
Maintainer  : huffman@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

{-# LANGUAGE OverloadedStrings #-}

module Verifier.SAW.Cryptol.Simpset where

import Verifier.SAW.Module
import Verifier.SAW.Rewriter
import Verifier.SAW.SharedTerm
import Verifier.SAW.Term.Functor

mkCryptolSimpset :: SharedContext -> IO Simpset
mkCryptolSimpset sc =
  do m <- scFindModule sc (mkModuleName ["Cryptol"])
     scSimpset sc (cryptolDefs m) [] []
  where
    cryptolDefs m = filter (not . excluded) $ moduleDefs m
    excluded d = defIdent d `elem` [ "Cryptol.fix" ]
