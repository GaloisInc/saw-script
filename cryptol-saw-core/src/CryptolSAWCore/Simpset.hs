{- |
Module      : Verifier.SAW.Cryptol.Simpset
Copyright   : Galois, Inc. 2018
License     : BSD3
Maintainer  : huffman@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

{-# LANGUAGE OverloadedStrings #-}

module Verifier.SAW.Cryptol.Simpset
  ( mkCryptolSimpset
  ) where

import Verifier.SAW.Module
import Verifier.SAW.Rewriter
import Verifier.SAW.SharedTerm
import Verifier.SAW.Term.Functor

mkCryptolSimpset :: SharedContext -> IO (Simpset a)
mkCryptolSimpset sc =
  do m <- scFindModule sc cryptolModuleName
     scSimpset sc (cryptolDefs m) [] []
  where
    cryptolDefs m = filter (not . excluded) $ moduleDefs m
    excluded d = defIdent d `elem` excludedNames

cryptolModuleName :: ModuleName
cryptolModuleName = mkModuleName ["Cryptol"]

excludedNames :: [Ident]
excludedNames =
  map (mkIdent cryptolModuleName)
  [ "fix"
  , "pair_cong"
  , "seq_cong"
  , "pair_cong1"
  , "pair_cong2"
  , "seq_cong1"
  , "fun_cong"
  , "seq_TCNum"
  , "seq_TCInf"
  , "PLiteral"
  , "PLogic"
  , "PRing"
  , "PIntegral"
  , "PField"
  , "PRound"
  , "PEq"
  , "PCmp"
  , "PSignedCmp"
  , "ecEq"
  ]
