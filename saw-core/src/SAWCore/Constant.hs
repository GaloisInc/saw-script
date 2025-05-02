{- |
Module      : SAWCore.Constant
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : huffman@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module SAWCore.Constant (scConst) where

import Data.Text (Text)

import SAWCore.SharedTerm
import SAWCore.Rewriter
import SAWCore.Conversion

scConst :: SharedContext -> Text -> Term -> IO Term
scConst sc name t = do
  ty <- scTypeOf sc t
  (_,ty') <- rewriteSharedTerm sc (addConvs natConversions emptySimpset :: Simpset ()) ty
  scConstant sc name t ty'
