{- |
Module      : Verifier.SAW.Constant
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : huffman@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module Verifier.SAW.Constant (scConst) where

import Data.Text (Text)

import Verifier.SAW.SharedTerm
import Verifier.SAW.Rewriter
import Verifier.SAW.Conversion

scConst :: SharedContext -> Text -> Term -> IO Term
scConst sc name t = do
  ty <- scTypeOf sc t
  (_,ty') <- rewriteSharedTerm sc (addConvs natConversions emptySimpset :: Simpset ()) ty
  scConstant sc name t ty'
