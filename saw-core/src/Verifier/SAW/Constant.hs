{- |
Module      : Verifier.SAW.Constant
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : huffman@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module Verifier.SAW.Constant (scConst) where
import Verifier.SAW.SharedTerm
import Verifier.SAW.Rewriter
import Verifier.SAW.Conversion

scConst :: SharedContext -> String -> Term -> IO Term
scConst sc name t = do
  ty <- scTypeOf sc t
  ty' <- rewriteSharedTerm sc (addConvs natConversions emptySimpset) ty
  scConstant sc name t ty'
