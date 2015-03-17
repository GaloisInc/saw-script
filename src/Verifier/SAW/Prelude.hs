{-# LANGUAGE CPP #-}
{-# LANGUAGE TemplateHaskell #-}

{- |
Module      : Verifier.SAW.Prelude
Copyright   : Galois, Inc. 2012-2014
License     : BSD3
Maintainer  : jhendrix@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module Verifier.SAW.Prelude
  ( Module
  , module Verifier.SAW.Prelude
  , module Verifier.SAW.Prelude.Constants
  ) where

import Control.Applicative ((<$>), (<*>))
import Control.Monad (join) 
import Verifier.SAW.ParserUtils
import Verifier.SAW.Prelude.Constants
import Verifier.SAW.SharedTerm

$(runDecWriter $ do
    prelude <- defineModuleFromFile [] "preludeModule" "prelude/Prelude.sawcore"
    declareSharedModuleFns "Prelude" (decVal prelude)
 )

scFinConst :: SharedContext s
           -> Nat -- ^ Index
           -> Nat -- ^ Bound n
           -> IO (SharedTerm s)
scFinConst sc i n | i < n = do
  fv <- scApplyPrelude_FinVal sc
  join $ fv <$> scNat sc i <*> scNat sc (n - (i + 1))
scFinConst _ _ _ = error "illegal arguments to scFinConst"

scEq :: SharedContext s -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
scEq sc x y = do
  xty <- scTypeOf sc x
  eqOp <- scApplyPrelude_eq sc
  eqOp xty x y
