{-# LANGUAGE CPP #-}
{-# LANGUAGE TemplateHaskell #-}
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
           -> Integer -- ^ Index
           -> Integer -- ^ Bound n
           -> IO (SharedTerm s)
scFinConst sc i n | i < n = do
  fv <- scApplyPreludeFinVal sc
  join $ fv <$> scNat sc i <*> scNat sc (n - (i + 1))
scFinConst _ _ _ = error "illegal arguments to scFinConst"

