{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module SAWCentral.Crucible.Common.Pred (
    checkBooleanType
    ) where

import Cryptol.TypeCheck.Type (tIsBit)
import CryptolSAWCore.TypedTerm (mkTypedTerm, ttType, ttIsMono)
import SAWCore.SharedTerm (SharedContext, Term)

-- | Ensure that the term has Cryptol type `Bit`
checkBooleanType :: SharedContext -> Term -> IO ()
checkBooleanType sc tm = do
  tt <- mkTypedTerm sc tm
  case ttIsMono (ttType tt) of
    Just ty | tIsBit ty -> pure ()
            | otherwise -> fail $ "Expected type Bit, got: " ++ show ty
    Nothing -> fail "Expected monomorphic Cryptol type, got polymorphic or unknown"
