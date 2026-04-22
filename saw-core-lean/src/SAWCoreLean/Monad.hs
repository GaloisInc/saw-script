{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}

{- |
Module      : SAWCoreLean.Monad
Copyright   : Galois, Inc. 2026
License     : BSD3
Maintainer  : saw@galois.com
Stability   : experimental
Portability : portable

Near-mirror of "SAWCoreRocq.Monad". Drops Rocq-specific config fields
(@vectorModule@, @monadicTranslation@, @postPreamble@) since Lean has
native 'BitVec'/'Vector' and no free-monad encoding is needed yet.
-}

module SAWCoreLean.Monad
  ( TranslationConfiguration(..)
  , TranslationConfigurationMonad
  , TranslationMonad
  , TranslationError(..)
  , WithTranslationConfiguration(..)
  , runTranslationMonad
  , ppTranslationError
  ) where

import qualified Control.Monad.Except as Except
import Control.Monad.Reader (MonadReader, ReaderT(..))
import Control.Monad.State (MonadState, StateT(..))
import Data.Text (Text)
import Prelude hiding (fail)

import Prettyprinter ((<+>))

import qualified SAWSupport.Pretty as PPS
import SAWCore.SharedTerm

data TranslationError
  = NotSupported Term
  | NotExpr Term
  | NotType Term
  | LocalVarOutOfBounds Term
  | BadTerm Term
  | CannotCreateDefaultValue Term

ppTranslationError :: SharedContext -> TranslationError -> IO Text
ppTranslationError sc err = do
  let (msg, tm) = case err of
        NotSupported t -> ("Not supported:", t)
        NotExpr t      -> ("Expecting an expression term:", t)
        NotType t      -> ("Expecting a type term: ", t)
        LocalVarOutOfBounds t ->
            ("Local variable reference is out of bounds:", t)
        BadTerm t      -> ("Malformed term:", t)
        CannotCreateDefaultValue t ->
            ("Unable to generate a default value of the given type:", t)
  ppopts <- scGetPPOpts sc
  tm' <- prettyTerm sc tm
  pure $ PPS.renderText ppopts $ msg <+> tm'

data TranslationConfiguration = TranslationConfiguration
  { constantRenaming :: [(String, String)]
  -- ^ A map from 'ImportedName's of constants to names that should be used to
  -- realize them in Lean; primarily used to map Cryptol operators (@||@, @&&@,
  -- etc.) to nicer names on the Lean side, but works on any imported name.
  , constantSkips :: [String]
  -- ^ A list of 'ImportedName's to skip — not translate when encountered. The
  -- consumer is expected to supply their own Lean definitions.
  }

-- | The functional dependency of 'MonadReader' makes it not compositional, so
-- we have to jam together different structures that want to be in the 'Reader'
-- into a single datatype.  This type allows adding extra configuration on top
-- of the translation configuration.
data WithTranslationConfiguration r = WithTranslationConfiguration
  { translationConfiguration :: TranslationConfiguration
  , otherConfiguration :: r
  }

-- | Some computations rely solely on access to the configuration, so we
-- provide it separately.
type TranslationConfigurationMonad r m =
  ( MonadReader (WithTranslationConfiguration r) m
  )

type TranslationMonad r s m =
  ( Except.MonadError TranslationError  m
  , TranslationConfigurationMonad r m
  , MonadState s m
  )

runTranslationMonad ::
  TranslationConfiguration ->
  r ->
  s ->
  (forall m. TranslationMonad r s m => m a) ->
  Either TranslationError (a, s)
runTranslationMonad configuration r s m =
  runStateT (runReaderT m (WithTranslationConfiguration configuration r)) s
