{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}

{- |
Module      : SAWCoreCoq.Monad
Copyright   : Galois, Inc. 2018
License     : BSD3
Maintainer  : atomb@galois.com
Stability   : experimental
Portability : portable
-}

module SAWCoreCoq.Monad
  ( TranslationConfiguration(..)
  , TranslationConfigurationMonad
  , TranslationMonad
  , TranslationError(..)
  , WithTranslationConfiguration(..)
  , runTranslationMonad
  ) where

import qualified Control.Monad.Except as Except
import Control.Monad.Reader (MonadReader, ReaderT(..))
import Control.Monad.State (MonadState, StateT(..))
import Prelude hiding (fail)

import SAWCore.SharedTerm
-- import SAWCore.Term.CtxTerm
--import SAWCore.Term.Pretty
-- import qualified SAWCore.UntypedAST as Un

data TranslationError a
  = NotSupported a
  | NotExpr a
  | NotType a
  | LocalVarOutOfBounds a
  | BadTerm a
  | CannotCreateDefaultValue a

instance {-# OVERLAPPING #-} Show (TranslationError Term) where
  show = showError showTerm

instance {-# OVERLAPPABLE #-} Show a => Show (TranslationError a) where
  show = showError show

showError :: (a -> String) -> TranslationError a -> String
showError printer err = case err of
  NotSupported a -> "Not supported: " ++ printer a
  NotExpr a      -> "Expecting an expression term: " ++ printer a
  NotType a      -> "Expecting a type term: " ++ printer a
  LocalVarOutOfBounds a -> "Local variable reference is out of bounds: " ++ printer a
  BadTerm a -> "Malformed term: " ++ printer a
  CannotCreateDefaultValue a -> "Unable to generate a default value of the given type: " ++ printer a

data TranslationConfiguration = TranslationConfiguration
  { constantRenaming :: [(String, String)]
  -- ^ A map from 'ImportedName's of constants to names that should be used to
  -- realize them in Coq; this is generally used to map cryptol operators like
  -- @||@ or @&&@ to nicer names in Coq, but works on any imported names
  , constantSkips :: [String]
  -- ^ A list of 'ImportedName's to skip, i.e., not translate when encountered
  , monadicTranslation :: Bool
  -- ^ Whether to wrap everything in a free monad construction.
  -- - Advantage: fixpoints can be readily represented
  -- - Disadvantage: pure computations look more gnarly
  , postPreamble :: String
  -- ^ Text to be concatenated at the end of the Coq preamble, before the code
  -- generated by the translation.  Usually consists of extra file imports,
  -- module imports, scopes openings.
  , vectorModule       :: String
  -- ^ all vector operations will be prepended with this module name, i.e.
  -- "<VectorModule>.append", etc.  So that it can be retargeted easily.
  -- Current provided options are:
  -- - SAWCoreVectorsAsCoqLists
  -- - SAWCoreVectorsAsCoqVectors
  -- Currently considering adding:
  -- - SAWCoreVectorsAsSSReflectSeqs
  }

-- | The functional dependency of 'MonadReader' makes it not compositional, so
-- we have to jam together different structures that want to be in the 'Reader'
-- into a single datatype.  This type allows adding extra configuration on top
-- of the translation configuration.
data WithTranslationConfiguration r = WithTranslationConfiguration
  { translationConfiguration :: TranslationConfiguration
  , otherConfiguration :: r
  }

-- | Some computations will rely solely on access to the configuration, so we
-- provide it separately.
type TranslationConfigurationMonad r m =
  ( MonadReader (WithTranslationConfiguration r) m
  )

type TranslationMonad r s m =
  ( Except.MonadError (TranslationError Term)  m
  , TranslationConfigurationMonad r m
  , MonadState s m
  )

runTranslationMonad ::
  TranslationConfiguration ->
  r ->
  s ->
  (forall m. TranslationMonad r s m => m a) ->
  Either (TranslationError Term) (a, s)
runTranslationMonad configuration r s m =
  runStateT (runReaderT m (WithTranslationConfiguration configuration r)) s
