{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}

{- |
Module      : Verifier.SAW.Module
Copyright   : Galois, Inc. 2012-2017
License     : BSD3
Maintainer  : huffman@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module Verifier.SAW.Module
  ( -- * Patterns.
    Pat(..)
  , patBoundVars
  , patBoundVarCount
  , patUnusedVarCount
    -- * Data types and definitions.
  , DefQualifier(..)
  , Def(..)
  , DefEqn(..)
  , Ctor(..)
  , DataType(..)
  ) where

import Control.Lens
#if !MIN_VERSION_base(4,8,0)
import Data.Foldable (Foldable)
#endif
import Data.Hashable
import GHC.Generics (Generic)

import Prelude hiding (all, foldr, sum)

import Verifier.SAW.Term.Functor
import Verifier.SAW.Utils (sumBy)

-- Patterns --------------------------------------------------------------------

-- Patterns are used to match equations.
data Pat e = -- | Variable bound by pattern.
             -- Variables may be bound in context in a different order than
             -- a left-to-right traversal.  The DeBruijnIndex indicates the order.
             PVar String DeBruijnIndex e
             -- | The
           | PUnused DeBruijnIndex e
           | PUnit
           | PPair (Pat e) (Pat e)
           | PEmpty
           | PField (Pat e) (Pat e) (Pat e) -- ^ Field name, field value, rest of record
           | PString String
           | PCtor Ident [Pat e]
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Generic)

instance Hashable e => Hashable (Pat e) -- automatically derived

patBoundVarCount :: Pat e -> DeBruijnIndex
patBoundVarCount p =
  case p of
    PVar{} -> 1
    PUnused{} -> 0
    PCtor _ l -> sumBy patBoundVarCount l
    PUnit     -> 0
    PPair x y -> patBoundVarCount x + patBoundVarCount y
    PEmpty    -> 0
    PField f x y -> patBoundVarCount f + patBoundVarCount x + patBoundVarCount y
    PString _ -> 0

patUnusedVarCount :: Pat e -> DeBruijnIndex
patUnusedVarCount p =
  case p of
    PVar{}       -> 0
    PUnused{}    -> 1
    PCtor _ l    -> sumBy patUnusedVarCount l
    PUnit        -> 0
    PPair x y    -> patUnusedVarCount x + patUnusedVarCount y
    PEmpty       -> 0
    PField _ x y -> patUnusedVarCount x + patUnusedVarCount y
    PString _    -> 0

patBoundVars :: Pat e -> [String]
patBoundVars p =
  case p of
    PVar s _ _   -> [s]
    PCtor _ l    -> concatMap patBoundVars l
    PUnit        -> []
    PPair x y    -> patBoundVars x ++ patBoundVars y
    PEmpty       -> []
    PField _ x y -> patBoundVars x ++ patBoundVars y
    PString _    -> []
    PUnused{}    -> []


-- Definitions -----------------------------------------------------------------

data DefQualifier
  = NoQualifier
  | PrimQualifier
  | AxiomQualifier
 deriving (Eq, Show, Generic)

instance Hashable DefQualifier -- automatically derived

-- | A Definition contains an identifier, the type of the definition, and a list of equations.
data Def =
  Def
  { defIdent :: Ident
  , defQualifier :: DefQualifier
  , defType :: Term
  , defEqs :: [DefEqn]
  }
  deriving (Eq, Show, Generic)

instance Hashable Def -- automatically derived

data DefEqn
  = DefEqn [Pat Term] Term -- ^ List of patterns and a right hand side
  deriving (Eq, Show, Generic)

instance Hashable DefEqn -- automatically derived


-- Constructors ----------------------------------------------------------------

data Ctor tp =
  Ctor
  { ctorName :: !Ident
  , ctorType :: tp -- ^ The type of the constructor (should contain no free variables).
  }
  deriving (Functor, Foldable, Traversable)

lift2 :: (a -> b) -> (b -> b -> c) -> a -> a -> c
lift2 f h x y = h (f x) (f y)

instance Eq (Ctor tp) where
  (==) = lift2 ctorName (==)

instance Ord (Ctor tp) where
  compare = lift2 ctorName compare

instance Show (Ctor tp) where
  show = show . ctorName


-- Datatypes -------------------------------------------------------------------

data DataType =
  DataType
  { dtName :: Ident
  , dtType :: Term
  , dtCtors :: [Ctor Term]
  , dtIsPrimitive :: Bool
  }

instance Eq DataType where
  (==) = lift2 dtName (==)

instance Ord DataType where
  compare = lift2 dtName compare

instance Show DataType where
  show = show . dtName
