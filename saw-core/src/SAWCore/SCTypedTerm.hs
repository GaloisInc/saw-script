{- |
Module      : SAWCore.SCTypedTerm
Copyright   : Galois, Inc. 2025
License     : BSD3
Maintainer  : huffman@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module SAWCore.SCTypedTerm
  ( SCTypedTerm -- abstract
  , unsafeSCTypedTerm
  , typedVal
  , typedType
  , typedCtx
  , scTypeCheckWHNF
  , scTypeOfTypedTerm
  , scTypedTermWHNF
  , scGlobalTypedTerm
  ) where

import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap

import SAWCore.Conversion (natConversions)
import SAWCore.Rewriter
import SAWCore.SharedTerm

-- | An abstract datatype pairing a 'Term' with its type.
data SCTypedTerm =
  SCTypedTerm
  Term -- ^ value
  Term -- ^ type
  (IntMap Term) -- ^ typing context

unsafeSCTypedTerm :: Term -> Term -> IntMap Term -> SCTypedTerm
unsafeSCTypedTerm = SCTypedTerm

-- | The raw 'Term' of an 'SCTypedTerm'.
typedVal :: SCTypedTerm -> Term
typedVal (SCTypedTerm trm _ _) = trm

-- | The type of an 'SCTypedTerm' as a 'Term'.
typedType :: SCTypedTerm -> Term
typedType (SCTypedTerm _ typ _) = typ

-- | The typing context of an 'SCTypedTerm', keyed by the 'VarIndex'
-- of each 'VarName' in the term.
typedCtx :: SCTypedTerm -> IntMap Term
typedCtx (SCTypedTerm _ _ ctx) = ctx

-- | Reduce the given 'Term' to WHNF, using all reductions allowed by
-- the SAWCore type system.
scTypeCheckWHNF :: SharedContext -> Term -> IO Term
scTypeCheckWHNF sc t =
  do (_, t') <- rewriteSharedTerm sc (addConvs natConversions emptySimpset :: Simpset ()) t
     scWhnf sc t'

-- | Compute the type of an 'SCTypedTerm'.
scTypeOfTypedTerm :: SharedContext -> SCTypedTerm -> IO SCTypedTerm
scTypeOfTypedTerm sc (SCTypedTerm _tm tp ctx) =
  do tp_tp <- scTypeOf' sc ctx tp
     pure (SCTypedTerm tp tp_tp ctx)

-- | Reduce an 'SCTypedTerm' to WHNF (see also 'scTypeCheckWHNF').
scTypedTermWHNF :: SharedContext -> SCTypedTerm -> IO SCTypedTerm
scTypedTermWHNF sc (SCTypedTerm tm tp ctx) =
  do tm' <- scTypeCheckWHNF sc tm
     pure (SCTypedTerm tm' tp ctx)

scGlobalTypedTerm :: SharedContext -> Ident -> IO SCTypedTerm
scGlobalTypedTerm sc ident =
  do tm <- scGlobalDef sc ident
     tp <- scTypeOfIdent sc ident
     pure (SCTypedTerm tm tp IntMap.empty)
