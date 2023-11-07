{- |
Module      : SAWScript.Bisimulation.BisimTheorem
License     : BSD3
Maintainer  : bboston7
Stability   : experimental
-}

module SAWScript.Bisimulation.BisimTheorem
  ( BisimTheorem(..) )
  where

import qualified Cryptol.TypeCheck.Type as C
import Verifier.SAW.TypedTerm ( TypedTerm )

-- | A proved bisimulation theorem.  See the comment at the top of
-- "SAWScript.Bisimulation" for an explanation of some of the terms used here.
data BisimTheorem = BisimTheorem {
    bisimTheoremStateRelation :: TypedTerm
 -- ^ State relation
  , bisimTheoremOutputRelation :: TypedTerm
 -- ^ Output relation
  , bisimTheoremLhs :: TypedTerm
 -- ^ Left hand side of the bisimulation
  , bisimTheoremRhs :: TypedTerm
 -- ^ Right hand side of the bisimulation
  , bisimTheoremOutputType :: C.Type
 -- ^ Output type for the bisimilar terms
  , bisimTheoremLhsStateType :: C.Type
 -- ^ State type for the left term
  , bisimTheoremRhsStateType :: C.Type
 -- ^ State type for the right term
  }
