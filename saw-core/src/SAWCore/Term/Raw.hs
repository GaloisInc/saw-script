{- |
Module      : SAWCore.Term.Raw
Copyright   : Galois, Inc. 2012-2025
License     : BSD3
Maintainer  : huffman@galois.com
Stability   : experimental
Portability : non-portable (language extensions)

This module is the low-level internal interface to the SAWCore 'Term'
type, and exposes the data type implementation.

Using this interface directly, it is possible to violate internal
'Term' invariants and break the soundness of SAWCore type system; do
so at your own risk!

-}

module SAWCore.Term.Raw
  ( Term(..)
  , TermIndex
  , unwrapTermF
  , termIndex
  , termSortOrType
  , alphaEquiv
  , varTypes
  , freeVars
  , closedTerm
  ) where

import qualified Data.Foldable as Foldable (and)
import Data.Hashable
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet)

import Instances.TH.Lift () -- for instance TH.Lift Text

import SAWCore.Name
import SAWCore.Term.Functor

-- Term Datatype ---------------------------------------------------------------

type TermIndex = Int -- Word64

-- | Dependently-typed SAWCore terms.
-- 'Term's are represented as directed acyclic graphs: Every 'Term' is
-- labeled with a unique 'TermIndex' to allow recognition of repeated
-- subterms.
-- Every 'Term' is also labeled with its type, as well as the types of
-- all the free variables it contains.
--
-- For more information on the semantics of 'Term's, see the
-- [manual](https://saw.galois.com/manual.html).
-- 'Term' and 'TermF' are split into two structures to facilitate
-- mutual structural recursion (sometimes referred to as the
-- ["knot-tying"](https://wiki.haskell.org/Tying_the_Knot) pattern,
-- sometimes referred to in terms of ["recursion
-- schemes"](https://blog.sumtypeofway.com/posts/introduction-to-recursion-schemes.html))
-- and term object reuse via hash-consing.
data Term
  = STApp
    -- ^ This constructor \"wraps\" a 'TermF' 'Term', assigning it a
    -- guaranteed-unique integer identifier and caching its likely-unique hash.
    -- 'Term's are constructed via 'STApp'. When a fresh 'TermF' is evinced
    -- in the course of a SAW invocation and needs to be lifted into a 'Term',
    -- we can see if we've already created a 'Term' wrapper for an identical
    -- 'TermF', and reuse it if so. The implementation of hash-consed 'Term'
    -- construction exists in 'SAWCore.SharedTerm', in particular in the
    -- 'SAWCore.SharedTerm.scTermF' field of the
    -- t'SAWCore.SharedTerm.SharedContext' object.
     { stAppIndex    :: {-# UNPACK #-} !TermIndex
       -- ^ The UID associated with a 'Term'. It is guaranteed unique across a
       -- universe of properly-constructed 'Term's within a single SAW
       -- invocation.
     , stAppHash     :: {-# UNPACK #-} !Int
       -- ^ The hash, according to 'hash', of the 'stAppTermF' field associated
       -- with this 'Term'. This should be as unique as a hash can be, but is
       -- not guaranteed unique as 'stAppIndex' is.
     , stAppVarTypes :: !(IntMap Term)
       -- ^ A map relating the 'VarIndex' of each free 'Variable' in
       -- the term to the type attached to the 'Variable' constructor.
       -- As an invariant, all free occurrences of the same variable
       -- must be tagged with the same type.
     , stAppTermF    :: !(TermF Term)
       -- ^ The underlying 'TermF' that this 'Term' wraps. This field "ties the
       -- knot" of the 'Term'/'TermF' recursion scheme.
     , stAppType     :: !(Either Sort Term)
       -- ^ The type of this term, represented a 'Sort' or another 'Term'.
       -- Invariant: This field must never contain a 'Right' with a term
       -- that is a 'Sort'; if the type is a 'Sort' then 'Left' is required.
       -- Making 'Sort' a special case lets us avoid storing an infinite
       -- tower of types inside every term.
     }
  deriving (Show)

instance Hashable Term where
  -- The hash of an 'STApp' depends on its not-necessarily-unique
  -- 'stAppHash' instead of its necessarily-unique 'stAppIndex'.
  -- The reason is that per #1830 (PR) and #1831 (issue), we want to
  -- to derive references to terms based solely on their shape.
  -- Indices have nothing to do with a term's shape - they're assigned
  -- sequentially when building terms, according to the (arbitrary)
  -- order in which a term is built.
  -- As for uniqueness, though hashing a term based on its subterms'
  -- hashes introduces less randomness/freshness, it maintains plenty,
  -- and provides benefits as described above.
  -- No code should ever rely on total uniqueness of hashes, and terms
  -- are no exception.
  --
  -- Note: Nevertheless, we do take some minor liberties with the
  -- contract of 'hashWithSalt'. The contract states that if two
  -- values are equal according to '(==)', then they must have the
  -- same hash.
  -- For terms constructed by/within SAW, this will hold, because
  -- SAW's handling of index generation and assignment ensures that
  -- equality of indices implies equality of terms and term hashes
  -- (see 'SAWCore.SharedTerm.getTerm').
  -- However, if terms are constructed outside this standard procedure
  -- or in a way that does not respect index uniqueness rules,
  -- 'hashWithSalt''s contract could be violated.
  hash STApp{ stAppHash = h } = h
  hashWithSalt salt = hashWithSalt salt . hash

instance Eq Term where
  (==) = equalTerm

equalTerm :: Term -> Term -> Bool
equalTerm (STApp{stAppIndex = i1, stAppHash = h1, stAppTermF = tf1, stAppType = mty1})
          (STApp{stAppIndex = i2, stAppHash = h2, stAppTermF = tf2, stAppType = mty2}) =
  i1 == i2 || (h1 == h2 && tf1 == tf2 && mty1 == mty2)
  -- The hash check (^) is merely an optimization that enables us to
  -- quickly return 'False' in most cases. Since we're assuming the
  -- contract of 'hashWithSalt' holds, then we know @tf1 == tf2@
  -- implies @h1 == h2@. Thus we could safely remove @h1 == h2@ without
  -- changing the behavior of this function, but keeping it in enables
  -- us to utilize the fact that we save 'STApp' hashes to get away
  -- with not traversing the 'stAppTermF' fields in most cases of
  -- inequality.

-- | Return 'True' iff the given terms are equal modulo alpha equivalence (i.e.
-- 'VarName's in 'Lambda' and 'Pi' expressions).
-- The types of the terms are not inspected.
alphaEquiv :: Term -> Term -> Bool
alphaEquiv = term IntMap.empty
  where
    term :: IntMap VarIndex -> Term -> Term -> Bool
    term vm
      (STApp{stAppIndex = i1, stAppTermF = tf1, stAppVarTypes = vt1})
      (STApp{stAppIndex = i2, stAppTermF = tf2}) =
      (IntMap.disjoint vt1 vm && i1 == i2) || termf vm tf1 tf2

    termf :: IntMap VarIndex -> TermF Term -> TermF Term -> Bool
    termf vm (FTermF ftf1) (FTermF ftf2) = ftermf vm ftf1 ftf2
    termf vm (App t1 u1) (App t2 u2) = term vm t1 t2 && term vm u1 u2
    termf vm (Lambda (vnIndex -> i1) t1 u1) (Lambda (vnIndex -> i2) t2 u2) =
      let vm' = if i1 == i2 then vm else IntMap.insert i1 i2 vm
      in term vm t1 t2 && term vm' u1 u2
    termf vm (Pi (vnIndex -> i1) t1 u1) (Pi (vnIndex -> i2) t2 u2) =
      let vm' = if i1 == i2 then vm else IntMap.insert i1 i2 vm
      in term vm t1 t2 && term vm' u1 u2
    termf _vm (Constant x1) (Constant x2) = x1 == x2
    termf vm (Variable x1 _t1) (Variable x2 _t2) =
      case IntMap.lookup (vnIndex x1) vm of
        Just i -> vnIndex x2 == i
        Nothing -> x1 == x2
    termf _ FTermF{}   _ = False
    termf _ App{}      _ = False
    termf _ Lambda{}   _ = False
    termf _ Pi{}       _ = False
    termf _ Constant{} _ = False
    termf _ Variable{} _ = False

    ftermf :: IntMap Int -> FlatTermF Term -> FlatTermF Term -> Bool
    ftermf vm ftf1 ftf2 =
      case zipWithFlatTermF (term vm) ftf1 ftf2 of
        Nothing -> False
        Just ftf3 -> Foldable.and ftf3

-- | Inspect the form of a 'Term' as a 'TermF'.
unwrapTermF :: Term -> TermF Term
unwrapTermF STApp{ stAppTermF = tf } = tf

-- | Return the unique 'TermIndex' of the given 'Term'.
--
-- We maintain the invariant that indexes are globally unique, so
-- @termIndex t1 == termIndex t2@ implies that @t1@ and @t2@ are the
-- same Haskell object.
--
-- Note that term equality according to the 'Eq' instance is weaker
-- than index equality: We allow terms such that @t1 == t2@ and
-- @termIndex t1 /= termIndex t2@.
termIndex :: Term -> TermIndex
termIndex STApp{ stAppIndex = i } = i

-- | Return the type tagged on the given 'Term'.
-- Return a 'Left' constructor if and only if the type is a 'Sort'.
--
-- Note that in the SAWCore type system, the type of the type of any
-- term is always a 'Sort' (or a 'Term' that reduces to a 'Sort').
-- So representing the type tag as an 'Either' ensures that that we
-- never need an infinitely-nested tower of types inside a 'Term'.
termSortOrType :: Term -> Either Sort Term
termSortOrType STApp{ stAppType = ty } = ty

instance Ord Term where
  compare (STApp{stAppIndex = i}) (STApp{stAppIndex = j}) | i == j = EQ
  compare x y = compare (unwrapTermF x) (unwrapTermF y)

-- Free Variables --------------------------------------------------------------

-- | Return an 'IntMap' relating the 'VarIndex' of each free variable
-- of a term to its type.
varTypes :: Term -> IntMap Term
varTypes STApp{ stAppVarTypes = vt } = vt

-- | Return an 'IntSet' containing the 'VarIndex' of all free
-- variables in the 'Term'.
freeVars :: Term -> IntSet
freeVars t = IntMap.keysSet (varTypes t)

-- | Test whether a 'Term' is closed, i.e., it has no free variables.
closedTerm :: Term -> Bool
closedTerm t = IntMap.null (varTypes t)
