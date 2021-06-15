{- |
Module      : SAWScript.TypedTerm
Description : SAW-Core terms paired with Cryptol types.
License     : BSD3
Maintainer  : huffman
Stability   : provisional
-}
{-# LANGUAGE PatternGuards #-}
module Verifier.SAW.TypedTerm where

import Control.Monad (foldM)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Text (Text)

import Cryptol.ModuleSystem.Name (nameIdent)
import qualified Cryptol.TypeCheck.AST as C
import Cryptol.Utils.PP (pretty)
import qualified Cryptol.Utils.Ident as C (mkIdent)
import qualified Cryptol.Utils.RecordMap as C (recordFromFields)

import Verifier.SAW.Cryptol (scCryptolType)
import Verifier.SAW.FiniteValue
import Verifier.SAW.Recognizer (asExtCns)
import Verifier.SAW.SharedTerm

-- Typed terms -----------------------------------------------------------------

-- | Within SAWScript, we represent an object language term as a
-- SAWCore shared term paired with a Cryptol type schema. The Cryptol
-- type is used for type inference/checking of inline Cryptol
-- expressions.

data TypedTerm =
  TypedTerm
  { ttType :: TypedTermType
  , ttTerm :: Term
  }
  deriving Show


-- | The different notion of Cryptol types that
--   as SAWCore term might have.
data TypedTermType
  = TypedTermSchema C.Schema
  | TypedTermKind   C.Kind
  | TypedTermOther  Term
 deriving Show


ttTermLens :: Functor f => (Term -> f Term) -> TypedTerm -> f TypedTerm
ttTermLens f tt = tt `seq` fmap (\x -> tt{ttTerm = x}) (f (ttTerm tt))

ttIsMono :: TypedTermType -> Maybe C.Type
ttIsMono ttp =
  case ttp of
    TypedTermSchema sch -> C.isMono sch
    _ -> Nothing

mkTypedTerm :: SharedContext -> Term -> IO TypedTerm
mkTypedTerm sc trm = do
  ty <- scTypeOf sc trm
  ct <- scCryptolType sc ty
  let ttt = case ct of
        Nothing        -> TypedTermOther ty
        Just (Left k)  -> TypedTermKind k
        Just (Right t) -> TypedTermSchema (C.tMono t)
  return (TypedTerm ttt trm)

-- | Apply a function-typed 'TypedTerm' to an argument. This operation
-- fails if the first 'TypedTerm' does not have a monomorphic function
-- type.
applyTypedTerm :: SharedContext -> TypedTerm -> TypedTerm -> IO TypedTerm
applyTypedTerm sc (TypedTerm tp t1) (TypedTerm _ t2)
  | Just (_,cty') <- C.tIsFun =<< ttIsMono tp
  = TypedTerm (TypedTermSchema (C.tMono cty')) <$> scApply sc t1 t2

-- TODO? extend this to allow explicit application of types?
applyTypedTerm _ _ _ = fail "applyTypedTerm: not a (monomorphic) function type"

-- | Apply a 'TypedTerm' to a list of arguments. This operation fails
-- if the first 'TypedTerm' does not have a function type of
-- sufficient arity.
applyTypedTerms :: SharedContext -> TypedTerm -> [TypedTerm] -> IO TypedTerm
applyTypedTerms sc = foldM (applyTypedTerm sc)

-- | Create an abstract defined constant with the specified name and body.
defineTypedTerm :: SharedContext -> Text -> TypedTerm -> IO TypedTerm
defineTypedTerm sc name (TypedTerm schema t) =
  do ty <- scTypeOf sc t
     TypedTerm schema <$> scConstant sc name t ty

-- | Make a tuple value from a list of 'TypedTerm's. This operation
-- fails if any 'TypedTerm' in the list has a polymorphic type.
tupleTypedTerm :: SharedContext -> [TypedTerm] -> IO TypedTerm
tupleTypedTerm sc tts =
  case traverse (ttIsMono . ttType) tts of
    Nothing -> fail "tupleTypedTerm: invalid polymorphic term"
    Just ctys ->
      TypedTerm (TypedTermSchema (C.tMono (C.tTuple ctys))) <$>
        scTuple sc (map ttTerm tts)

-- | Given a 'TypedTerm' with a tuple type, return a list of its
-- projected components. This operation fails if the 'TypedTerm' does
-- not have a tuple type.
destTupleTypedTerm :: SharedContext -> TypedTerm -> IO [TypedTerm]
destTupleTypedTerm sc (TypedTerm tp t) =
  case C.tIsTuple =<< ttIsMono tp of
    Nothing -> fail "asTupleTypedTerm: not a tuple type"
    Just ctys ->
      do let len = length ctys
         let idxs = take len [1 ..]
         ts <- traverse (\i -> scTupleSelector sc t i len) idxs
         pure $ zipWith TypedTerm (map (TypedTermSchema . C.tMono) ctys) ts

-- First order types and values ------------------------------------------------

cryptolTypeOfFirstOrderType :: FirstOrderType -> C.Type
cryptolTypeOfFirstOrderType fot =
  case fot of
    FOTBit -> C.tBit
    FOTInt -> C.tInteger
    FOTIntMod n -> C.tIntMod (C.tNum n)
    FOTVec n t -> C.tSeq (C.tNum n) (cryptolTypeOfFirstOrderType t)
    -- NB, special case, don't produce 1-tuples
    FOTTuple [x] -> cryptolTypeOfFirstOrderType x
    FOTTuple ts -> C.tTuple (map cryptolTypeOfFirstOrderType ts)
    FOTArray a b ->
      C.tArray
      (cryptolTypeOfFirstOrderType a)
      (cryptolTypeOfFirstOrderType b)
    FOTRec m ->
      C.tRec $
      C.recordFromFields $
      [ (C.mkIdent l, cryptolTypeOfFirstOrderType t)
      | (l, t) <- Map.assocs m ]

typedTermOfFirstOrderValue :: SharedContext -> FirstOrderValue -> IO TypedTerm
typedTermOfFirstOrderValue sc fov =
  do let fot = firstOrderTypeOf fov
     let cty = cryptolTypeOfFirstOrderType fot
     t <- scFirstOrderValue sc fov
     pure $ TypedTerm (TypedTermSchema (C.tMono cty)) t

-- Typed external constants ----------------------------------------------------

data TypedExtCns =
  TypedExtCns
  { tecType :: C.Type
  , tecExt :: ExtCns Term
  }
  deriving Show

-- | Recognize 'TypedTerm's that are external constants.
asTypedExtCns :: TypedTerm -> Maybe TypedExtCns
asTypedExtCns (TypedTerm tp t) =
  do cty <- ttIsMono tp
     ec <- asExtCns t
     pure $ TypedExtCns cty ec

-- | Make a 'TypedTerm' from a 'TypedExtCns'.
typedTermOfExtCns :: SharedContext -> TypedExtCns -> IO TypedTerm
typedTermOfExtCns sc (TypedExtCns cty ec) =
  TypedTerm (TypedTermSchema (C.tMono cty)) <$> scExtCns sc ec

abstractTypedExts :: SharedContext -> [TypedExtCns] -> TypedTerm -> IO TypedTerm
abstractTypedExts sc tecs (TypedTerm (TypedTermSchema (C.Forall params props ty)) trm) =
  do let tys = map tecType tecs
     let exts = map tecExt tecs
     let ty' = foldr C.tFun ty tys
     trm' <- scAbstractExts sc exts trm
     pure $ TypedTerm (TypedTermSchema (C.Forall params props ty')) trm'
abstractTypedExts sc tecs (TypedTerm (TypedTermKind k) trm) =
  do let exts = map tecExt tecs
     trm' <- scAbstractExts sc exts trm
     pure $ TypedTerm (TypedTermKind k) trm'
abstractTypedExts sc tecs (TypedTerm (TypedTermOther _tp) trm) =
  do let exts = map tecExt tecs
     trm' <- scAbstractExts sc exts trm
     tp'  <- scTypeOf sc trm'
     pure $ TypedTerm (TypedTermOther tp') trm'

-- Typed modules ---------------------------------------------------------------

-- | In SAWScript, we can refer to a Cryptol module as a first class
-- value. These are represented simply as maps from names to typed
-- terms.

data CryptolModule =
  CryptolModule (Map C.Name C.TySyn) (Map C.Name TypedTerm)

showCryptolModule :: CryptolModule -> String
showCryptolModule (CryptolModule sm tm) =
  unlines $
    (if Map.null sm then [] else
       "Type Synonyms" : "=============" : map showTSyn (Map.elems sm) ++ [""]) ++
    "Symbols" : "=======" : concatMap showBinding (Map.assocs tm)
  where
    showTSyn (C.TySyn name params _props rhs _doc) =
      "    " ++ unwords (pretty (nameIdent name) : map pretty params) ++ " = " ++ pretty rhs

    showBinding (name, TypedTerm (TypedTermSchema schema) _) =
      ["    " ++ pretty (nameIdent name) ++ " : " ++ pretty schema]
    showBinding _ =
      []
