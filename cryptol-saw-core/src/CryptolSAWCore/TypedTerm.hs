{- |
Module      : CryptolSAWCore.TypedTerm
Description : SAW-Core terms paired with Cryptol types.
License     : BSD3
Maintainer  : huffman
Stability   : provisional
-}
{-# LANGUAGE PatternGuards #-}
module CryptolSAWCore.TypedTerm
 -- ppTypedTerm,
 -- ppTypedTermType,
 -- ppTypedExtCns,
 where

import Control.Monad (foldM)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Text (Text)

import qualified Prettyprinter as PP

import Cryptol.ModuleSystem.Name (nameIdent)
import qualified Cryptol.TypeCheck.AST as C
import qualified Cryptol.Utils.PP as C (pretty, ppPrec)
import qualified Cryptol.Utils.Ident as C (mkIdent)
import qualified Cryptol.Utils.RecordMap as C (recordFromFields)

import qualified SAWSupport.Pretty as PPS (defaultOpts)

import CryptolSAWCore.Cryptol (scCryptolType, Env, importKind, importSchema)
import SAWCore.FiniteValue
import SAWCore.Recognizer (asVariable)
import SAWCore.SharedTerm
import SAWCore.SCTypeCheck (scTypeCheckError)
import SAWCore.Term.Pretty (ppTerm)

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
--   a SAWCore term might have.
data TypedTermType
  = TypedTermSchema C.Schema
  | TypedTermKind   C.Kind
  | TypedTermOther  Term
 deriving Show


ppTypedTerm :: TypedTerm -> PP.Doc ann
ppTypedTerm (TypedTerm tp tm) =
  PP.unAnnotate (ppTerm PPS.defaultOpts tm)
  PP.<+> PP.pretty ":" PP.<+>
  ppTypedTermType tp

ppTypedTermType :: TypedTermType -> PP.Doc ann
ppTypedTermType (TypedTermSchema sch) =
  PP.viaShow (C.ppPrec 0 sch)
ppTypedTermType (TypedTermKind k) =
  PP.viaShow (C.ppPrec 0 k)
ppTypedTermType (TypedTermOther tp) =
  PP.unAnnotate (ppTerm PPS.defaultOpts tp)

ppTypedExtCns :: TypedExtCns -> PP.Doc ann
ppTypedExtCns (TypedExtCns tp ec) =
  PP.unAnnotate (ppName (ecNameInfo ec))
  PP.<+> PP.pretty ":" PP.<+>
  PP.viaShow (C.ppPrec 0 tp)


-- | Convert the 'ttType' field of a 'TypedTerm' to a SAW core term
ttTypeAsTerm :: SharedContext -> Env -> TypedTerm -> IO Term
ttTypeAsTerm sc env (TypedTerm (TypedTermSchema schema) _) =
  importSchema sc env schema
ttTypeAsTerm sc _ (TypedTerm (TypedTermKind k) _) = importKind sc k
ttTypeAsTerm _ _ (TypedTerm (TypedTermOther tp) _) = return tp

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

-- | Apply a function-typed 'TypedTerm' to an argument.
--   This operation fails if the type of the argument does
--   not match the function.
applyTypedTerm :: SharedContext -> TypedTerm -> TypedTerm -> IO TypedTerm
applyTypedTerm sc x y = applyTypedTerms sc x [y]

-- | Apply a 'TypedTerm' to a list of arguments. This operation fails
-- if the first 'TypedTerm' does not have a function type of
-- sufficient arity, or if the types of the arguments do not match
-- the type of the function.
applyTypedTerms :: SharedContext -> TypedTerm -> [TypedTerm] -> IO TypedTerm
applyTypedTerms sc (TypedTerm _ fn) args =
  do trm <- foldM (scApply sc) fn (map ttTerm args)
     ty <- scTypeCheckError sc trm
     -- NB, scCryptolType can behave in strange ways due to the non-injectivity
     -- of the mapping from Cryptol to SAWCore types. Perhaps we would be better
     -- to combine the incoming type information instead of applying and then
     -- reconstructing here.
     ct <- scCryptolType sc ty
     let ttt = case ct of
           Nothing        -> TypedTermOther ty
           Just (Left k)  -> TypedTermKind k
           Just (Right t) -> TypedTermSchema (C.tMono t)
     return (TypedTerm ttt trm)


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
         let idxs = take len [0..]
         ts <- traverse (scTupleSelector sc t) idxs
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

-- Typed named variables -------------------------------------------------------

data TypedExtCns =
  TypedExtCns
  { tecType :: C.Type
  , tecExt :: ExtCns Term
  }
  deriving Show

-- | Recognize 'TypedTerm's that are named variables.
asTypedExtCns :: TypedTerm -> Maybe TypedExtCns
asTypedExtCns (TypedTerm tp t) =
  do cty <- ttIsMono tp
     ec <- asVariable t
     pure $ TypedExtCns cty ec

-- | Make a 'TypedTerm' from a 'TypedExtCns'.
typedTermOfExtCns :: SharedContext -> TypedExtCns -> IO TypedTerm
typedTermOfExtCns sc (TypedExtCns cty ec) =
  TypedTerm (TypedTermSchema (C.tMono cty)) <$> scVariable sc ec

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
      "    " ++ unwords (C.pretty (nameIdent name) : map C.pretty params) ++ " = " ++ C.pretty rhs

    showBinding (name, TypedTerm (TypedTermSchema schema) _) =
      ["    " ++ C.pretty (nameIdent name) ++ " : " ++ C.pretty schema]
    showBinding _ =
      []
