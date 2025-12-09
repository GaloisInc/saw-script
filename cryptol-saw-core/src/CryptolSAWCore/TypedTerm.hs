{-# LANGUAGE OverloadedStrings #-}
{- |
Module      : CryptolSAWCore.TypedTerm
Description : SAW-Core terms paired with Cryptol types.
License     : BSD3
Maintainer  : huffman
Stability   : provisional
-}

module CryptolSAWCore.TypedTerm
 -- prettyTypedTerm,
 -- prettyTypedTermType,
 -- prettyTypedTermPure,
 -- prettyTypedTermTypePure,
 -- prettyTypedVariable,
 where

import Control.Monad (foldM)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Text (Text)

import qualified Prettyprinter as PP

import Cryptol.ModuleSystem.Name (nameIdent)
import qualified Cryptol.TypeCheck.AST as C
import qualified Cryptol.Utils.PP as C (pp, ppPrec)
import qualified Cryptol.Utils.Ident as C (mkIdent)
import qualified Cryptol.Utils.RecordMap as C (recordFromFields)

import qualified SAWSupport.Pretty as PPS (Opts, defaultOpts)

import CryptolSAWCore.Cryptol (scCryptolType, Env, importKind, importSchema)
import SAWCore.FiniteValue
import SAWCore.Name (VarName(..))
import SAWCore.Recognizer (asVariable)
import SAWCore.SharedTerm
import SAWCore.Term.Pretty (prettyTermPure)

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


-- It is not ideal to have two copies of these but it's not that
-- helpful to try to share. In the long run the pure ones should
-- probably go away as they produce worse output.

prettyTypedTerm :: SharedContext -> PPS.Opts -> TypedTerm -> IO (PP.Doc ann)
prettyTypedTerm sc opts (TypedTerm tp tm) = do
  tm' <- prettyTerm sc opts tm
  tp' <- prettyTypedTermType sc opts tp
  pure $ PP.unAnnotate tm' PP.<+> ":" PP.<+> tp'

prettyTypedTermType :: SharedContext -> PPS.Opts -> TypedTermType -> IO (PP.Doc ann)
prettyTypedTermType _sc _opts (TypedTermSchema sch) =
  pure $ PP.viaShow (C.ppPrec 0 sch)
prettyTypedTermType _sc _opts (TypedTermKind k) =
  pure $ PP.viaShow (C.ppPrec 0 k)
prettyTypedTermType sc opts (TypedTermOther tp) = do
  tp' <- prettyTerm sc opts tp
  pure $ PP.unAnnotate tp'

prettyTypedTermPure :: TypedTerm -> PP.Doc ann
prettyTypedTermPure (TypedTerm tp tm) =
  PP.unAnnotate (prettyTermPure PPS.defaultOpts tm)
  PP.<+> ":" PP.<+>
  prettyTypedTermTypePure tp

prettyTypedTermTypePure :: TypedTermType -> PP.Doc ann
prettyTypedTermTypePure (TypedTermSchema sch) =
  PP.viaShow (C.ppPrec 0 sch)
prettyTypedTermTypePure (TypedTermKind k) =
  PP.viaShow (C.ppPrec 0 k)
prettyTypedTermTypePure (TypedTermOther tp) =
  PP.unAnnotate (prettyTermPure PPS.defaultOpts tp)

prettyTypedVariable :: TypedVariable -> PP.Doc ann
prettyTypedVariable (TypedVariable ctp vn _tp) =
  PP.unAnnotate (PP.pretty (vnName vn))
  PP.<+> ":" PP.<+>
  PP.viaShow (C.ppPrec 0 ctp)


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
     ty <- scTypeOf sc trm
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
     TypedTerm schema <$> scFreshConstant sc name t ty

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

-- Typed variables -------------------------------------------------------------

data TypedVariable =
  TypedVariable
  { tvCType :: C.Type
  , tvName :: VarName
  , tvType :: Term
  }
  deriving Show

-- | Recognize 'TypedTerm's that are variables.
asTypedVariable :: TypedTerm -> Maybe TypedVariable
asTypedVariable (TypedTerm tp t) =
  do cty <- ttIsMono tp
     (x, ty) <- asVariable t
     pure $ TypedVariable cty x ty

-- | Make a 'TypedTerm' from a 'TypedVariable'.
typedTermOfVariable :: SharedContext -> TypedVariable -> IO TypedTerm
typedTermOfVariable sc (TypedVariable cty vn ty) =
  TypedTerm (TypedTermSchema (C.tMono cty)) <$> scVariable sc vn ty

abstractTypedVars :: SharedContext -> [TypedVariable] -> TypedTerm -> IO TypedTerm
abstractTypedVars sc tvars (TypedTerm (TypedTermSchema (C.Forall params props ty)) trm) =
  do let tys = map tvCType tvars
     let vars = map (\(TypedVariable _ vn tp) -> (vn, tp)) tvars
     let ty' = foldr C.tFun ty tys
     trm' <- scLambdaList sc vars trm
     pure $ TypedTerm (TypedTermSchema (C.Forall params props ty')) trm'
abstractTypedVars sc tvars (TypedTerm (TypedTermKind k) trm) =
  do let vars = map (\(TypedVariable _ vn tp) -> (vn, tp)) tvars
     trm' <- scLambdaList sc vars trm
     pure $ TypedTerm (TypedTermKind k) trm'
abstractTypedVars sc tvars (TypedTerm (TypedTermOther _tp) trm) =
  do let vars = map (\(TypedVariable _ vn tp) -> (vn, tp)) tvars
     trm' <- scLambdaList sc vars trm
     tp'  <- scTypeOf sc trm'
     pure $ TypedTerm (TypedTermOther tp') trm'

-- Typed modules ---------------------------------------------------------------

-- | In SAWScript, we can refer to a Cryptol module as a first class
-- value. These are represented simply as maps from names to typed
-- terms.

data CryptolModule =
  CryptolModule
    (Map C.Name C.TySyn)    -- type synonyms
    (Map C.Name TypedTerm)  -- symbols (mapping to SawCore things).

-- Note: Cryptol's prettyprinter isn't directly compatible with SAW's.
--
-- Also note that its naming conventions are opposite ours; it uses
-- "pp" to make Docs and "pretty" to make Strings.
--
prettyCryptolModule :: CryptolModule -> PP.Doc ann
prettyCryptolModule (CryptolModule sm tm) =
  let cpp item = PP.viaShow $ C.pp item
      prettyTSyn (C.TySyn name params _props rhs _doc) =
        let name' = cpp (nameIdent name)
            params' = map cpp params
            rhs' = cpp rhs
        in
        PP.indent 4 $ PP.hsep (name' : params') PP.<+> "=" PP.<+> rhs'

      prettyBinding (name, TypedTerm (TypedTermSchema schema) _) =
        [PP.indent 4 $ cpp (nameIdent name) PP.<+> ":" PP.<+> cpp schema]
      prettyBinding _ =
        []
      synonyms =
        if Map.null sm then []
        else
            "Type Synonyms" : "=============" : map prettyTSyn (Map.elems sm) ++ [""]
      symbols =
        "Symbols" : "=======" : concatMap prettyBinding (Map.assocs tm)
  in
  PP.vsep $ synonyms ++ symbols
