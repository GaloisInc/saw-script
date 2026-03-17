{-# LANGUAGE OverloadedStrings #-}

{- |
Module      : CryptolSAWCore.TypedTerm
Description : SAWCore terms paired with Cryptol types.
License     : BSD3
Maintainer  : saw@galois.com
Stability   : provisional
Portability : default
-}

module CryptolSAWCore.TypedTerm (
    TypedTerm(..),
    TypedTermType(..),

    prettyTypedTerm,
    prettyTypedTermType,
    prettyTypedTermPure,
    prettyTypedTermTypePure,
    prettyTypedVariable,
    ppTypedTermType,
    ppTypedTermTypePure,
    ppTypedTerm,
    ppTypedTermPure,
    -- (note: there's no downstream use for ppTypedVariable so it isn't provided)

    ttTypeAsTerm,
    ttTermLens,
    ttIsMono,
    mkTypedTerm,
    applyTypedTerms,
    typedTermOfFirstOrderValue,

    TypedVariable(..),
    asTypedVariable,
    typedTermOfVariable,
    abstractTypedVars,

    CryptolModule(..),
    prettyCryptolModule
  ) where

import Control.Monad (foldM)
import Data.Text (Text)
import Data.Map (Map)
import qualified Data.Map as Map

import qualified Prettyprinter as PP
import Prettyprinter ((<+>))

import Cryptol.ModuleSystem.Name (nameIdent)
import qualified Cryptol.TypeCheck.AST as C
import qualified Cryptol.Utils.Ident as C (mkIdent)
import qualified Cryptol.Utils.RecordMap as C (recordFromFields)

import qualified SAWSupport.Pretty as PPS (Opts, defaultOpts, renderText)

import qualified CryptolSAWCore.Pretty as CryPP
import CryptolSAWCore.Cryptol (scCryptolType, CryptolEnv, importKind, importSchema)
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


-- | The different notions of Cryptol types that a SAWCore term might
--   have. Kinds, types, and values are stratified in Cryptol, but not
--   in SAWCore because SAWCore is dependently typed.
--
data TypedTermType
  = TypedTermSchema C.Schema
  | TypedTermKind   C.Kind
  | TypedTermOther  Term
 deriving Show


-- It is not ideal to have two copies of these but it's not that
-- helpful to try to share. In the long run the pure ones should
-- probably go away as they produce worse output.

-- | Print a `TypedTerm` to a `PP.Doc`.
prettyTypedTerm :: SharedContext -> PPS.Opts -> TypedTerm -> IO (PP.Doc ann)
prettyTypedTerm sc opts (TypedTerm tp tm) = do
  tm' <- prettyTerm sc opts tm
  tp' <- prettyTypedTermType sc opts tp
  pure $ PP.unAnnotate tm' <+> ":" <+> tp'

-- | Print a `TypedTermType` to a `PP.Doc`.
prettyTypedTermType :: SharedContext -> PPS.Opts -> TypedTermType -> IO (PP.Doc ann)
prettyTypedTermType _sc _opts (TypedTermSchema sch) =
  pure $ CryPP.pretty sch
prettyTypedTermType _sc _opts (TypedTermKind k) =
  pure $ CryPP.pretty k
prettyTypedTermType sc opts (TypedTermOther tp) = do
  tp' <- prettyTerm sc opts tp
  pure $ PP.unAnnotate tp'

-- | Print a `TypedTerm` to a `PP.Doc`, without needing the
--   `SharedContext` or `IO`.
--
--   This produces inferior output at the SAWCore level. See `prettyTermPure`.
--
prettyTypedTermPure :: TypedTerm -> PP.Doc ann
prettyTypedTermPure (TypedTerm tp tm) =
  PP.unAnnotate (prettyTermPure PPS.defaultOpts tm)
  <+> ":" <+>
  prettyTypedTermTypePure tp

-- | Print a `TypedTermType` to a `PP.Doc`, without needing the
--   `SharedContext` or `IO`.
--
--   This produces inferior output at the SAWCore level. See `prettyTermPure`.
--
prettyTypedTermTypePure :: TypedTermType -> PP.Doc ann
prettyTypedTermTypePure (TypedTermSchema sch) =
  CryPP.pretty sch
prettyTypedTermTypePure (TypedTermKind k) =
  CryPP.pretty k
prettyTypedTermTypePure (TypedTermOther tp) =
  PP.unAnnotate (prettyTermPure PPS.defaultOpts tp)

-- | Print a `TypedVariable` to a `PP.Doc`.
prettyTypedVariable :: TypedVariable -> PP.Doc ann
prettyTypedVariable (TypedVariable ctp vn _tp) =
  PP.unAnnotate (PP.pretty (vnName vn))
  <+> ":" <+>
  CryPP.pretty ctp

-- | Print a `TypedTermType` to `Text`.
ppTypedTermType :: SharedContext -> PPS.Opts -> TypedTermType -> IO Text
ppTypedTermType sc opts ty =
  PPS.renderText opts <$> prettyTypedTermType sc opts ty

-- | Print a `TypedTermType` to `Text`, without needing the
--   `SharedContext` or `IO`.
--
--   This produces inferior output at the SAWCore level. See `prettyTermPure`.
--
ppTypedTermTypePure :: PPS.Opts -> TypedTermType -> Text
ppTypedTermTypePure opts ty =
  PPS.renderText opts $ prettyTypedTermTypePure ty

-- | Print a `TypedTerm` to `Text`.
ppTypedTerm :: SharedContext -> PPS.Opts -> TypedTerm -> IO Text
ppTypedTerm sc opts ty =
  PPS.renderText opts <$> prettyTypedTerm sc opts ty

-- | Print a `TypedTermType` to `Text`, without needing the
--   `SharedContext` or `IO`.
--
--   This produces inferior output at the SAWCore level. See `prettyTermPure`.
--
ppTypedTermPure :: PPS.Opts -> TypedTerm -> Text
ppTypedTermPure opts t =
  PPS.renderText opts $ prettyTypedTermPure t


-- | Convert the 'ttType' field of a 'TypedTerm' to a SAW core term
ttTypeAsTerm :: SharedContext -> CryptolEnv -> TypedTerm -> IO Term
ttTypeAsTerm sc env (TypedTerm (TypedTermSchema schema) _) =
  importSchema sc env schema
ttTypeAsTerm sc _ (TypedTerm (TypedTermKind k) _) = importKind sc k
ttTypeAsTerm _ _ (TypedTerm (TypedTermOther tp) _) = return tp

ttTermLens :: Functor f => (Term -> f Term) -> TypedTerm -> f TypedTerm
ttTermLens f tt = tt `seq` fmap (\x -> tt{ttTerm = x}) (f (ttTerm tt))

-- | Check if a `TypedTermType` is monomorphic and if so return its type.
ttIsMono :: TypedTermType -> Maybe C.Type
ttIsMono ttp =
  case ttp of
    TypedTermSchema sch -> C.isMono sch
    _ -> Nothing

-- | Cons a `TypedTerm` from a `Term` by attempting to lift its
--   SAWCore type back to Cryptol. See `scCryptolType`.
mkTypedTerm :: SharedContext -> Term -> IO TypedTerm
mkTypedTerm sc trm = do
  ty <- scTypeOf sc trm
  ct <- scCryptolType sc ty
  let ttt = case ct of
        Nothing        -> TypedTermOther ty
        Just (Left k)  -> TypedTermKind k
        Just (Right t) -> TypedTermSchema (C.tMono t)
  return (TypedTerm ttt trm)

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

-- First order types and values ------------------------------------------------

-- | Convert a `FirstOrderType` to a Cryptol `C.Type`.
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

-- | Convert a `FirstOrderValue` to a `TypedTerm`.
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
    (Map C.Name C.TySyn)    -- ^ type synonyms
    (Map C.Name TypedTerm)  -- ^ symbols (mapping to SAWCore things).

-- | Print a `CryptolModule` (module handle).
prettyCryptolModule :: CryptolModule -> PP.Doc ann
prettyCryptolModule (CryptolModule sm tm) =
  let prettyTSyn (C.TySyn name params _props rhs _doc) =
        let name' = CryPP.pretty (nameIdent name)
            params' = map CryPP.pretty params
            rhs' = CryPP.pretty rhs
        in
        PP.indent 4 $ PP.hsep (name' : params') <+> "=" <+> rhs'

      prettyBinding (name, TypedTerm (TypedTermSchema schema) _) =
        let name' = CryPP.pretty (nameIdent name)
            schema' = CryPP.pretty schema
        in
        [PP.indent 4 $ name' <+> ":" <+> schema']
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
