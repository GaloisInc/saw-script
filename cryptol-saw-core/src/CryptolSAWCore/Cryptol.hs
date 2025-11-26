{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns #-}

{- |
Module      : CryptolSAWCore.Cryptol
Copyright   : Galois, Inc. 2012-2025
License     : BSD3
Maintainer  : huffman@galois.com
Stability   : experimental
Portability : non-portable (language extensions)

This module \'imports\' various Cryptol elements (Name,Expr,...),
translating each to the comparable element of SAWCore.
-}

module CryptolSAWCore.Cryptol
  ( scCryptolType
  , Env(..)
  , emptyEnv

  , isErasedProp
  , proveProp

  , ImportPrimitiveOptions(..)
  , importName
  , importExpr
  , importTopLevelDeclGroups
  , importDeclGroups
  , importType
  , importKind
  , importSchema

  , defaultPrimitiveOptions
  , genCodeForNominalTypes
  , exportValueWithSchema

  ) where

import Control.Monad (foldM, forM, zipWithM, join, when, unless)
import Control.Exception (catch, SomeException)
import Data.Bifunctor (first)
import qualified Data.Foldable as Fold
import Data.List (elemIndex)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Maybe (fromMaybe)
import qualified Data.IntTrie as IntTrie
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Vector as Vector
import GHC.Stack
import Prelude ()
import Prelude.Compat
import Text.URI

-- cryptol
import qualified Cryptol.Eval.Type as TV
import qualified Cryptol.Backend.Monad as V
import qualified Cryptol.Backend.SeqMap as V
import qualified Cryptol.Backend.WordValue as V
import qualified Cryptol.Eval.Value as V
import qualified Cryptol.Eval.Concrete as V
import Cryptol.Eval.Type (evalValType)
import qualified Cryptol.TypeCheck.AST as C
import qualified Cryptol.TypeCheck.Solver.InfNat as C (Nat'(..))
import qualified Cryptol.TypeCheck.Subst as C (Subst, apSubst, listSubst, singleTParamSubst)
import qualified Cryptol.ModuleSystem.Name as C
  (asPrim, nameUnique, nameIdent, nameInfo, NameInfo(..), asLocal)
import qualified Cryptol.Utils.Ident as C
  ( Ident, PrimIdent(..)
  , prelPrim, floatPrim, arrayPrim, suiteBPrim, primeECPrim
  , identText, interactiveName
  , ModPath(..), modPathSplit, ogModule, ogFromParam, Namespace(NSValue)
  , modNameChunksText
  )
import qualified Cryptol.Utils.RecordMap as C
import Cryptol.TypeCheck.Type as C (NominalType(..))
import Cryptol.TypeCheck.TypeOf (fastTypeOf, fastSchemaOf)
import qualified Cryptol.Utils.PP as PP
import Cryptol.Utils.PP (pretty, pp)

-- saw-core
import qualified SAWCore.Simulator.Concrete as SC
import qualified SAWCore.Simulator.Value as SC
import SAWCore.Prim (BitVector(..))
import SAWCore.SharedTerm
import SAWCore.SCTypeCheck               as SC
import SAWCore.Simulator.MonadLazy (force)
import SAWCore.Name (preludeName, Name(..))
import SAWCore.Term.Functor (mkSort, FieldName, LocalName)
import SAWCore.Term.Pretty (showTerm)

-- local modules:
import CryptolSAWCore.Panic

-- Type-check the Prelude and Cryptol modules at compile time
import Language.Haskell.TH
import CryptolSAWCore.Prelude

$(runIO (mkSharedContext >>= \sc ->
          scLoadPreludeModule sc >> scLoadCryptolModule sc >> pure []))

--------------------------------------------------------------------------------

-- | Type Environments
--   SharedTerms are paired with a deferred shift amount for loose variables
data Env = Env
  { envT :: Map Int    Term  -- ^ Type variables are referenced by unique id
  , envE :: Map C.Name Term       -- ^ Term variables are referenced by name
  , envP :: Map C.Prop (Term, [FieldName])
              -- ^ Bound propositions are referenced implicitly by their types
              --   The actual class dictionary we need is obtained by applying the
              --   given field selectors (in reverse order!) to the term.

  , envC :: Map C.Name C.Schema    -- ^ Cryptol type environment

  , envRefPrims :: Map C.PrimIdent C.Expr
  , envPrims :: Map C.PrimIdent Term -- ^ Translations for other primitives
  , envPrimTypes :: Map C.PrimIdent Term -- ^ Translations for primitive types
  }

emptyEnv :: Env
emptyEnv =
  Env Map.empty Map.empty Map.empty Map.empty Map.empty Map.empty Map.empty


-- | bindTParam' - create a binding for a type parameter, returning 3-tuple:
--                 - environment
--                 - the SAWCore kind of the parameter
--                 - the SAWCore term for the type variable.
bindTParam' :: SharedContext -> C.TParam -> Env -> IO (Env, Term, Term)
bindTParam' sc tp env =
  do
  k <- importKind sc (C.tpKind tp)
  v <- scFreshVariable sc (tparamToLocalName tp) k
  return ( env { envT = Map.insert (C.tpUnique tp) v (envT env)
               }
         , v
         , k
         )

-- | bindTParam - create a binding for a type parameter, just return
--                the new environment and the new sawcore type var (as Term).
bindTParam :: SharedContext -> C.TParam -> Env -> IO (Env, Term)
bindTParam sc tp env =
  do
  (e,v,_) <- bindTParam' sc tp env
  return (e,v)


-- | bindName - create a new binding, adding to appropriate
--              environments; return 3-tuple
--               - the updated environment,
--               - the new SAWCore var (as a Term), and
--               - the SAWCore type of the variable.
bindName :: SharedContext -> C.Name -> C.Schema -> Env -> IO (Env,Term,Term)
bindName sc name schema env = do
  ty <- importSchema sc env schema
  v  <- scFreshVariable sc (nameToLocalName name) ty
  let env' = env { envE = Map.insert name v      (envE env)
                 , envC = Map.insert name schema (envC env)
                 }
  return (env', v, ty)

bindProp :: SharedContext -> C.Prop -> Text -> Env -> IO (Env, Term)
bindProp sc prop nm env =
  do
  ty <- importType sc env prop
  v <- scFreshVariable sc nm ty
  return ( env { envP = insertSupers prop [] v (envP env)}
         , v
         )

-- | When we insert a non-erasable prop into the environment, make
--   sure to also insert all its superclasses.  We arrange it so
--   that every class dictionary contains the implementation of its
--   superclass dictionaries, which can be extracted via field projections.
insertSupers ::
  C.Prop ->
  [FieldName] {- Field names to project the associated class (in reverse order) -} ->
  Term ->
  Map C.Prop (Term, [FieldName]) ->
  Map C.Prop (Term, [FieldName])
insertSupers prop fs v m
  -- If the prop is already in the map, stop
  | Just _ <- Map.lookup prop m = m

  -- Insert the prop and check if it has any superclasses that also need to be added
  | otherwise = Map.insert (normalizeProp prop) (v, fs) $ go prop

 where
 super p f t = insertSupers (C.TCon (C.PC p) [t]) (f:fs) v

 go (C.TCon (C.PC p) [t]) =
    case p of
      C.PRing      -> super C.PZero "ringZero" t m
      C.PLogic     -> super C.PZero "logicZero" t m
      C.PField     -> super C.PRing "fieldRing" t m
      C.PIntegral  -> super C.PRing "integralRing" t m
      C.PRound     -> super C.PField "roundField" t . super C.PCmp "roundCmp" t $ m
      C.PCmp       -> super C.PEq "cmpEq" t m
      C.PSignedCmp -> super C.PEq "signedCmpEq" t m
      _ -> m
 go _ = m


-- | We normalize the first argument of 'Literal' class constraints
-- arbitrarily to 'inf', so that we can ignore that parameter when
-- matching dictionaries.
normalizeProp :: C.Prop -> C.Prop
normalizeProp prop
  | Just (_, a) <- C.pIsLiteral prop = C.pLiteral C.tInf a
  | Just (_, a) <- C.pIsLiteralLessThan prop = C.pLiteralLessThan C.tInf a
  | otherwise = prop


--------------------------------------------------------------------------------

importKind :: SharedContext -> C.Kind -> IO Term
importKind sc kind =
  case kind of
    C.KType       -> scISort sc (mkSort 0)
    C.KNum        -> scGlobalApply sc "Cryptol.Num" []
    C.KProp       -> scSort sc (mkSort 0)
    (C.:->) k1 k2 -> join $ scFun sc <$> importKind sc k1 <*> importKind sc k2

importTFun :: SharedContext -> C.TFun -> IO Term
importTFun sc tf =
  case tf of
    C.TCWidth         -> scGlobalDef sc "Cryptol.tcWidth"
    C.TCAdd           -> scGlobalDef sc "Cryptol.tcAdd"
    C.TCSub           -> scGlobalDef sc "Cryptol.tcSub"
    C.TCMul           -> scGlobalDef sc "Cryptol.tcMul"
    C.TCDiv           -> scGlobalDef sc "Cryptol.tcDiv"
    C.TCMod           -> scGlobalDef sc "Cryptol.tcMod"
    C.TCExp           -> scGlobalDef sc "Cryptol.tcExp"
    C.TCMin           -> scGlobalDef sc "Cryptol.tcMin"
    C.TCMax           -> scGlobalDef sc "Cryptol.tcMax"
    C.TCCeilDiv       -> scGlobalDef sc "Cryptol.tcCeilDiv"
    C.TCCeilMod       -> scGlobalDef sc "Cryptol.tcCeilMod"
    C.TCLenFromThenTo -> scGlobalDef sc "Cryptol.tcLenFromThenTo"

-- | Precondition: @not ('isErasedProp' pc)@.
importPC :: SharedContext -> C.PC -> IO Term
importPC sc pc =
  case pc of
    C.PEqual           -> panic "importPC" ["found PEqual"]
    C.PNeq             -> panic "importPC" ["found PNeq"]
    C.PGeq             -> panic "importPC" ["found PGeq"]
    C.PFin             -> panic "importPC" ["found PFin"]
    C.PHas _           -> panic "importPC" ["found PHas"]
    C.PPrime           -> panic "importPC" ["found PPrime"]
    C.PZero            -> scGlobalDef sc "Cryptol.PZero"
    C.PLogic           -> scGlobalDef sc "Cryptol.PLogic"
    C.PRing            -> scGlobalDef sc "Cryptol.PRing"
    C.PIntegral        -> scGlobalDef sc "Cryptol.PIntegral"
    C.PField           -> scGlobalDef sc "Cryptol.PField"
    C.PRound           -> scGlobalDef sc "Cryptol.PRound"
    C.PEq              -> scGlobalDef sc "Cryptol.PEq"
    C.PCmp             -> scGlobalDef sc "Cryptol.PCmp"
    C.PSignedCmp       -> scGlobalDef sc "Cryptol.PSignedCmp"
    C.PLiteral         -> scGlobalDef sc "Cryptol.PLiteral"
    C.PLiteralLessThan -> scGlobalDef sc "Cryptol.PLiteralLessThan"
    C.PAnd             -> panic "importPC" ["found PAnd"]
    C.PTrue            -> panic "importPC" ["found PTrue"]
    C.PFLiteral        -> panic "importPC" ["found PFLiteral"]
    C.PValidFloat      -> panic "importPC" ["found PValidFloat"]

-- | Translate size types to SAW values of type Num, value types to SAW types of sort 0.
importType :: HasCallStack => SharedContext -> Env -> C.Type -> IO Term
importType sc env ty =
  case ty of
    C.TVar tvar ->
      case tvar of
        C.TVFree{} {- Int Kind (Set TVar) Doc -} ->
            panic "importType" [
                "TVFree in TVar is not supported: " <> Text.pack (pretty ty)
            ]
        C.TVBound v -> case Map.lookup (C.tpUnique v) (envT env) of
            Just t -> pure t
            Nothing ->
              panic "importType" [
                  "found TVar that's TVBound but doesn't exist: " <> Text.pack (show $ pp v)
              ]
    C.TUser _ _ t  -> go t -- look through type synonyms
    C.TRec fm ->
      importType sc env (C.tTuple (map snd (C.canonicalFields fm)))

    C.TNominal nt ts ->
      do let s = C.listSubst (zip (map C.TVBound (C.ntParams nt)) ts)
         let n = C.ntName nt
         case ntDef nt of
           C.Struct stru -> go (plainSubst s (C.TRec (C.ntFields stru)))
           C.Enum {} ->
             -- The (parameterized) type should be in the sc env,
             -- just apply types to it:
             scGlobalApply sc (identOfEnumType n) =<< traverse go ts
           C.Abstract
             | Just prim' <- C.asPrim n
             , Just t <- Map.lookup prim' (envPrimTypes env) ->
               scApplyAllBeta sc t =<< traverse go ts
             | True -> panic "importType" [
                           "Unknown primitive type: " <> Text.pack (show n),
                           "Full type: " <> Text.pack (pretty ty)
                       ]

    C.TCon tcon tyargs ->
      case tcon of
        C.TC tc ->
          case tc of
            C.TCNum n    -> scGlobalApply sc "Cryptol.TCNum" =<< sequence [scNat sc (fromInteger n)]
            C.TCInf      -> scGlobalApply sc "Cryptol.TCInf" []
            C.TCBit      -> scBoolType sc
            C.TCInteger  -> scIntegerType sc
            C.TCIntMod   -> scGlobalApply sc "Cryptol.IntModNum" =<< traverse go tyargs
            C.TCFloat    -> scGlobalApply sc "Cryptol.TCFloat"   =<< traverse go tyargs
            C.TCArray    -> do a <- go (tyargs !! 0)
                               b <- go (tyargs !! 1)
                               scArrayType sc a b
            C.TCRational -> scGlobalApply sc "Cryptol.Rational" []
            C.TCSeq      -> scGlobalApply sc "Cryptol.seq" =<< traverse go tyargs
            C.TCFun      -> do a <- go (tyargs !! 0)
                               b <- go (tyargs !! 1)
                               scFun sc a b
            C.TCTuple _n -> scTupleType sc =<< traverse go tyargs
        C.PC pc ->
          case pc of
            C.PLiteral -> -- we omit first argument to class Literal
              do a <- go (tyargs !! 1)
                 scGlobalApply sc "Cryptol.PLiteral" [a]
            C.PLiteralLessThan -> -- we omit first argument to class LiteralLessThan
              do a <- go (tyargs !! 1)
                 scGlobalApply sc "Cryptol.PLiteralLessThan" [a]
            _ ->
              do pc' <- importPC sc pc
                 tyargs' <- traverse go tyargs
                 scApplyAll sc pc' tyargs'
        C.TF tf ->
          do tf' <- importTFun sc tf
             tyargs' <- traverse go tyargs
             scApplyAll sc tf' tyargs'
        C.TError _k ->
          panic "importType" ["found TError"]
  where
    go = importType sc env

isErasedProp :: C.Prop -> Bool
isErasedProp prop =
  case prop of
    C.TCon (C.PC C.PZero           ) _ -> False
    C.TCon (C.PC C.PLogic          ) _ -> False
    C.TCon (C.PC C.PRing           ) _ -> False
    C.TCon (C.PC C.PIntegral       ) _ -> False
    C.TCon (C.PC C.PField          ) _ -> False
    C.TCon (C.PC C.PRound          ) _ -> False
    C.TCon (C.PC C.PEq             ) _ -> False
    C.TCon (C.PC C.PCmp            ) _ -> False
    C.TCon (C.PC C.PSignedCmp      ) _ -> False
    C.TCon (C.PC C.PLiteral        ) _ -> False
    C.TCon (C.PC C.PLiteralLessThan) _ -> False
    _ -> True

-- | Translate a 'Prop' containing a numeric constraint to a 'Term' that tests
-- if the 'Prop' holds. This function will 'panic' for 'Prop's that are not
-- numeric constraints, such as @Integral@. In other words, this function
-- supports the same set of 'Prop's that constraint guards do.
importNumericConstraintAsBool :: SharedContext -> Env -> C.Prop -> IO Term
importNumericConstraintAsBool sc env prop =
  case prop of
    C.TCon (C.PC C.PEqual) [lhs, rhs] -> eqTerm lhs rhs
    C.TCon (C.PC C.PNeq) [lhs, rhs] -> eqTerm lhs rhs >>= scNot sc
    C.TCon (C.PC C.PGeq) [lhs, rhs] -> do
      -- Convert 'lhs >= rhs' into '(rhs < lhs) \/ (rhs == lhs)'
      lhs' <- importType sc env lhs
      rhs' <- importType sc env rhs
      lt <- scGlobalApply sc "Cryptol.tcLt" [rhs', lhs']
      eq <- scGlobalApply sc "Cryptol.tcEqual" [rhs', lhs']
      scOr sc lt eq
    C.TCon (C.PC C.PFin) [x] -> do
      x' <- importType sc env x
      scGlobalApply sc "Cryptol.tcFin" [x']
    C.TCon (C.PC C.PAnd) [lhs, rhs] -> do
      lhs' <- importType sc env lhs
      rhs' <- importType sc env rhs
      scAnd sc lhs' rhs'
    C.TCon (C.PC C.PTrue) [] -> scBool sc True
    C.TCon (C.TError _) _ -> scBool sc False
    C.TUser _ _ t -> importNumericConstraintAsBool sc env t
    _ ->
        panic "importNumericConstraintAsBool" [
            "Called with non-numeric constraint: " <> Text.pack (pretty prop)
        ]
  where
    -- | Construct a term for equality of two types
    eqTerm :: C.Type -> C.Type -> IO Term
    eqTerm lhs rhs = do
      lhs' <- importType sc env lhs
      rhs' <- importType sc env rhs
      scGlobalApply sc "Cryptol.tcEqual" [lhs', rhs']

importPropsType :: SharedContext -> Env -> [C.Prop] -> C.Type -> IO Term
importPropsType sc env [] ty = importType sc env ty
importPropsType sc env (prop : props) ty
  | isErasedProp prop = importPropsType sc env props ty
  | otherwise =
    do p <- importType sc env prop
       t <- importPropsType sc env props ty
       scFun sc p t

nameToLocalName :: C.Name -> LocalName
nameToLocalName = C.identText . C.nameIdent

nameToFieldName :: C.Name -> FieldName
nameToFieldName = C.identText . C.nameIdent

tparamToLocalName :: C.TParam -> LocalName
tparamToLocalName tp =
  maybe (Text.pack ("u" ++ show (C.tpUnique tp)))
        nameToLocalName
        (C.tpName tp)

importPolyType :: SharedContext -> Env -> [C.TParam] -> [C.Prop] -> C.Type -> IO Term
importPolyType sc env [] props ty = importPropsType sc env props ty
importPolyType sc env (tp : tps) props ty =
  do (env',a) <- bindTParam sc tp env
     t <- importPolyType sc env' tps props ty
     scGeneralizeTerms sc [a] t

importSchema :: SharedContext -> Env -> C.Schema -> IO Term
importSchema sc env (C.Forall tparams props ty) =
  importPolyType sc env tparams props ty

-- entry point
proveProp :: HasCallStack => SharedContext -> Env -> C.Prop -> IO Term
proveProp sc env prop = provePropRec sc env prop prop

-- internal recursive version
--
-- (we carry around the original prop when recursing as "prop0", in
-- case we get stuck and need to bail out, at which point we want to
-- be able to print it)
provePropRec :: HasCallStack => SharedContext -> Env -> C.Prop -> C.Prop -> IO Term
provePropRec sc env prop0 prop =
  case Map.lookup (normalizeProp prop) (envP env) of

    -- Class dictionary was provided as an argument
    Just (prf, fs) ->
       do -- apply field projections as necessary to compute superclasses
          -- NB: reverse the order of the fields
          foldM (scRecordSelect sc) prf (reverse fs)

    -- Class dictionary not provided, compute it from the structure of types
    Nothing ->
      case prop of
        -- instance Zero Bit
        (C.pIsZero -> Just (C.tIsBit -> True))
          -> do scGlobalApply sc "Cryptol.PZeroBit" []
        -- instance Zero Integer
        (C.pIsZero -> Just (C.tIsInteger -> True))
          -> do scGlobalApply sc "Cryptol.PZeroInteger" []
        -- instance Zero (Z n)
        (C.pIsZero -> Just (C.tIsIntMod -> Just n))
          -> do n' <- importType sc env n
                scGlobalApply sc "Cryptol.PZeroIntModNum" [n']
        -- instance Zero Rational
        (C.pIsZero -> Just (C.tIsRational -> True))
          -> do scGlobalApply sc "Cryptol.PZeroRational" []
        -- instance Zero [n]
        (C.pIsZero -> Just (C.tIsSeq -> Just (n, C.tIsBit -> True)))
          -> do n' <- importType sc env n
                scGlobalApply sc "Cryptol.PZeroSeqBool" [n']
        -- instance ValidFloat e p => Zero (Float e p)
        (C.pIsZero -> Just (C.tIsFloat -> Just (e, p)))
          -> do e' <- importType sc env e
                p' <- importType sc env p
                scGlobalApply sc "Cryptol.PZeroFloat" [e', p']
        -- instance (Zero a) => Zero [n]a
        (C.pIsZero -> Just (C.tIsSeq -> Just (n, a)))
          -> do n' <- importType sc env n
                a' <- importType sc env a
                pa <- provePropRec sc env prop0 (C.pZero a)
                scGlobalApply sc "Cryptol.PZeroSeq" [n', a', pa]
        -- instance (Zero b) => Zero (a -> b)
        (C.pIsZero -> Just (C.tIsFun -> Just (a, b)))
          -> do a' <- importType sc env a
                b' <- importType sc env b
                pb <- provePropRec sc env prop0 (C.pZero b)
                scGlobalApply sc "Cryptol.PZeroFun" [a', b', pb]
        -- instance (Zero a, Zero b, ...) => Zero (a, b, ...)
        (C.pIsZero -> Just (C.tIsTuple -> Just ts))
          -> do ps <- traverse (provePropRec sc env prop0 . C.pZero) ts
                scTuple sc ps
        -- instance (Zero a, Zero b, ...) => Zero { x : a, y : b, ... }
        (C.pIsZero -> Just (C.tIsRec -> Just fm))
          -> do provePropRec sc env prop0 (C.pZero (C.tTuple (map snd (C.canonicalFields fm))))

        -- instance Logic Bit
        (C.pIsLogic -> Just (C.tIsBit -> True))
          -> do scGlobalApply sc "Cryptol.PLogicBit" []
        -- instance Logic [n]
        (C.pIsLogic -> Just (C.tIsSeq -> Just (n, C.tIsBit -> True)))
          -> do n' <- importType sc env n
                scGlobalApply sc "Cryptol.PLogicSeqBool" [n']
        -- instance (Logic a) => Logic [n]a
        (C.pIsLogic -> Just (C.tIsSeq -> Just (n, a)))
          -> do n' <- importType sc env n
                a' <- importType sc env a
                pa <- provePropRec sc env prop0 (C.pLogic a)
                scGlobalApply sc "Cryptol.PLogicSeq" [n', a', pa]
        -- instance (Logic b) => Logic (a -> b)
        (C.pIsLogic -> Just (C.tIsFun -> Just (a, b)))
          -> do a' <- importType sc env a
                b' <- importType sc env b
                pb <- provePropRec sc env prop0 (C.pLogic b)
                scGlobalApply sc "Cryptol.PLogicFun" [a', b', pb]
        -- instance Logic ()
        (C.pIsLogic -> Just (C.tIsTuple -> Just []))
          -> do scGlobalApply sc "Cryptol.PLogicUnit" []
        -- instance (Logic a, Logic b) => Logic (a, b)
        (C.pIsLogic -> Just (C.tIsTuple -> Just [t]))
          -> do provePropRec sc env prop0 (C.pLogic t)
        (C.pIsLogic -> Just (C.tIsTuple -> Just (t : ts)))
          -> do a <- importType sc env t
                b <- importType sc env (C.tTuple ts)
                pa <- provePropRec sc env prop0 (C.pLogic t)
                pb <- provePropRec sc env prop0 (C.pLogic (C.tTuple ts))
                scGlobalApply sc "Cryptol.PLogicPair" [a, b, pa, pb]
        -- instance (Logic a, Logic b, ...) => instance Logic { x : a, y : b, ... }
        (C.pIsLogic -> Just (C.tIsRec -> Just fm))
          -> do provePropRec sc env prop0 (C.pLogic (C.tTuple (map snd (C.canonicalFields fm))))

        -- instance Ring Integer
        (C.pIsRing -> Just (C.tIsInteger -> True))
          -> do scGlobalApply sc "Cryptol.PRingInteger" []
        -- instance Ring (Z n)
        (C.pIsRing -> Just (C.tIsIntMod -> Just n))
          -> do n' <- importType sc env n
                scGlobalApply sc "Cryptol.PRingIntModNum" [n']
        -- instance Ring Rational
        (C.pIsRing -> Just (C.tIsRational -> True))
          -> do scGlobalApply sc "Cryptol.PRingRational" []
        -- instance (fin n) => Ring [n]
        (C.pIsRing -> Just (C.tIsSeq -> Just (n, C.tIsBit -> True)))
          -> do n' <- importType sc env n
                scGlobalApply sc "Cryptol.PRingSeqBool" [n']
        -- instance ValidFloat e p => Ring (Float e p)
        (C.pIsRing -> Just (C.tIsFloat -> Just (e, p)))
          -> do e' <- importType sc env e
                p' <- importType sc env p
                scGlobalApply sc "Cryptol.PRingFloat" [e', p']
        -- instance (Ring a) => Ring [n]a
        (C.pIsRing -> Just (C.tIsSeq -> Just (n, a)))
          -> do n' <- importType sc env n
                a' <- importType sc env a
                pa <- provePropRec sc env prop0 (C.pRing a)
                scGlobalApply sc "Cryptol.PRingSeq" [n', a', pa]
        -- instance (Ring b) => Ring (a -> b)
        (C.pIsRing -> Just (C.tIsFun -> Just (a, b)))
          -> do a' <- importType sc env a
                b' <- importType sc env b
                pb <- provePropRec sc env prop0 (C.pRing b)
                scGlobalApply sc "Cryptol.PRingFun" [a', b', pb]
        -- instance Ring ()
        (C.pIsRing -> Just (C.tIsTuple -> Just []))
          -> do scGlobalApply sc "Cryptol.PRingUnit" []
        -- instance (Ring a, Ring b) => Ring (a, b)
        (C.pIsRing -> Just (C.tIsTuple -> Just [t]))
          -> do provePropRec sc env prop0 (C.pRing t)
        (C.pIsRing -> Just (C.tIsTuple -> Just (t : ts)))
          -> do a <- importType sc env t
                b <- importType sc env (C.tTuple ts)
                pa <- provePropRec sc env prop0 (C.pRing t)
                pb <- provePropRec sc env prop0 (C.pRing (C.tTuple ts))
                scGlobalApply sc "Cryptol.PRingPair" [a, b, pa, pb]
        -- instance (Ring a, Ring b, ...) => instance Ring { x : a, y : b, ... }
        (C.pIsRing -> Just (C.tIsRec -> Just fm))
          -> do provePropRec sc env prop0 (C.pRing (C.tTuple (map snd (C.canonicalFields fm))))

        -- instance Integral Integer
        (C.pIsIntegral -> Just (C.tIsInteger -> True))
          -> do scGlobalApply sc "Cryptol.PIntegralInteger" []
        -- instance Integral [n]
        (C.pIsIntegral -> Just (C.tIsSeq -> (Just (n, C.tIsBit -> True))))
          -> do n' <- importType sc env n
                scGlobalApply sc "Cryptol.PIntegralSeqBool" [n']

        -- instance Field Rational
        (C.pIsField -> Just (C.tIsRational -> True))
          -> do scGlobalApply sc "Cryptol.PFieldRational" []
        -- instance (prime p) => Field (Z p)
        (C.pIsField -> Just (C.tIsIntMod -> Just n))
          -> do n' <- importType sc env n
                scGlobalApply sc "Cryptol.PFieldIntModNum" [n']
        -- instance (ValidFloat e p) => Field (Float e p)
        (C.pIsField -> Just (C.tIsFloat -> Just (e, p)))
          -> do e' <- importType sc env e
                p' <- importType sc env p
                scGlobalApply sc "Cryptol.PFieldFloat" [e', p']

        -- instance Round Rational
        (C.pIsRound -> Just (C.tIsRational -> True))
          -> do scGlobalApply sc "Cryptol.PRoundRational" []
        -- instance (ValidFloat e p) => Round (Float e p)
        (C.pIsRound -> Just (C.tIsFloat -> Just (e, p)))
          -> do e' <- importType sc env e
                p' <- importType sc env p
                scGlobalApply sc "Cryptol.PRoundFloat" [e', p']

        -- instance Eq Bit
        (C.pIsEq -> Just (C.tIsBit -> True))
          -> do scGlobalApply sc "Cryptol.PEqBit" []
        -- instance Eq Integer
        (C.pIsEq -> Just (C.tIsInteger -> True))
          -> do scGlobalApply sc "Cryptol.PEqInteger" []
        -- instance Eq (Z n)
        (C.pIsEq -> Just (C.tIsIntMod -> Just n))
          -> do n' <- importType sc env n
                scGlobalApply sc "Cryptol.PEqIntModNum" [n']
        -- instance Eq Rational
        (C.pIsEq -> Just (C.tIsRational -> True))
          -> do scGlobalApply sc "Cryptol.PEqRational" []
        -- instance Eq (Float e p)
        (C.pIsEq -> Just (C.tIsFloat -> Just (e, p)))
          -> do e' <- importType sc env e
                p' <- importType sc env p
                scGlobalApply sc "Cryptol.PEqFloat" [e', p']
        -- instance (fin n) => Eq [n]
        (C.pIsEq -> Just (C.tIsSeq -> Just (n, C.tIsBit -> True)))
          -> do n' <- importType sc env n
                scGlobalApply sc "Cryptol.PEqSeqBool" [n']
        -- instance (fin n, Eq a) => Eq [n]a
        (C.pIsEq -> Just (C.tIsSeq -> Just (n, a)))
          -> do n' <- importType sc env n
                a' <- importType sc env a
                pa <- provePropRec sc env prop0 (C.pEq a)
                scGlobalApply sc "Cryptol.PEqSeq" [n', a', pa]
        -- instance Eq ()
        (C.pIsEq -> Just (C.tIsTuple -> Just []))
          -> do scGlobalApply sc "Cryptol.PEqUnit" []
        -- instance (Eq a, Eq b) => Eq (a, b)
        (C.pIsEq -> Just (C.tIsTuple -> Just [t]))
          -> do provePropRec sc env prop0 (C.pEq t)
        (C.pIsEq -> Just (C.tIsTuple -> Just (t : ts)))
          -> do a <- importType sc env t
                b <- importType sc env (C.tTuple ts)
                pa <- provePropRec sc env prop0 (C.pEq t)
                pb <- provePropRec sc env prop0 (C.pEq (C.tTuple ts))
                scGlobalApply sc "Cryptol.PEqPair" [a, b, pa, pb]
        -- instance (Eq a, Eq b, ...) => instance Eq { x : a, y : b, ... }
        (C.pIsEq -> Just (C.tIsRec -> Just fm))
          -> do provePropRec sc env prop0 (C.pEq (C.tTuple (map snd (C.canonicalFields fm))))

        -- instance Cmp Bit
        (C.pIsCmp -> Just (C.tIsBit -> True))
          -> do scGlobalApply sc "Cryptol.PCmpBit" []
        -- instance Cmp Integer
        (C.pIsCmp -> Just (C.tIsInteger -> True))
          -> do scGlobalApply sc "Cryptol.PCmpInteger" []
        -- instance Cmp Rational
        (C.pIsCmp -> Just (C.tIsRational -> True))
          -> do scGlobalApply sc "Cryptol.PCmpRational" []
        -- instance Cmp (Float e p)
        (C.pIsCmp -> Just (C.tIsFloat -> Just (e, p)))
          -> do e' <- importType sc env e
                p' <- importType sc env p
                scGlobalApply sc "Cryptol.PCmpFloat" [e', p']
        -- instance (fin n) => Cmp [n]
        (C.pIsCmp -> Just (C.tIsSeq -> Just (n, C.tIsBit -> True)))
          -> do n' <- importType sc env n
                scGlobalApply sc "Cryptol.PCmpSeqBool" [n']
        -- instance (fin n, Cmp a) => Cmp [n]a
        (C.pIsCmp -> Just (C.tIsSeq -> Just (n, a)))
          -> do n' <- importType sc env n
                a' <- importType sc env a
                pa <- provePropRec sc env prop0 (C.pCmp a)
                scGlobalApply sc "Cryptol.PCmpSeq" [n', a', pa]
        -- instance Cmp ()
        (C.pIsCmp -> Just (C.tIsTuple -> Just []))
          -> do scGlobalApply sc "Cryptol.PCmpUnit" []
        -- instance (Cmp a, Cmp b) => Cmp (a, b)
        (C.pIsCmp -> Just (C.tIsTuple -> Just [t]))
          -> do provePropRec sc env prop0 (C.pCmp t)
        (C.pIsCmp -> Just (C.tIsTuple -> Just (t : ts)))
          -> do a <- importType sc env t
                b <- importType sc env (C.tTuple ts)
                pa <- provePropRec sc env prop0 (C.pCmp t)
                pb <- provePropRec sc env prop0 (C.pCmp (C.tTuple ts))
                scGlobalApply sc "Cryptol.PCmpPair" [a, b, pa, pb]
        -- instance (Cmp a, Cmp b, ...) => instance Cmp { x : a, y : b, ... }
        (C.pIsCmp -> Just (C.tIsRec -> Just fm))
          -> do provePropRec sc env prop0 (C.pCmp (C.tTuple (map snd (C.canonicalFields fm))))

        -- instance (fin n) => SignedCmp [n]
        (C.pIsSignedCmp -> Just (C.tIsSeq -> Just (n, C.tIsBit -> True)))
          -> do n' <- importType sc env n
                scGlobalApply sc "Cryptol.PSignedCmpSeqBool" [n']
        -- instance (fin n, SignedCmp a) => SignedCmp [n]a
        (C.pIsSignedCmp -> Just (C.tIsSeq -> Just (n, a)))
          -> do n' <- importType sc env n
                a' <- importType sc env a
                pa <- provePropRec sc env prop0 (C.pSignedCmp a)
                scGlobalApply sc "Cryptol.PSignedCmpSeq" [n', a', pa]
        -- instance SignedCmp ()
        (C.pIsSignedCmp -> Just (C.tIsTuple -> Just []))
          -> do scGlobalApply sc "Cryptol.PSignedCmpUnit" []
        -- instance (SignedCmp a, SignedCmp b) => SignedCmp (a, b)
        (C.pIsSignedCmp -> Just (C.tIsTuple -> Just [t]))
          -> do provePropRec sc env prop0 (C.pSignedCmp t)
        (C.pIsSignedCmp -> Just (C.tIsTuple -> Just (t : ts)))
          -> do a <- importType sc env t
                b <- importType sc env (C.tTuple ts)
                pa <- provePropRec sc env prop0 (C.pSignedCmp t)
                pb <- provePropRec sc env prop0 (C.pSignedCmp (C.tTuple ts))
                scGlobalApply sc "Cryptol.PSignedCmpPair" [a, b, pa, pb]
        -- instance (SignedCmp a, SignedCmp b, ...) => instance SignedCmp { x : a, y : b, ... }
        (C.pIsSignedCmp -> Just (C.tIsRec -> Just fm))
          -> do provePropRec sc env prop0 (C.pSignedCmp (C.tTuple (map snd (C.canonicalFields fm))))

        -- instance Literal val Bit
        (C.pIsLiteral -> Just (_, C.tIsBit -> True))
          -> do scGlobalApply sc "Cryptol.PLiteralBit" []
        -- instance Literal val Integer
        (C.pIsLiteral -> Just (_, C.tIsInteger -> True))
          -> do scGlobalApply sc "Cryptol.PLiteralInteger" []
        -- instance Literal val (Z n)
        (C.pIsLiteral -> Just (_, C.tIsIntMod -> Just n))
          -> do n' <- importType sc env n
                scGlobalApply sc "Cryptol.PLiteralIntModNum" [n']
        -- instance Literal val Rational
        (C.pIsLiteral -> Just (_, C.tIsRational -> True))
          -> do scGlobalApply sc "Cryptol.PLiteralRational" []
        -- instance (fin n, n >= width val) => Literal val [n]
        (C.pIsLiteral -> Just (_, C.tIsSeq -> Just (n, C.tIsBit -> True)))
          -> do n' <- importType sc env n
                scGlobalApply sc "Cryptol.PLiteralSeqBool" [n']
        -- instance ValidFloat e p => Literal val (Float e p) (with extra constraints)
        (C.pIsLiteral -> Just (_, C.tIsFloat -> Just (e, p)))
          -> do e' <- importType sc env e
                p' <- importType sc env p
                scGlobalApply sc "Cryptol.PLiteralFloat" [e', p']

        -- instance (2 >= val) => LiteralLessThan val Bit
        (C.pIsLiteralLessThan -> Just (_, C.tIsBit -> True))
          -> do scGlobalApply sc "Cryptol.PLiteralBit" []
        -- instance LiteralLessThan val Integer
        (C.pIsLiteralLessThan -> Just (_, C.tIsInteger -> True))
          -> do scGlobalApply sc "Cryptol.PLiteralInteger" []
        -- instance (fin n, n >= 1, n >= val) LiteralLessThan val (Z n)
        (C.pIsLiteralLessThan -> Just (_, C.tIsIntMod -> Just n))
          -> do n' <- importType sc env n
                scGlobalApply sc "Cryptol.PLiteralIntModNum" [n']
        -- instance Literal val Rational
        (C.pIsLiteralLessThan -> Just (_, C.tIsRational -> True))
          -> do scGlobalApply sc "Cryptol.PLiteralRational" []
        -- instance (fin n, n >= lg2 val) => Literal val [n]
        (C.pIsLiteralLessThan -> Just (_, C.tIsSeq -> Just (n, C.tIsBit -> True)))
          -> do n' <- importType sc env n
                scGlobalApply sc "Cryptol.PLiteralSeqBool" [n']
        -- instance ValidFloat e p => Literal val (Float e p) (with extra constraints)
        (C.pIsLiteralLessThan -> Just (_, C.tIsFloat -> Just (e, p)))
          -> do e' <- importType sc env e
                p' <- importType sc env p
                scGlobalApply sc "Cryptol.PLiteralFloat" [e', p']

        _ -> do
            let prop0' = "   " <> Text.pack (pretty prop0)
                prop' = "   " <> Text.pack (pretty prop)
                env' = map (\p -> "   " <> Text.pack (pretty p)) $ Map.keys $ envP env
                message = [
                    "Cannot find or infer typeclass instance",
                    "Property needed:",
                    prop',
                    "Original property:",
                    prop0',
                    "Available propositions in the environment:"
                 ] ++ env'
            panic "proveProp" message

importPrimitive :: SharedContext -> ImportPrimitiveOptions -> Env -> C.Name -> C.Schema -> IO Term
importPrimitive sc primOpts env n sch
  -- lookup primitive in the main primitive lookup table
  | Just nm <- C.asPrim n, Just term <- Map.lookup nm allPrims = term sc

  -- lookup primitive in the main reference implementation lookup table
  | Just nm <- C.asPrim n, Just expr <- Map.lookup nm (envRefPrims env) =
      do t <- importSchema sc env sch
         e <- importExpr sc env expr
         nmi <- importName n
         scDefineConstant sc nmi e t

  -- lookup primitive in the extra primitive lookup table
  | Just nm <- C.asPrim n, Just t <- Map.lookup nm (envPrims env) = return t

  -- Optionally, create an opaque constant representing the primitive
  -- if it doesn't match one of the ones we know about.
  | Just _ <- C.asPrim n, allowUnknownPrimitives primOpts =
      importOpaque sc env n sch

  -- Panic if we don't know the given primitive (TODO? probably shouldn't be a panic)
  | Just nm <- C.asPrim n =
      panic "importPrimitive" ["Unknown Cryptol primitive name: " <> Text.pack (show nm)]

  | otherwise =
      panic "importPrimitive" ["Improper Cryptol primitive name: " <> Text.pack (show n)]

-- | Create an opaque constant with the given name and schema
importOpaque :: SharedContext -> Env -> C.Name -> C.Schema -> IO Term
importOpaque sc env n sch = do
  t <- importSchema sc env sch
  nmi <- importName n
  scOpaqueConstant sc nmi t

importConstant :: SharedContext -> Env -> C.Name -> C.Schema -> Term -> IO Term
importConstant sc env n sch rhs = do
  nmi <- importName n
  t <- importSchema sc env sch
  scDefineConstant sc nmi rhs t

allPrims :: Map C.PrimIdent (SharedContext -> IO Term)
allPrims = prelPrims <> arrayPrims <> floatPrims <> suiteBPrims <> primeECPrims

prelPrims :: Map C.PrimIdent (SharedContext -> IO Term)
prelPrims =
  Map.fromList $
  first C.prelPrim <$>
  [ ("True",         flip scBool True)
  , ("False",        flip scBool False)
  , ("number",       flip scGlobalDef "Cryptol.ecNumber")      -- Converts a numeric type into its corresponding value.
     --                                                        -- {val, a} (Literal val a) => a

  , ("fromZ",        flip scGlobalDef "Cryptol.ecFromZ")       -- {n} (fin n, n >= 1) => Z n -> Integer

    -- -- Zero
  , ("zero",         flip scGlobalDef "Cryptol.ecZero")        -- {a} (Zero a) => a

    -- -- Logic
  , ("&&",           flip scGlobalDef "Cryptol.ecAnd")         -- {a} (Logic a) => a -> a -> a
  , ("||",           flip scGlobalDef "Cryptol.ecOr")          -- {a} (Logic a) => a -> a -> a
  , ("^",            flip scGlobalDef "Cryptol.ecXor")         -- {a} (Logic a) => a -> a -> a
  , ("complement",   flip scGlobalDef "Cryptol.ecCompl")       -- {a} (Logic a) => a -> a

    -- -- Ring
  , ("fromInteger",  flip scGlobalDef "Cryptol.ecFromInteger") -- {a} (Ring a) => Integer -> a
  , ("+",            flip scGlobalDef "Cryptol.ecPlus")        -- {a} (Ring a) => a -> a -> a
  , ("-",            flip scGlobalDef "Cryptol.ecMinus")       -- {a} (Ring a) => a -> a -> a
  , ("*",            flip scGlobalDef "Cryptol.ecMul")         -- {a} (Ring a) => a -> a -> a
  , ("negate",       flip scGlobalDef "Cryptol.ecNeg")         -- {a} (Ring a) => a -> a

    -- -- Integral
  , ("toInteger",    flip scGlobalDef "Cryptol.ecToInteger")   -- {a} (Integral a) => a -> Integer
  , ("/",            flip scGlobalDef "Cryptol.ecDiv")         -- {a} (Integral a) => a -> a -> a
  , ("%",            flip scGlobalDef "Cryptol.ecMod")         -- {a} (Integral a) => a -> a -> a
  , ("^^",           flip scGlobalDef "Cryptol.ecExp")         -- {a} (Ring a, Integral b) => a -> b -> a
  , ("infFrom",      flip scGlobalDef "Cryptol.ecInfFrom")     -- {a} (Integral a) => a -> [inf]a
  , ("infFromThen",  flip scGlobalDef "Cryptol.ecInfFromThen") -- {a} (Integral a) => a -> a -> [inf]a

    -- -- Field
  , ("recip",        flip scGlobalDef "Cryptol.ecRecip")       -- {a} (Field a) => a -> a
  , ("/.",           flip scGlobalDef "Cryptol.ecFieldDiv")    -- {a} (Field a) => a -> a -> a

    -- -- Round
  , ("ceiling",      flip scGlobalDef "Cryptol.ecCeiling")     -- {a} (Round a) => a -> Integer
  , ("floor",        flip scGlobalDef "Cryptol.ecFloor")       -- {a} (Round a) => a -> Integer
  , ("trunc",        flip scGlobalDef "Cryptol.ecTruncate")    -- {a} (Round a) => a -> Integer
  , ("roundAway",    flip scGlobalDef "Cryptol.ecRoundAway")   -- {a} (Round a) => a -> Integer
  , ("roundToEven",  flip scGlobalDef "Cryptol.ecRoundToEven") -- {a} (Round a) => a -> Integer

    -- -- Eq
  , ("==",           flip scGlobalDef "Cryptol.ecEq")          -- {a} (Eq a) => a -> a -> Bit
  , ("!=",           flip scGlobalDef "Cryptol.ecNotEq")       -- {a} (Eq a) => a -> a -> Bit

    -- -- Cmp
  , ("<",            flip scGlobalDef "Cryptol.ecLt")          -- {a} (Cmp a) => a -> a -> Bit
  , (">",            flip scGlobalDef "Cryptol.ecGt")          -- {a} (Cmp a) => a -> a -> Bit
  , ("<=",           flip scGlobalDef "Cryptol.ecLtEq")        -- {a} (Cmp a) => a -> a -> Bit
  , (">=",           flip scGlobalDef "Cryptol.ecGtEq")        -- {a} (Cmp a) => a -> a -> Bit

    -- -- SignedCmp
  , ("<$",           flip scGlobalDef "Cryptol.ecSLt")         -- {a} (SignedCmp a) => a -> a -> Bit

    -- -- Bitvector primitives
  , ("/$",           flip scGlobalDef "Cryptol.ecSDiv")        -- {n} (fin n, n>=1) => [n] -> [n] -> [n]
  , ("%$",           flip scGlobalDef "Cryptol.ecSMod")        -- {n} (fin n, n>=1) => [n] -> [n] -> [n]
  , ("lg2",          flip scGlobalDef "Cryptol.ecLg2")         -- {n} (fin n) => [n] -> [n]
  , (">>$",          flip scGlobalDef "Cryptol.ecSShiftR")     -- {n, ix} (fin n, n >= 1, Integral ix) => [n] -> ix -> [n]
  , ("toSignedInteger",
                     flip scGlobalDef "Cryptol.toSignedInteger") -- {n} (fin n, n >= 1) => [n] -> Integer

    -- -- Rational primitives
  , ("ratio",        flip scGlobalDef "Cryptol.ecRatio")       -- Integer -> Integer -> Rational

    -- -- FLiteral
  , ("fraction",     flip scGlobalDef "Cryptol.ecFraction")    -- {m, n, r, a} FLiteral m n r a => a

    -- -- Shifts/rotates
  , ("<<",           flip scGlobalDef "Cryptol.ecShiftL")      -- {n, ix, a} (Integral ix, Zero a) => [n]a -> ix -> [n]a
  , (">>",           flip scGlobalDef "Cryptol.ecShiftR")      -- {n, ix, a} (Integral ix, Zero a) => [n]a -> ix -> [n]a
  , ("<<<",          flip scGlobalDef "Cryptol.ecRotL")        -- {n, ix, a} (fin n, Integral ix) => [n]a -> ix -> [n]a
  , (">>>",          flip scGlobalDef "Cryptol.ecRotR")        -- {n, ix, a} (fin n, Integral ix) => [n]a -> ix -> [n]a

    -- -- Sequences primitives
  , ("#",            flip scGlobalDef "Cryptol.ecCat")         -- {a,b,d} (fin a) => [a] d -> [b] d -> [a + b] d
  , ("take",         flip scGlobalDef "Cryptol.ecTake")        -- {front, back, a} [front + back]a -> [front]a
  , ("drop",         flip scGlobalDef "Cryptol.ecDrop")        -- {front, back, a} (fin front) => [front + back]a -> [back]a
  , ("join",         flip scGlobalDef "Cryptol.ecJoin")        -- {a,b,c} (fin b) => [a][b]c -> [a * b]c
  , ("split",        flip scGlobalDef "Cryptol.ecSplit")       -- {a,b,c} (fin b) => [a * b] c -> [a][b] c
  , ("reverse",      flip scGlobalDef "Cryptol.ecReverse")     -- {a,b} (fin a) => [a] b -> [a] b
  , ("transpose",    flip scGlobalDef "Cryptol.ecTranspose")   -- {a,b,c} [a][b]c -> [b][a]c
  , ("@",            flip scGlobalDef "Cryptol.ecAt")          -- {n, a, ix} (Integral ix) => [n]a -> ix -> a
  , ("!",            flip scGlobalDef "Cryptol.ecAtBack")      -- {n, a, ix} (fin n, Integral ix) => [n]a -> ix -> a
  , ("update",       flip scGlobalDef "Cryptol.ecUpdate")      -- {n, a, ix} (Integral ix) => [n]a -> ix -> a -> [n]a
  , ("updateEnd",    flip scGlobalDef "Cryptol.ecUpdateEnd")   -- {n, a, ix} (fin n, Integral ix) => [n]a -> ix -> a -> [n]a

    -- -- Enumerations
  , ("fromTo",         flip scGlobalDef "Cryptol.ecFromTo")
                                  -- fromTo : {first, last, bits, a}
                                  --           ( fin last, fin bits, last >== first,
                                  --             Literal first a, Literal last a)
                                  --        => [1 + (last - first)]a
  , ("fromToLessThan", flip scGlobalDef "Cryptol.ecFromToLessThan")
                                  -- fromToLessThan : {first, bound, a}
                                  --                   ( fin first, bound >= first,
                                  --                     LiteralLessThan bound a)
                                  --                => [bound - first]a
  , ("fromThenTo",     flip scGlobalDef "Cryptol.ecFromThenTo")
                                  -- fromThenTo : {first, next, last, a, len}
                                  --              ( fin first, fin next, fin last
                                  --              , Literal first a, Literal next a, Literal last a
                                  --              , first != next
                                  --              , lengthFromThenTo first next last == len) => [len]a
  , ("fromToBy",       flip scGlobalDef "Cryptol.ecFromToBy")
                                  -- fromToBy : {first, last, stride, a}
                                  --   (fin last, fin stride, stride >= 1, last >= first, Literal last a) =>
                                  --   [1 + (last - first)/stride]a
  , ("fromToByLessThan", flip scGlobalDef "Cryptol.ecFromToByLessThan")
                                  -- fromToByLessThan : {first, bound, stride, a}
                                  --   (fin first, fin stride, stride >= 1, bound >= first, LiteralLessThan bound a) =>
                                  --   [(bound - first)/^stride]a
  , ("fromToDownBy", flip scGlobalDef "Cryptol.ecFromToDownBy")
                                  -- fromToDownBy : {first, last, stride, a}
                                  --   (fin first, fin stride, stride >= 1, first >= last, Literal first a) =>
                                  --   [1 + (first - last)/stride]a
  , ("fromToDownByGreaterThan", flip scGlobalDef "Cryptol.ecFromToDownByGreaterThan")
                                  -- fromToDownByGreaterThan : {first, bound, stride, a}
                                  --   (fin first, fin stride, stride >= 1, first >= bound, Literal first a) =>
                                  --   [(first - bound)/^stride]a

    -- GF2 Polynomial primitives
  , ("pmult",        flip scGlobalDef "Cryptol.ecPmult")     -- {u, v} (fin u, fin v) => [1 + u] -> [1 + v] -> [1 + (u + v)]
  , ("pmod",         flip scGlobalDef "Cryptol.ecPmod")      -- {u, v} (fin u, fin v) => [u] -> [1 + v] -> [v]

    -- Evaluation primitives: deepseq, parmap
  , ("deepseq",      flip scGlobalDef "Cryptol.ecDeepseq")     -- {a, b} (Eq b) => a -> b -> b
  , ("parmap",       flip scGlobalDef "Cryptol.ecParmap")      -- {a, b, n} (Eq b, fin n) => (a -> b) -> [n]a -> [n]b
  , ("foldl",        flip scGlobalDef "Cryptol.ecFoldl")       -- {n, a, b} (fin n) => (a -> b -> a) -> a -> [n]b -> a
  , ("foldl'",       flip scGlobalDef "Cryptol.ecFoldlPrime")  -- {n, a, b} (fin n, Eq a) => (a -> b -> a) -> a -> [n]b -> a
  , ("scanl",        flip scGlobalDef "Cryptol.ecScanl")       -- {n, a, b}  (a -> b -> a) -> a -> [n]b -> [1+n]a
  , ("error",        flip scGlobalDef "Cryptol.ecError")       -- {at,len} (fin len) => [len][8] -> at -- Run-time error
  , ("random",       flip scGlobalDef "Cryptol.ecRandom")      -- {a} => [32] -> a -- Random values
  , ("trace",        flip scGlobalDef "Cryptol.ecTrace")       -- {n,a,b} [n][8] -> a -> b -> b
  ]

arrayPrims :: Map C.PrimIdent (SharedContext -> IO Term)
arrayPrims =
  Map.fromList $
  first C.arrayPrim <$>
  [ ("arrayConstant", flip scGlobalDef "Cryptol.ecArrayConstant") -- {a,b} b -> Array a b
  , ("arrayLookup",   flip scGlobalDef "Cryptol.ecArrayLookup") -- {a,b} Array a b -> a -> b
  , ("arrayUpdate",   flip scGlobalDef "Cryptol.ecArrayUpdate") -- {a,b} Array a b -> a -> b -> Array a b
  , ("arrayCopy", flip scGlobalDef "Cryptol.ecArrayCopy") -- {n,a} Array [n] a -> [n] -> Array [n] a -> [n] -> [n] -> Array [n] a
  , ("arrayEq", flip scGlobalDef "Cryptol.ecArrayEq")     -- {a, b} (Array a b) -> (Array a b) -> Bool
  , ("arraySet", flip scGlobalDef "Cryptol.ecArraySet") -- {n,a} Array [n] a -> [n] -> a -> [n] -> Array [n] a
  , ("arrayRangeEqual", flip scGlobalDef "Cryptol.ecArrayRangeEq") -- {n,a} Array [n] a -> [n] -> Array [n] a -> [n] -> [n] -> Bit
  ]

floatPrims :: Map C.PrimIdent (SharedContext -> IO Term)
floatPrims =
  Map.fromList $
  first C.floatPrim <$>
  [ ("fpNaN",          flip scGlobalDef "Cryptol.ecFpNaN")
  , ("fpPosInf",       flip scGlobalDef "Cryptol.ecFpPosInf")
  , ("fpFromBits",     flip scGlobalDef "Cryptol.ecFpFromBits")
  , ("fpToBits",       flip scGlobalDef "Cryptol.ecFpToBits")
  , ("=.=",            flip scGlobalDef "Cryptol.ecFpEq")
  , ("fpAdd",          flip scGlobalDef "Cryptol.ecFpAdd")
  , ("fpSub",          flip scGlobalDef "Cryptol.ecFpSub")
  , ("fpMul",          flip scGlobalDef "Cryptol.ecFpMul")
  , ("fpDiv",          flip scGlobalDef "Cryptol.ecFpDiv")
  , ("fpToRational",   flip scGlobalDef "Cryptol.ecFpToRational")
  , ("fpFromRational", flip scGlobalDef "Cryptol.ecFpFromRational")
  , ("fpIsNaN",        flip scGlobalDef "Cryptol.fpIsNaN")
  , ("fpIsInf",        flip scGlobalDef "Cryptol.fpIsInf")
  , ("fpIsZero",       flip scGlobalDef "Cryptol.fpIsZero")
  , ("fpIsNeg",        flip scGlobalDef "Cryptol.fpIsNeg")
  , ("fpIsNormal",     flip scGlobalDef "Cryptol.fpIsNormal")
  , ("fpIsSubnormal",  flip scGlobalDef "Cryptol.fpIsSubnormal")
  , ("fpFMA",          flip scGlobalDef "Cryptol.fpFMA")
  , ("fpAbs",          flip scGlobalDef "Cryptol.fpAbs")
  , ("fpSqrt",         flip scGlobalDef "Cryptol.fpSqrt")
  ]

suiteBPrims :: Map C.PrimIdent (SharedContext -> IO Term)
suiteBPrims =
  Map.fromList $
  first C.suiteBPrim <$>
  [ ("AESEncRound",      flip scGlobalDef "Cryptol.AESEncRound")
  , ("AESEncFinalRound", flip scGlobalDef "Cryptol.AESEncFinalRound")
  , ("AESDecRound",      flip scGlobalDef "Cryptol.AESDecRound")
  , ("AESDecFinalRound", flip scGlobalDef "Cryptol.AESDecFinalRound")
  , ("AESInvMixColumns", flip scGlobalDef "Cryptol.AESInvMixColumns")
  , ("AESKeyExpand",     flip scGlobalDef "Cryptol.AESKeyExpand")
  , ("processSHA2_224",  flip scGlobalDef "Cryptol.processSHA2_224")
  , ("processSHA2_256",  flip scGlobalDef "Cryptol.processSHA2_256")
  , ("processSHA2_384",  flip scGlobalDef "Cryptol.processSHA2_384")
  , ("processSHA2_512",  flip scGlobalDef "Cryptol.processSHA2_512")
  ]

primeECPrims :: Map C.PrimIdent (SharedContext -> IO Term)
primeECPrims =
  Map.fromList $
  first C.primeECPrim <$>
  [ ("ec_double",      flip scGlobalDef "Cryptol.ec_double")
  , ("ec_add_nonzero", flip scGlobalDef "Cryptol.ec_add_nonzero")
  , ("ec_mult",        flip scGlobalDef "Cryptol.ec_mult")
  , ("ec_twin_mult",   flip scGlobalDef "Cryptol.ec_twin_mult")
  ]

-- | Convert a Cryptol expression to a SAWCore term. Calling
-- 'scTypeOf' on the result of @'importExpr' sc env expr@ must yield a
-- type that is equivalent (i.e. convertible) with the one returned by
-- @'importSchema' sc env ('fastTypeOf' ('envC' env) expr)@.
importExpr :: HasCallStack => SharedContext -> Env -> C.Expr -> IO Term
importExpr sc env expr =
  case expr of
    C.EList es t ->
      do t' <- importType sc env t
         es' <- traverse (importExpr' sc env (C.tMono t)) es
         scVector sc t' es'

    C.ETuple es ->
      do es' <- traverse (importExpr sc env) es
         scTuple sc es'

    C.ERec fm ->
      do es' <- traverse (importExpr sc env . snd) (C.canonicalFields fm)
         scTuple sc es'

    C.ESel e sel ->
      -- Elimination for tuple/record/list
      case sel of
        C.TupleSel i _maybeLen ->
          do e' <- importExpr sc env e
             let t = fastTypeOf (envC env) e
             case C.tIsTuple t of
               Just ts -> scTupleSelector sc e' (i+1) (length ts)
               Nothing -> panic "importExpr" [
                              "Invalid tuple selector: " <> Text.pack (show i),
                              "Type: " <> Text.pack (pretty t)
                          ]
        C.RecordSel x _ ->
          do e' <- importExpr sc env e
             let t = fastTypeOf (envC env) e
             case C.tNoUser t of
               C.TRec fm ->
                 do i <- the
                      ("Expected field " <> Text.pack (show x) <> " in normal RecordSel")
                      (elemIndex x (map fst (C.canonicalFields fm)))
                    scTupleSelector sc e' (i+1) (length (C.canonicalFields fm))
               C.TNominal nt _args ->
                 do let fs = case C.ntDef nt of
                               C.Struct s -> C.ntFields s
                               C.Enum {} ->
                                 panic "importExpr" [
                                     "Select from enum",
                                     "Type: " <> Text.pack (pretty t)
                                 ]
                               C.Abstract ->
                                 panic "importExpr" [
                                     "Select from abstract type",
                                     "Type: " <> Text.pack (pretty t)
                                 ]
                    i <- the ("Expected field " <> Text.pack (show x) <> " in Newtype Record Sel")
                          (elemIndex x (map fst (C.canonicalFields fs)))
                    scTupleSelector sc e' (i+1) (length (C.canonicalFields fs))
               _ -> panic "importExpr" [
                        "Invalid record selector: " <> Text.pack (pretty x),
                        "Type: " <> Text.pack (pretty t)
                    ]
        C.ListSel i _maybeLen ->
          do let t = fastTypeOf (envC env) e
             (n, a) <-
               case C.tIsSeq t of
                 Just (n, a) -> return (n, a)
                 Nothing -> panic "importExpr" [
                                "ListSel: not a list type",
                                "Type: " <> Text.pack (pretty t)
                            ]
             a' <- importType sc env a
             n' <- importType sc env n
             e' <- importExpr sc env e
             i' <- scNat sc (fromIntegral i)
             scGlobalApply sc "Cryptol.eListSel" [a', n', e', i']

    C.ESet _ e1 sel e2 ->
      case sel of
        C.TupleSel i _maybeLen ->
          do e1' <- importExpr sc env e1
             e2' <- importExpr sc env e2
             let t1 = fastTypeOf (envC env) e1
             case C.tIsTuple t1 of
               Nothing ->
                    panic "importExpr" [
                        "ESet/TupleSel: not a tuple type",
                        "Type: " <> Text.pack (pretty t1)
                    ]
               Just ts ->
                 do ts' <- traverse (importType sc env) ts
                    let t2' = ts' !! i
                    f <- scGlobalApply sc "Cryptol.const" [t2', t2', e2']
                    g <- tupleUpdate sc f i ts'
                    scApply sc g e1'
        C.RecordSel x _ ->
          do e1' <- importExpr sc env e1
             e2' <- importExpr sc env e2
             let t1 = fastTypeOf (envC env) e1
             case C.tIsRec t1 of
               Nothing ->
                    panic "importExpr" [
                        "ESet/RecordSel: not a record type",
                        "Type: " <> Text.pack (pretty t1)
                    ]
               Just tm ->
                 do i <- the ("Expected a field " <> Text.pack (show x) <> " RecordSel")
                      (elemIndex x (map fst (C.canonicalFields tm)))
                    ts' <- traverse (importType sc env . snd) (C.canonicalFields tm)
                    let t2' = ts' !! i
                    f <- scGlobalApply sc "Cryptol.const" [t2', t2', e2']
                    g <- tupleUpdate sc f i ts'
                    scApply sc g e1'
        C.ListSel _i _maybeLen ->
          panic "importExpr" [
              "ListSel is unsupported in ESet:",
              "   " <> Text.pack (pretty expr)
          ]

    C.EIf e1 e2 e3 ->
      do let ty = fastTypeOf (envC env) e2
         ty' <- importType sc env ty
         e1' <- importExpr sc env e1
         e2' <- importExpr sc env e2
         e3' <- importExpr' sc env (C.tMono ty) e3
         scGlobalApply sc "Prelude.ite" [ty', e1', e2', e3']

    C.EComp len eltty e mss ->
      importComp sc env len eltty e mss

    C.EVar qname ->
      case Map.lookup qname (envE env) of
        Just e' -> pure e'
        Nothing -> panic "importExpr" ["Unknown variable: " <> Text.pack (show qname)]

    C.ETAbs tp e ->
      do (env',a) <- bindTParam sc tp env
         e' <- importExpr sc env' e
         scAbstractTerms sc [a] e'

    C.ETApp e t ->
      do e' <- importExpr sc env e
         t' <- importType sc env t
         scApply sc e' t'

    C.EApp e1 e2 ->
      do e1' <- importExpr sc env e1
         let t1 = fastTypeOf (envC env) e1
         t1a <-
           case C.tIsFun t1 of
             Just (a, _) -> return a
             Nothing ->
                 panic "importExpr" [
                     "EApp: expected function type",
                     "Type: " <> Text.pack (pretty t1)
                 ]
         e2' <- importExpr' sc env (C.tMono t1a) e2
         scApply sc e1' e2'

    C.EAbs x t e ->
      do (env',v,_) <- bindName sc x (C.tMono t) env
         e' <- importExpr sc env' e
         scAbstractTerms sc [v] e'

    C.EProofAbs prop e
      | isErasedProp prop -> importExpr sc env e
      | otherwise ->
        do (env',v) <- bindProp sc prop "_P" env
           e' <- importExpr sc env' e
           scAbstractTerms sc [v] e'

    C.EProofApp e ->
      case fastSchemaOf (envC env) e of
        C.Forall [] (p : _ps) _ty
          | isErasedProp p -> importExpr sc env e
          | otherwise ->
            do e' <- importExpr sc env e
               prf <- proveProp sc env p
               scApply sc e' prf
        s ->
            panic "importExpr" [
                "EProofApp: invalid type",
                "Expr: " <> Text.pack (pretty expr),
                "Schema: " <> Text.pack (pretty s)
            ]

    C.EWhere e dgs ->
      do env' <- importDeclGroups sc env dgs
         importExpr sc env' e

    C.ELocated _ e ->
      importExpr sc env e

    C.EPropGuards arms typ -> do
      -- Convert prop guards to nested if-then-elses
      typ' <- importType sc env typ
      errMsg <- scString sc "No constraints satisfied in constraint guard"
      err <- scGlobalApply sc "Prelude.error" [typ', errMsg]
      -- NOTE: Must use a right fold to maintain order of prop guards in
      -- generated if-then-else
      Fold.foldrM (propGuardToIte typ') err arms

    C.ECase s alts dflt -> do
      let ty = fastTypeOf (envC env) expr
          -- need the type of whole expression as a type-arg in SAWCore
      importCase sc env ty s alts dflt

  where
    -- XXX find this a better name
    the :: Text -> Maybe a -> IO a
    the what = maybe (panic "importExpr" ["Internal type error", what]) return

    -- | Translate an erased 'Prop' to a term and return the conjunction of the
    -- translated term and 'mt' if 'mt' is 'Just'. Otherwise, return the
    -- translated 'Prop'.  This function is intended to be used in a fold,
    -- taking a 'Maybe' in the first argument to avoid creating an unnecessary
    -- conjunction over singleton lists.
    conjoinErasedProps :: Maybe Term -> C.Prop -> IO (Maybe Term)
    conjoinErasedProps mt p = do
      p' <- importNumericConstraintAsBool sc env p
      case mt of
        Just t -> Just <$> scAnd sc t p'
        Nothing -> pure $ Just p'

    -- | A helper function to be used in a fold converting a prop guard to an
    -- if-then-else. In order, the arguments of the function are:
    -- 1. The type of the prop guard
    -- 2. An arm of the prop guard
    -- 3. A term representing the else branch of the if-then-else
    propGuardToIte :: Term -> ([C.Prop], C.Expr) -> Term -> IO Term
    propGuardToIte typ (props, body) falseBranch = do
      mCondition <- Fold.foldlM conjoinErasedProps Nothing props
      condition <- maybe (scBool sc True) pure mCondition
      trueBranch <- importExpr sc env body
      scGlobalApply sc "Prelude.ite" [typ, condition, trueBranch, falseBranch]


-- | Convert a Cryptol expression with the given type schema to a
-- SAWCore term. Calling 'scTypeOf' on the result of @'importExpr''
-- sc env schema expr@ must yield a type that is equivalent (i.e.
-- convertible) with the one returned by @'importSchema' sc env
-- schema@.
--
-- Essentially, this function should be used when the expression's type is known
-- (such as with a type annotation), and 'importExpr' should be used when the
-- type must be inferred.
importExpr' :: HasCallStack => SharedContext -> Env -> C.Schema -> C.Expr -> IO Term
importExpr' sc env schema expr =
  case expr of
    C.ETuple es ->
      do ty <- the "Expected a mono type in ETuple" (C.isMono schema)
         ts <- the "Expected a tuple type in ETuple" (C.tIsTuple ty)
         es' <- sequence (zipWith go ts es)
         scTuple sc es'

    C.ERec fm ->
      do ty <- the "Expected a mono type in ERec" (C.isMono schema)
         tm <- the "Expected a record type in ERec" (C.tIsRec ty)
         es' <- sequence (zipWith go (map snd (C.canonicalFields tm)) (map snd (C.canonicalFields fm)))
         scTuple sc es'

    C.EIf e1 e2 e3 ->
      do ty  <- the "Expected a mono type in EIf" (C.isMono schema)
         ty' <- importType sc env ty
         e1' <- importExpr sc env e1
         e2' <- importExpr' sc env schema e2
         e3' <- importExpr' sc env schema e3
         scGlobalApply sc "Prelude.ite" [ty', e1', e2', e3']

    C.ETAbs tp e ->
      do schema' <-
           case schema of
             C.Forall (tp1 : tparams) props ty ->
               let s = C.singleTParamSubst tp1 (C.TVar (C.TVBound tp))
               in return (C.Forall tparams (map (plainSubst s) props) (plainSubst s ty))
             C.Forall [] _ _ ->
               panic "importExpr'" [
                   "Unexpected empty params in type abstraction (ETAbs)",
                   "   " <> Text.pack (show expr)
               ]
         (env',v) <- bindTParam sc tp env
         e' <- importExpr' sc env' schema' e
         scAbstractTerms sc [v] e'

    C.EAbs x _ e ->
      do ty <- the "expected a mono schema in EAbs" (C.isMono schema)
         (a, b) <- the "expected a function type in EAbs" (C.tIsFun ty)
         (env',v,_) <- bindName sc x (C.tMono a) env
         e' <- importExpr' sc env' (C.tMono b) e
         scAbstractTerms sc [v] e'

    C.EProofAbs _ e ->
      do (prop, schema') <-
           case schema of
             C.Forall [] (p : ps) ty -> return (p, C.Forall [] ps ty)
             C.Forall as ps _ ->
                let nas = Text.pack $ show $ length as
                    nps = Text.pack $ show $ length ps
                in
                panic "importExpr'" [
                    "Internal type error: unexpected schema in EProofAbs",
                    "   Found " <> nas <> " variables, expected none",
                    "   Found " <> nps <> " predicates, expected at least one",
                    "Schema: " <> Text.pack (pretty schema)
                ]
         if isErasedProp prop
           then importExpr' sc env schema' e
           else do (env',v) <- bindProp sc prop "_P" env
                   e' <- importExpr' sc env' schema' e
                   scAbstractTerms sc [v] e'

    C.EWhere e dgs ->
      do env' <- importDeclGroups sc env dgs
         importExpr' sc env' schema e

    C.ELocated _ e ->
      importExpr' sc env schema e

    C.ECase     {} -> fallback
    C.EList     {} -> fallback
    C.ESel      {} -> fallback
    C.ESet      {} -> fallback
    C.EComp     {} -> fallback
    C.EVar      {} -> fallback
    C.EApp      {} -> fallback
    C.ETApp     {} -> fallback
    C.EProofApp {} -> fallback
    C.EPropGuards {} -> fallback

  where
    go :: C.Type -> C.Expr -> IO Term
    go t = importExpr' sc env (C.tMono t)

    -- XXX find this a better name
    the :: Text -> Maybe a -> IO a
    the what = maybe (panic "importExpr" ["Internal type error", what]) return

    fallback :: IO Term
    fallback =
      do let t1 = fastTypeOf (envC env) expr
         t2 <- the "fallback: schema is not mono" (C.isMono schema)
         expr' <- importExpr sc env expr
         coerceTerm sc env t1 t2 expr'

tupleUpdate :: SharedContext -> Term -> Int -> [Term] -> IO Term
tupleUpdate _ f 0 [_] = return f
tupleUpdate sc f 0 (a : ts) =
  do b <- scTupleType sc ts
     scGlobalApply sc "Cryptol.updFst" [a, b, f]
tupleUpdate sc f n (a : ts) =
  do g <- tupleUpdate sc f (n - 1) ts
     b <- scTupleType sc ts
     scGlobalApply sc "Cryptol.updSnd" [a, b, g]
tupleUpdate _ _ _ [] = panic "tupleUpdate" ["empty tuple"]

-- | Apply a substitution to a type *without* simplifying
-- constraints like @Ring [n]a@ to @Ring a@. (This is in contrast to
-- 'apSubst', which performs simplifications wherever possible.)
plainSubst :: C.Subst -> C.Type -> C.Type
plainSubst s ty =
  case ty of
    C.TCon tc ts   -> C.TCon tc (map (plainSubst s) ts)
    C.TUser f ts t -> C.TUser f (map (plainSubst s) ts) (plainSubst s t)
    C.TRec fs      -> C.TRec (fmap (plainSubst s) fs)
    C.TVar x       -> C.apSubst s (C.TVar x)
    C.TNominal nt ts -> C.TNominal nt (fmap (plainSubst s) ts)


-- | Generate a URI representing a cryptol name from a sequence of
--   name parts representing the fully-qualified name.  If a \"unique\"
--   value is given, this represents a dynamically bound name in
--   the \"\<interactive\>\" pseudo-module, and the unique value will
--   be incorporated into the name as a fragment identifier.
--   At least one name component must be supplied.
--
--   Some examples:
--
--   * @Cryptol::foldl@ ---> @cryptol:\/Cryptol\/foldl@
--   * @MyModule::SubModule::name@ ---> @cryptol:\/MyModule\/SubModule\/name@
--   * @\<interactive\>::f@ ---> @cryptol:f#1234@
--
--   In the above example, 1234 is the unique integer value provided with the name.

cryptolURI ::
  [Text] {- ^ Name components  -} ->
  Maybe Int {- ^ unique integer for dynamic names -} ->
  URI
cryptolURI [] _ = panic "cryptolURI" ["Could not make URI from empty path"]
cryptolURI (p:ps) Nothing =
  fromMaybe (panic "cryptolURI" ["Could not make URI from path: " <> Text.pack (show (p:ps))]) $
  do sch <- mkScheme "cryptol"
     path' <- mapM mkPathPiece (p:|ps)
     pure URI
       { uriScheme = Just sch
       , uriAuthority = Left True -- absolute path
       , uriPath = Just (False, path')
       , uriQuery = []
       , uriFragment = Nothing
       }
cryptolURI (p:ps) (Just uniq) =
  fromMaybe (panic "cryptolURI" ["Could not make URI from path: " <> Text.pack (show (p:ps)), "Fragment: " <> Text.pack (show uniq)]) $
  do sch <- mkScheme "cryptol"
     path' <- mapM mkPathPiece (p:|ps)
     frag <- mkFragment (Text.pack (show uniq))
     pure URI
       { uriScheme = Just sch
       , uriAuthority = Left False -- relative path
       , uriPath = Just (False, path')
       , uriQuery = []
       , uriFragment = Just frag
       }


importName :: C.Name -> IO NameInfo
importName cnm =
  case C.nameInfo cnm of
    C.LocalName {} -> fail ("Cannot import non-top-level name: " ++ show cnm)
    C.GlobalName _ns og
      | C.ogModule og == C.TopModule C.interactiveName ->
          let shortNm = C.identText (C.nameIdent cnm)
              aliases = [shortNm]
              uri = cryptolURI [shortNm] (Just (C.nameUnique cnm))
           in pure (ImportedName uri aliases)

      | otherwise ->
          let (topMod, nested) = C.modPathSplit (C.ogModule og)
              topChunks = C.modNameChunksText topMod
              modNms    = topChunks ++ map C.identText nested
              -- If the name came from a module parameter, add the module
              -- parameter identifier to distinguish between names that have the
              -- same identifier but come from different module parameters (see
              -- #1892)
              ifaceNms  = case C.ogFromParam og of
                            Just i  -> [C.identText i]
                            Nothing -> []
              shortNm   = C.identText (C.nameIdent cnm)
              nmParts   = modNms ++ ifaceNms ++ [shortNm]
              longNm    = Text.intercalate "::" nmParts
              aliases   = [shortNm, longNm]
              uri       = cryptolURI nmParts Nothing
           in pure (ImportedName uri aliases)

-- | Currently this imports declaration groups by inlining all the
-- definitions. (With subterm sharing, this is not as bad as it might
-- seem.) We might want to think about generating let or where
-- expressions instead.
--
-- For Cryptol @foreign@ declarations, we import them as regular
-- Cryptol expressions if a Cryptol implementation exists, and as an
-- opaque constant otherwise.
importDeclGroup :: DeclGroupOptions -> SharedContext -> Env -> C.DeclGroup -> IO Env
importDeclGroup declOpts sc env0 (C.Recursive decls) =
  case decls of
    [decl] ->
      case C.dDefinition decl of

        C.DPrim ->
          panic "importDeclGroup" [
              "Primitive declarations cannot be recursive (single decl): " <> Text.pack (show (C.dName decl)),
              "   " <> Text.pack (pretty decl)
          ]

        C.DForeign _ mexpr ->
          case mexpr of
            Nothing -> panicForeignNoExpr decl
            Just expr -> addExpr expr

        C.DExpr expr ->
          addExpr expr

      where
      addExpr expr = do
        let ty = C.dSignature decl
            nm = C.dName decl
        (env1,v,t') <- bindName sc nm ty env0
        e' <- importExpr' sc env1 ty expr
        f' <- scAbstractTerms sc [v] e'
        rhs <- scGlobalApply sc "Prelude.fix" [t', f']
        rhs' <- case declOpts of
                  TopLevelDeclGroup _ ->
                    do nmi <- importName nm
                       scDefineConstant sc nmi rhs t'
                  NestedDeclGroup ->
                    return rhs
        return env0 { envE = Map.insert nm rhs' (envE env0)
                    , envC = Map.insert nm ty   (envC env0)
                    }

    -- - A group of mutually-recursive declarations -
    -- We handle this by "tupling up" all the declarations using a record and
    -- taking the fixpoint at this record type.  The desired declarations are
    -- then achieved by projecting the field names from this record.
    _ -> do
      -- build the environment for the declaration bodies
      let dm = Map.fromList [ (C.dName d, d) | d <- decls ]

      -- the types of the declarations
      tm <- traverse (importSchema sc env0 . C.dSignature) dm

      -- the type of the recursive record
      rect <- scRecordType sc (Map.assocs $ Map.mapKeys nameToFieldName tm)

      -- grab a reference to the outermost variable; this will be the record
      -- in the body of the lambda we build later
      v0 <- scFreshVariable sc "fixRecord" rect

      -- build a list of projections from a record variable
      vm <- traverse (scRecordSelect sc v0 . nameToFieldName . C.dName) dm

      -- the raw imported bodies of the declarations
      em <- do
            let
                -- | In env2 the names of the recursively-defined
                -- functions/values are bound to projections from the
                -- local variable of the fixed-point operator (for use
                -- in translating the definition bodies).
                env2 =
                  env0 { envE = Map.union vm                     (envE env0)
                       , envC = Map.union (fmap C.dSignature dm) (envC env0)
                       }

                extractDeclExpr decl =
                  case C.dDefinition decl of
                    C.DExpr expr ->
                      importExpr' sc env2 (C.dSignature decl) expr
                    C.DForeign _ mexpr ->
                      case mexpr of
                        Nothing -> panicForeignNoExpr decl
                        Just expr ->
                          importExpr' sc env2 (C.dSignature decl) expr
                    C.DPrim ->
                      panic "importDeclGroup" [
                        "Primitive declarations cannot be recursive (multiple decls): "
                        <> Text.pack (show (C.dName decl))
                      , "   " <> Text.pack (pretty decl)
                      ]

            traverse extractDeclExpr dm

      -- the body of the recursive record
      recv <- scRecord sc (Map.mapKeys nameToFieldName em)

      -- build a lambda from the record body...
      f <- scAbstractTerms sc [v0] recv

      -- and take its fixpoint
      rhs <- scGlobalApply sc "Prelude.fix" [rect, f]

      -- finally, build projections from the fixed record to shove
      -- into the environment if toplevel, then wrap each binding with
      -- a Constant constructor
      let mkRhs d t =
            do let s = nameToFieldName (C.dName d)
               r <- scRecordSelect sc rhs s
               case declOpts of
                 TopLevelDeclGroup _ ->
                   do nmi <- importName (C.dName d)
                      scDefineConstant sc nmi r t
                 NestedDeclGroup -> return r
      rhss <- sequence (Map.intersectionWith mkRhs dm tm)

     -- NOTE: The envE fields of env2 and the following Env
     -- are different.  The same names bound in env2 are now bound to
     -- the output of the fixed-point operator:
      return env0 { envE = Map.union rhss                   (envE env0)
                  , envC = Map.union (fmap C.dSignature dm) (envC env0)
                  }

  where
  panicForeignNoExpr decl = panic "importDeclGroup" [
      "Foreign declaration without Cryptol body in recursive group: " <>
          Text.pack (show (C.dName decl)),
      "   " <> Text.pack (pretty decl)
    ]

importDeclGroup declOpts sc env (C.NonRecursive decl) = do
  rhs <- case C.dDefinition decl of
    C.DForeign _ mexpr
      | TopLevelDeclGroup _ <- declOpts ->
        case mexpr of
          Nothing -> importOpaque sc env (C.dName decl) (C.dSignature decl)
          Just expr -> do
            rhs <- importExpr' sc env (C.dSignature decl) expr
            importConstant sc env (C.dName decl) (C.dSignature decl) rhs
      | otherwise ->
        panic "importDeclGroup" [
            "Foreign declarations only allowed at top level: " <>
                Text.pack (show (C.dName decl))
        ]

    C.DPrim
      | TopLevelDeclGroup primOpts <- declOpts ->
        importPrimitive sc primOpts env (C.dName decl) (C.dSignature decl)
      | otherwise ->
        panic "importDeclGroup" [
            "Primitive declarations only allowed at top-level: " <>
                Text.pack (show (C.dName decl))
        ]

    C.DExpr expr -> do
      rhs <- importExpr' sc env (C.dSignature decl) expr
      case declOpts of
        TopLevelDeclGroup _ ->
          importConstant sc env (C.dName decl) (C.dSignature decl) rhs
        NestedDeclGroup -> return rhs

  pure env { envE = Map.insert (C.dName decl) rhs (envE env)
           , envC = Map.insert (C.dName decl) (C.dSignature decl) (envC env)
           }


data ImportPrimitiveOptions =
  ImportPrimitiveOptions
  { allowUnknownPrimitives :: Bool
    -- ^ Should unknown primitives be translated as fresh external constants?
  }

defaultPrimitiveOptions :: ImportPrimitiveOptions
defaultPrimitiveOptions =
  ImportPrimitiveOptions
  { allowUnknownPrimitives = True
  }

data DeclGroupOptions
  = TopLevelDeclGroup ImportPrimitiveOptions
  | NestedDeclGroup

importDeclGroups :: SharedContext -> Env -> [C.DeclGroup] -> IO Env
importDeclGroups sc = foldM (importDeclGroup NestedDeclGroup sc)

importTopLevelDeclGroups :: SharedContext -> ImportPrimitiveOptions -> Env -> [C.DeclGroup] -> IO Env
importTopLevelDeclGroups sc primOpts = foldM (importDeclGroup (TopLevelDeclGroup primOpts) sc)

coerceTerm :: SharedContext -> Env -> C.Type -> C.Type -> Term -> IO Term
coerceTerm sc env t1 t2 e
  | t1 == t2 = do return e
  | otherwise =
    do t1' <- importType sc env t1
       t2' <- importType sc env t2
       same <- scSubtype sc t1' t2'
       case same of
         True -> pure e -- ascribe type t2' to e
         False ->
           do q <- proveEq sc env t1 t2
              scGlobalApply sc "Prelude.coerce" [t1', t2', q, e]

proveEq :: SharedContext -> Env -> C.Type -> C.Type -> IO Term
proveEq sc env t1 t2
  | t1 == t2 =
    do s <- scSort sc (mkSort 0)
       t' <- importType sc env t1
       scGlobalApply sc "Prelude.Refl" [s, t']
  | otherwise =
    case (tNoUser t1, tNoUser t2) of
      (C.tIsSeq -> Just (n1, a1), C.tIsSeq -> Just (n2, a2)) ->
        do n1' <- importType sc env n1
           n2' <- importType sc env n2
           a1' <- importType sc env a1
           a2' <- importType sc env a2
           num <- scGlobalApply sc "Cryptol.Num" []
           nEq <- if n1 == n2
                  then scGlobalApply sc "Prelude.Refl" [num, n1']
                  else scGlobalApply sc "Prelude.unsafeAssert" [num, n1', n2']
           aEq <- proveEq sc env a1 a2
           if a1 == a2
             then scGlobalApply sc "Cryptol.seq_cong1" [n1', n2', a1', nEq]
             else scGlobalApply sc "Cryptol.seq_cong" [n1', n2', a1', a2', nEq, aEq]
      (C.tIsIntMod -> Just n1, C.tIsIntMod -> Just n2) ->
        do n1' <- importType sc env n1
           n2' <- importType sc env n2
           num <- scGlobalApply sc "Cryptol.Num" []
           nEq <- if n1 == n2
                  then scGlobalApply sc "Prelude.Refl" [num, n1']
                  else scGlobalApply sc "Prelude.unsafeAssert" [num, n1', n2']
           scGlobalApply sc "Cryptol.IntModNum_cong" [n1', n2', nEq]
      (C.tIsFun -> Just (a1, b1), C.tIsFun -> Just (a2, b2)) ->
        do a1' <- importType sc env a1
           a2' <- importType sc env a2
           b1' <- importType sc env b1
           b2' <- importType sc env b2
           aEq <- proveEq sc env a1 a2
           bEq <- proveEq sc env b1 b2
           scGlobalApply sc "Cryptol.fun_cong" [a1', a2', b1', b2', aEq, bEq]
      (tIsPair -> Just (a1, b1), tIsPair -> Just (a2, b2)) ->
        do a1' <- importType sc env a1
           a2' <- importType sc env a2
           b1' <- importType sc env b1
           b2' <- importType sc env b2
           aEq <- proveEq sc env a1 a2
           bEq <- proveEq sc env b1 b2
           if b1 == b2
             then scGlobalApply sc "Cryptol.pair_cong1" [a1', a2', b1', aEq]
             else if a1 == a2
                  then scGlobalApply sc "Cryptol.pair_cong2" [a1', b1', b2', bEq]
                  else scGlobalApply sc "Cryptol.pair_cong" [a1', a2', b1', b2', aEq, bEq]
      (C.tIsRec -> Just tm1, C.tIsRec -> Just tm2)
        | map fst (C.canonicalFields tm1) == map fst (C.canonicalFields tm2) ->
          proveEq sc env (C.tTuple (map snd (C.canonicalFields tm1))) (C.tTuple (map snd (C.canonicalFields tm2)))

      (C.tIsNominal -> Just (C.NominalType{C.ntDef=C.Enum _},_),
       C.tIsNominal -> Just (C.NominalType{C.ntDef=C.Enum _},_)) ->
        panic "proveEq" [
            "Enum types unsupported.",
            "Found: " <> Text.pack (pretty t1) <> " and " <> Text.pack (pretty t2)
        ]

        -- XXX: add a case for `enum`
        -- 1. Match constructors by names, and prove fields as tuples
        -- 2. We need some way to combine the proofs of equality of
        -- the fields, into a proof for equality of the whole type
        -- for sums
        --
        -- XXX: Response to above: Not sure what purpose of `proveEq`
        -- is, but wouldn't Enum types have name (not structural)
        -- equality?

      (_, _) ->
        panic "proveEq" [
            "Internal type error:",
            "t1: " <> Text.pack (pretty t1),
            "t2: " <> Text.pack (pretty t2)
        ]


-- | Resolve user types (type aliases and newtypes) to their simpler SAW-compatible forms.
tNoUser :: C.Type -> C.Type
tNoUser initialTy =
  case C.tNoUser initialTy of
    C.TNominal nt params
      | C.Struct fs <- C.ntDef nt ->
        if null params then
            C.TRec (C.ntFields fs)
        else
            -- XXX: We should instantiate, see #2019
            panic "tNoUser" [
                "Nominal type with parameters: " <> Text.pack (pretty initialTy)
            ]
    t -> t


-- | Deconstruct a Cryptol tuple type as a pair according to the
-- SAWCore tuple type encoding.
tIsPair :: C.Type -> Maybe (C.Type, C.Type)
tIsPair t =
  do ts <- C.tIsTuple t
     case ts of
       [] -> Nothing
       [t1, t2] -> Just (t1, t2)
       t1 : ts' -> Just (t1, C.tTuple ts')


--------------------------------------------------------------------------------
-- List comprehensions

importComp :: SharedContext -> Env -> C.Type -> C.Type -> C.Expr -> [[C.Match]] -> IO Term
importComp sc env lenT elemT expr mss =
  do let zipAll [] = panic "importComp" ["zero-branch list comprehension"]
         zipAll [branch] =
           do (xs, len, ty, args) <- importMatches sc env branch
              m <- importType sc env len
              a <- importType sc env ty
              return (xs, m, a, [args], len)
         zipAll (branch : branches) =
           do (xs, len, ty, args) <- importMatches sc env branch
              m <- importType sc env len
              a <- importType sc env ty
              (ys, n, b, argss, len') <- zipAll branches
              ab <- scTupleType sc [a, b]
              if len == len' then
                do zs <- scGlobalApply sc "Cryptol.seqZipSame" [a, b, m, xs, ys]
                   return (zs, m, ab, args : argss, len)
              else
                do zs <- scGlobalApply sc "Cryptol.seqZip" [a, b, m, n, xs, ys]
                   mn <- scGlobalApply sc "Cryptol.tcMin" [m, n]
                   return (zs, mn, ab, args : argss, C.tMin len len')
     (xs, n, a, argss, lenT') <- zipAll mss
     f <- lambdaTuples sc env elemT expr argss
     b <- importType sc env elemT
     ys <- scGlobalApply sc "Cryptol.seqMap" [a, b, n, f, xs]
     -- The resulting type might not match the annotation, so we coerce
     coerceTerm sc env (C.tSeq lenT' elemT) (C.tSeq lenT elemT) ys

lambdaTuples :: SharedContext -> Env -> C.Type -> C.Expr -> [[(C.Name, C.Type)]] -> IO Term
lambdaTuples sc env _ty expr [] = importExpr sc env expr
lambdaTuples sc env ty expr (args : argss) =
  do f <- lambdaTuple sc env ty expr argss args
     if null args || null argss
       then return f
       else do a <- importType sc env (tNestedTuple (map snd args))
               b <- importType sc env (tNestedTuple (map (tNestedTuple . map snd) argss))
               c <- importType sc env ty
               scGlobalApply sc "Prelude.uncurry" [a, b, c, f]

lambdaTuple :: SharedContext -> Env -> C.Type -> C.Expr -> [[(C.Name, C.Type)]] -> [(C.Name, C.Type)] -> IO Term
lambdaTuple sc env ty expr argss [] = lambdaTuples sc env ty expr argss
lambdaTuple sc env ty expr argss ((x, t) : args) =
  do a <- importType sc env t
     (env',x',_) <- bindName sc x (C.Forall [] [] t) env
     e <- lambdaTuple sc env' ty expr argss args
     f <- scAbstractTerms sc [x'] e
     if null args
        then return f
        else do b <- importType sc env (tNestedTuple (map snd args))
                let tuple = tNestedTuple (map (tNestedTuple . map snd) argss)
                c <- importType sc env (if null argss then ty else C.tFun tuple ty)
                scGlobalApply sc "Prelude.uncurry" [a, b, c, f]

tNestedTuple :: [C.Type] -> C.Type
tNestedTuple [] = C.tTuple []
tNestedTuple [t] = t
tNestedTuple (t : ts) = C.tTuple [t, tNestedTuple ts]


-- | Returns the shared term, length type, element tuple type, bound
-- variables.
--
-- XXX: clean up the cutpaste
importMatches :: SharedContext -> Env -> [C.Match]
              -> IO (Term, C.Type, C.Type, [(C.Name, C.Type)])
importMatches _sc _env [] =
    panic "importMatches" ["empty comprehension branch"]

importMatches sc env [C.From name _len _eltty expr] = do
  (len, ty) <- case C.tIsSeq (fastTypeOf (envC env) expr) of
    Just x -> return x
    Nothing ->
      panic "importMatches" [
          "Type mismatch (From): " <> Text.pack (show (fastTypeOf (envC env) expr)),
          "   " <> Text.pack (pretty expr)
      ]
  xs <- importExpr sc env expr
  return (xs, len, ty, [(name, ty)])

importMatches sc env (C.From name _len _eltty expr : matches) = do
  (len1, ty1) <- case C.tIsSeq (fastTypeOf (envC env) expr) of
    Just x -> return x
    Nothing ->
      panic "importMatches" [
          "Type mismatch (From): " <> Text.pack (show (fastTypeOf (envC env) expr)),
          "   " <> Text.pack (pretty expr)
      ]
  m <- importType sc env len1
  a <- importType sc env ty1
  xs <- importExpr sc env expr
  (env',v,_) <- bindName sc name (C.Forall [] [] ty1) env
  (body, len2, ty2, args) <- importMatches sc env' matches
  n <- importType sc env len2
  b <- importType sc env ty2
  f <- scAbstractTerms sc [v] body

  result <- scGlobalApply sc "Cryptol.from" [a, b, m, n, xs, f]
  return (result, C.tMul len1 len2, C.tTuple [ty1, ty2], (name, ty1) : args)

importMatches sc env [C.Let decl]
  | C.DPrim <- C.dDefinition decl =
     panic "importMatches" [
         "Primitive declarations not allowed in 'let':" <> Text.pack (show (C.dName decl)),
         "   " <> Text.pack (pretty decl)
     ]
  | C.DExpr expr <- C.dDefinition decl = do
     e <- importExpr sc env expr
     ty1 <- case C.dSignature decl of
              C.Forall [] [] ty1 -> return ty1
              _ -> panic "importMatches" [
                       "Unimplemented: polymorphic Let",
                       "   " <> Text.pack (pretty decl)
                   ]
     a <- importType sc env ty1
     result <- scGlobalApply sc "Prelude.single" [a, e]
     return (result, C.tOne, ty1, [(C.dName decl, ty1)])

importMatches sc env (C.Let decl : matches) =
  case C.dDefinition decl of

    C.DForeign {} ->
      panic "importMatches" [
          "Foreign declarations not allowed in 'let':" <> Text.pack (show (C.dName decl)),
          "   " <> Text.pack (pretty decl)
      ]

    C.DPrim ->
      panic "importMatches" [
          "Primitive declarations not allowed in 'let':" <> Text.pack (show (C.dName decl)),
          "   " <> Text.pack (pretty decl)
      ]

    C.DExpr expr -> do
     e <- importExpr sc env expr
     ty1 <- case C.dSignature decl of
              C.Forall [] [] ty1 -> return ty1
              _ -> panic "importMatches" [
                       "Unimplemented: polymorphic Let",
                       "   " <> Text.pack (pretty decl)
                   ]
     (env', v, _) <- bindName sc (C.dName decl) (C.dSignature decl) env
     (body, len, ty2, args) <- importMatches sc env' matches
     n <- importType sc env len
     a <- importType sc env ty1
     b <- importType sc env ty2
     f <- scAbstractTerms sc [v] body
     result <- scGlobalApply sc "Cryptol.mlet" [a, b, n, e, f]
     return (result, len, C.tTuple [ty1, ty2], (C.dName decl, ty1) : args)


--------------------------------------------------------------------------------
-- Utilities:

-- | assertSAWCoreTypeChecks sc nm term mType - typeChecks (SAWCore) @term@.
--     if @mType == Just type'@ then ensure the following
--         term :: type'
--
--   This code is used for sanity checks during code generation, like assert.
--
--   FIXME: Currently we have made parts of this function un-reachable to
--     reduce the run-time impact of this check.  A better, long-term,
--     project-wide solution would be desirable: how to dial up run-time checks for
--     [integration] tests, but dial down run-time checks for general use.
--
assertSAWCoreTypeChecks :: Show i => SharedContext -> i -> Term -> Maybe Term -> IO ()
assertSAWCoreTypeChecks sc ident term mType =
  do result <- SC.scTypeCheck sc term
     case result of
       Right ty1 ->
           case mType of
             Nothing  ->
               pure ()
             Just ty2 ->
               when False $
                 -- N.B. currently unreachable to reduce run-time impact:
                 do
                 eq <- scConvertible sc True ty1 ty2
                 unless eq $
                   panic "assertSAWCoreTypeChecks" [
                       "Expected type " <> Text.pack (showTerm ty1),
                       "does not match the inferred type " <> Text.pack (showTerm ty2)
                   ]
       Left err ->
           panic "assertSAWCoreTypeChecks" ([
               "Internal type error when checking " <> Text.pack (show ident) <> ":"
           ] ++
               map Text.pack (SC.prettyTCError err)
           )


-- | When possible, convert back from a SAWCore type to a Cryptol Type, or Kind.
scCryptolType :: SharedContext -> Term -> IO (Maybe (Either C.Kind C.Type))
scCryptolType sc t =
  do modmap <- scGetModuleMap sc
     catch
       (case SC.evalSharedTerm modmap Map.empty Map.empty t of
           -- NOTE: we make sure that asCryptolTypeValue gets evaluated, to
           -- ensure that any panics in the simulator get caught here
           SC.TValue tv
             | Just !ret <- asCryptolTypeValue tv -> return $ Just ret
           _ -> return Nothing)
       (\ (_::SomeException) -> return Nothing)


  where

  asCryptolTypeValue :: SC.TValue SC.Concrete -> Maybe (Either C.Kind C.Type)
  asCryptolTypeValue v =
    case v of
      SC.VBoolType -> return (Right C.tBit)
      SC.VIntType -> return (Right C.tInteger)
      SC.VIntModType n -> return (Right (C.tIntMod (C.tNum n)))
      SC.VArrayType v1 v2 -> do
        Right t1 <- asCryptolTypeValue v1
        Right t2 <- asCryptolTypeValue v2
        return (Right (C.tArray t1 t2))
      SC.VVecType n v2 -> do
        Right t2 <- asCryptolTypeValue v2
        return (Right (C.tSeq (C.tNum n) t2))

      SC.VDataType (nameInfo -> ModuleIdentifier "Prelude.Stream") [SC.TValue v1] [] ->
          do Right t1 <- asCryptolTypeValue v1
             return (Right (C.tSeq C.tInf t1))

      SC.VDataType (nameInfo -> ModuleIdentifier "Cryptol.Num") [] [] ->
        return (Left C.KNum)

      SC.VDataType {} -> Nothing

      SC.VUnitType -> return (Right (C.tTuple []))
      SC.VPairType v1 v2 -> do
        Right t1 <- asCryptolTypeValue v1
        Right t2 <- asCryptolTypeValue v2
        case C.tIsTuple t2 of
          Just ts -> return (Right (C.tTuple (t1 : ts)))
          Nothing -> return (Right (C.tTuple [t1, t2]))

      SC.VPiType v1 (SC.VNondependentPi v2) ->
        do Right t1 <- asCryptolTypeValue v1
           Right t2 <- asCryptolTypeValue v2
           return (Right (C.tFun t1 t2))

      SC.VSort s
        | s == mkSort 0 -> return (Left C.KType)
        | otherwise     -> Nothing

      -- TODO?
      SC.VPiType _v1 (SC.VDependentPi _) -> Nothing
      SC.VStringType -> Nothing
      SC.VRecordType{} -> Nothing
      SC.VTyTerm{} -> Nothing

--------------------------------------------------------------------------------
-- exporting functions:

-- | Convert from SAWCore's Value type to Cryptol's, guided by the
-- Cryptol type schema.
exportValueWithSchema :: C.Schema -> SC.CValue -> V.Eval V.Value
exportValueWithSchema (C.Forall [] [] ty) v = exportValue (evalValType mempty ty) v
exportValueWithSchema _ _ = pure (V.VPoly mempty (error "exportValueWithSchema"))
-- TODO: proper support for polymorphic values

exportValue :: TV.TValue -> SC.CValue -> V.Eval V.Value
exportValue ty v = case ty of

  TV.TVBit ->
    pure (V.VBit (SC.toBool v))

  TV.TVInteger ->
    pure (V.VInteger (case v of SC.VInt x -> x; _ -> error "exportValue: expected integer"))

  TV.TVIntMod _modulus ->
    pure (V.VInteger (case v of SC.VIntMod _ x -> x; _ -> error "exportValue: expected intmod"))

  TV.TVArray{} -> panic "exportValue" ["Not yet implemented: array type: " <> Text.pack (pretty (TV.tValTy ty))]

  TV.TVRational -> panic "exportValue" ["Not yet implemented: Rational"]

  TV.TVFloat _ _ -> panic "exportValue" ["Not yet implemented: Float"]

  TV.TVSeq _ e ->
    case v of
      SC.VWord w -> V.word V.Concrete (toInteger (width w)) (unsigned w)
      SC.VVector xs
        | TV.isTBit e -> V.VWord <$>
            V.bitmapWordVal V.Concrete (toInteger (Vector.length xs))
                 (V.finiteSeqMap V.Concrete . map (V.ready . SC.toBool . SC.runIdentity . force) $ Fold.toList xs)
        | otherwise   -> V.mkSeq V.Concrete (C.Nat (toInteger (Vector.length xs))) e $ V.finiteSeqMap V.Concrete $
                            map (\x -> exportValue e (SC.runIdentity (force x))) (Vector.toList xs)
      _ -> error $ "exportValue (on seq type " ++ show ty ++ ")"

  -- infinite streams
  TV.TVStream e ->
    case v of
      SC.VExtra (SC.CStream trie) -> pure $ V.VStream (V.indexSeqMap $ \i -> exportValue e (IntTrie.apply trie i))
      _ -> error $ "exportValue (on seq type " ++ show ty ++ ")"

  -- tuples
  TV.TVTuple etys -> pure $ V.VTuple $ exportTupleValue etys v

  -- records
  TV.TVRec fields ->
      pure . V.VRecord . C.recordFromFieldsWithDisplay (C.displayOrder fields) $ exportRecordValue (C.canonicalFields fields) v

  -- functions
  TV.TVFun _aty _bty ->
    pure $ V.VFun mempty (error "exportValue: TODO functions")

  -- nominal types
  TV.TVNominal _ _ fields ->
    case fields of
      TV.TVStruct fs   -> exportValue (TV.TVRec fs) v
      TV.TVEnum {}     -> error ("exportValue: TODO enum: " ++ show v)
      TV.TVAbstract {} -> error "exportValue: TODO abstract types"


exportTupleValue :: [TV.TValue] -> SC.CValue -> [V.Eval V.Value]
exportTupleValue tys v =
  case (tys, v) of
    ([]    , SC.VUnit    ) -> []
    ([t]   , _           ) -> [exportValue t v]
    (t : ts, SC.VPair x y) -> (exportValue t (run x)) : exportTupleValue ts (run y)
    _                      -> error $ "exportValue: expected tuple"
  where
    run = SC.runIdentity . force

exportRecordValue :: [(C.Ident, TV.TValue)] -> SC.CValue -> [(C.Ident, V.Eval V.Value)]
exportRecordValue fields v =
  case (fields, v) of
    ([]         , SC.VUnit    ) -> []
    ([(n, t)]   , _           ) -> [(n, exportValue t v)]
    ((n, t) : ts, SC.VPair x y) -> (n, exportValue t (run x)) : exportRecordValue ts (run y)
    (_, SC.VRecordValue (alistAllFields
                         (map (C.identText . fst) fields) -> Just ths)) ->
      zipWith (\(n,t) x -> (n, exportValue t (run x))) fields ths
    _                              -> error $ "exportValue: expected record"
  where
    run = SC.runIdentity . force

--------------------------------------------------------------------------------
-- Supporting Nominal Types:

-- | Generate functions, required by 'NominalType's, to be inserted into the
--   term environment.
--
--   - For 'C.Struct', make identity functions that take the record which
--     the newtype wraps.
--
--   - For 'C.Abstract', no functions need to be produced.
--
--   - 'C.Enum' will will create these definitions:
--     - multiple constructor functions (added to Cryptol Env)
--     - a number of 'internal' only SAWCore definitions:
--       - case function for the type (not used directly by Cryptol code).
--       - multiple definitions that define the Enum's representation
--         type in SAWCore

genCodeForNominalTypes ::
  HasCallStack =>
  SharedContext -> Map C.Name NominalType -> Env -> IO Env
genCodeForNominalTypes sc nominalMap env0 =
  foldM updateEnvForNominal env0 nominalMap

  where

    updateEnvForNominal :: Env -> NominalType -> IO Env
    updateEnvForNominal env nt = do
      let kinds = map C.tpKind (C.ntParams nt)
      unless (all (`elem` [C.KType, C.KNum]) kinds) $
        panic "genCodeForNominalTypes" [
            "Type parameters for nominal types must each have kind * or #:",
            Text.pack (show kinds)
          ]

      constrs <- newDefsForNominal env nt
      let conTs = C.nominalTypeConTypes nt
      return env { envE = foldr (uncurry Map.insert) (envE env) constrs
                 , envC = foldr (uncurry Map.insert) (envC env) conTs
                 }
        -- NOTE: the Cryptol schemas for the Struct & Enum constructors get added to
        --       the Cryptol environment.

    -- | Create functions/constructors for different 'NominalType's.
    newDefsForNominal ::
      HasCallStack => Env -> NominalType -> IO [(C.Name,Term)]
    newDefsForNominal env nt =
      case C.ntDef nt of
        C.Abstract  -> return []

        C.Enum x    -> genCodeForEnum sc env nt x
                        -- returns constructors, everything else put directly into
                        -- SAWCore environment.

        C.Struct fs -> do
            let recTy      = C.TRec (C.ntFields fs)
                conNm      = C.ntConName fs
                paramName  = C.asLocal C.NSValue conNm
                             -- NOTE: We use name of constructor as the
                             -- name of the constructor argument! Thus we can
                             -- avoid need for a new unique name.
                             --
                             -- FIXME: this doesn't seem foolproof!
                fn         = C.EAbs paramName recTy (C.EVar paramName)
                fnWithTAbs = foldr C.ETAbs fn (C.ntParams nt)
            e <- importExpr sc env fnWithTAbs
            return [(conNm, e)]


-- | genCodeForEnum ... - called when we see an "enum" definition in the Cryptol module.
--    - This action does two things
--       1. Returns the names & definitions of the constructors of the enum.
--          This fits with the code for other nominals, needed because
--          the "rest" of Cryptol code to be translated needs to see the
--          constructors in the Cryptol environments.
--       2. It adds many other definitions to the SAWCore environment
--          (in the sc :: SharedContext).  These definitions are only
--          used by other generated SAWCore code, so we don't need to
--          return this information back to the Cryptol environment(s).
--
--    - N.B. PLEASE refer to doc/developer/translating-enums.md for a
--      description of this translation at a more abstract level.  The
--      example there is what is used below to explain the below code
--      by SAWCore examples.  The running example we use is
--
--      > enum ETT ts = C1
--      >             | C2 Nat
--      >             | C3 Bool ts
--
--   FIXME: the uses of 'preludeName' should all be removed and new
--     definitions should be added to the module name being processed.
--     (At one point this was problematic, TODO: figure out and
--     resolve.)
--
genCodeForEnum ::
  HasCallStack =>
  SharedContext -> Env -> NominalType -> [C.EnumCon] -> IO [(C.Name,Term)]
genCodeForEnum sc env nt ctors =
  do
  let ntName'  = ntName nt
      numCtors = length ctors

  -------------------------------------------------------------
  -- Common code to handle type parameters of the nominal type:
  --  - `Variable`s are used to capture each of the type variables.

  -- The type parameters (`ts` in the example above)
  let tyParamsInfo  = C.ntParams nt

  -- | the kinds of the type Params:
  -- tyParamsKinds <- forM tyParamsInfo $ \tpi ->
  --                   importKind sc (C.tpKind tpi)
  -- | create variables for the type Params:
  -- tyParamsVars  <- mapM (scVariable sc) tyParamsECs

  (envWithTParams,tks) <-
    mapAccumLM
      (\env' tpi -> do
                    (env'',ty,k) <- bindTParam' sc tpi env'
                    return (env'', (ty,k))
      )
      env
      tyParamsInfo
  let (tyParamsVars, tyParamsKinds) = unzip tks


  let
      -- | @addTypeAbstractions t@ - create the SAWCore type
      --   abstractions around @t@ (holding the type Param references)
      addTypeAbstractions :: Term -> IO Term
      addTypeAbstractions t = scAbstractTerms sc tyParamsVars t

  -------------------------------------------------------------
  -- Common naming conventions:
  let sumTy_ident = identOfEnumType ntName'
      case_ident  = identOfEnumCase ntName'
      tl_ident    = newIdent ntName' "__LS"
                    -- name for the 'type list', type is ListSort (thus LS)

  -------------------------------------------------------------
  -- Definitions to access needed SAWCore Prelude types & definitions:
  sort0          <- scSort sc (mkSort 0)
  scListSort     <- scGlobalApply sc "Prelude.ListSort" []
  scLS_Nil       <- scGlobalApply sc "Prelude.LS_Nil"  []

  let scLS_Cons s ls   = scGlobalApply sc "Prelude.LS_Cons" [s,ls]

      scEithersV ls    = scGlobalApply sc "Prelude.EithersV" [ls]
      sc_eithersV b ls = scGlobalApply sc "Prelude.eithersV" [b,ls]

     -- to create values of the Either type:
      scLeft  a b x    = scGlobalApply sc "Prelude.Left"  [a,b,x]
      scRight a b x    = scGlobalApply sc "Prelude.Right" [a,b,x]

      scMakeListSort :: [Term] -> IO Term
      scMakeListSort = Fold.foldrM scLS_Cons scLS_Nil

      -- | scMakeFunsTo b tvs - create FunsTo list of type `FunsTo b`, given
      --    the list of (type, val :: type->b) pairs
      scMakeFunsTo :: Term -> [(Term,Term)] -> IO Term
      scMakeFunsTo b tvs =
        do
        scFunsTo_Nil <- scGlobalApply sc "Prelude.FunsTo_Nil"  [b]
        let scFunsTo_Cons (t,v) r =
              scGlobalApply sc "Prelude.FunsTo_Cons" [b,t,v,r]
        Fold.foldrM scFunsTo_Cons scFunsTo_Nil tvs

  -------------------------------------------------------------
  -- Create TypeList(tl) for the Enum, add to SAWCore environment:
  --  - elements of list are the elements of the Sum.
  --  - the types maintain the same exact type vars (see tyParamsInfo)
  -- Using the running example, we want to add the following to the
  -- SAWCore environment:
  --
  --   > ETT__LS : sort 0 -> ListSort;
  --   > ETT__LS ts = LS_Cons     (scTupleType [])
  --   >               (LS_Cons  (scTupleType [Nat])
  --   >                (LS_Cons (scTupleType [Bool,ts])
  --   >                  LS_Nil));

  --  cheating a little in the above syntax.
  --   - scTupleType is not SAWCore, it represents what's created with
  --     `scTupleType' function
  --   - using list syntax for the ListSort lists that are the arguments
  --     to the above.

  -- argTypes_eachCtor is the sum-of-products matrix for this enum type:
  (argTypes_eachCtor :: [[Term]]) <-
    forM ctors $ \c->     -- for each constructor
      forM (C.ecFields c) -- for each constructor field (type)
         (importType sc envWithTParams)

  -- map the list of types to the product type:
  represType_eachCtor <- forM argTypes_eachCtor $ \ts ->
                           scTupleType sc ts

  tl_rhs   <- addTypeAbstractions =<< scMakeListSort represType_eachCtor
  tl_type  <- scFunAll sc tyParamsKinds scListSort
  tl_tm    <- scDefineConstant sc (ModuleIdentifier tl_ident) tl_rhs tl_type

  -------------------------------------------------------------
  -- Create the definition for the SAWCore sum (to which we map the
  -- enum type).  For the running example we would see this:
  --
  -- > ETT : (ts : sort 0) -> sort 0;
  -- > ETT ts = EithersV (ETT__LS ts);
  --

  -- the Typelist(tl) applied to the type parameters.
  tl_applied <- scApplyAll sc tl_tm tyParamsVars

  sumTy_type <- scFunAll sc tyParamsKinds sort0
  sumTy_rhs  <- addTypeAbstractions =<< scEithersV tl_applied
  sumTy_tm   <- scDefineConstant sc (ModuleIdentifier sumTy_ident) sumTy_rhs sumTy_type

  -------------------------------------------------------------
  -- Create a `case` function specialized to the enum type.
  -- For the running example, we will define this:
  --
  --   > ETT_case  : (ts : sort 0)
  --   >          -> (b: sort 0)
  --   >          -> (arrowsType []        b)
  --   >          -> (arrowsType [Nat]     b)
  --   >          -> (arrowsType [Bool,ts] b)
  --   >          -> ETT ts
  --   >          -> b;
  --   > ETT_case ts b f1 f2 f3 =
  --   >   eithersV b
  --   >     (FunsTo_Cons b (ETT__ArgType_C1 ts) (\(x: scTupleType []       ) -> f1)
  --   >     (FunsTo_Cons b (ETT__ArgType_C2 ts) (\(x: scTupleType [Nat]    ) -> f2 x.1)
  --   >     (FunsTo_Cons b (ETT__ArgType_C3 ts) (\(x: scTupleType [Bool,ts]) -> f3 x.1 x.2)
  --   >     (FunsTo_Nil b))));
  --
  -- Using the same syntax cheats we did above.

  sumTy_applied <- scApplyAll sc sumTy_tm tyParamsVars

  let mkAltFuncTypes b = mapM (\ts->scFunAll sc ts b) argTypes_eachCtor
  case_type <-
      do
      b <- scFreshVariable sc "b" sort0
           -- all uses are direct under the 'Pi'
      altFuncTypes <- mkAltFuncTypes b
      scGeneralizeTerms sc tyParamsVars
        =<< scGeneralizeTerms sc [b] -- the scPi construct
        =<< scFunAll sc altFuncTypes
        =<< scFun sc sumTy_applied b

  case_rhs <-
      do
      -- Create needed vars for SAWCore expression
      --  - generating something like:
      --    \tyvars..-> \(b: sort)->(\f1 f2 ... ->
      --       eithersV b (FunsToCons b ... (\x-> f1 ...) ...)

      b <- scFreshVariable sc "b" sort0
      let funcNames = map (\n-> Text.pack ("f" ++ show n)) [1..numCtors]
      funcTypes <- mkAltFuncTypes b
      funcVars  <- zipWithM (scFreshVariable sc) funcNames funcTypes
      funcDefs  <- forM (zip3 funcVars represType_eachCtor ctors) $
                     \(funcVar,ty,ctor) ->
                         do
                         x <- scFreshVariable sc "x" ty
                         let n = length (C.ecFields ctor)
                         scAbstractTerms sc [x]
                           =<< scApplyAll sc funcVar
                           =<< forM [1..n]
                                 (\i-> scTupleSelector sc x i n)

      addTypeAbstractions
        =<< scAbstractTerms sc [b]
        =<< scAbstractTerms sc funcVars
        =<< sc_eithersV b
        =<< scMakeFunsTo b (zip represType_eachCtor funcDefs)

  _ <- scDefineConstant sc (ModuleIdentifier case_ident) case_rhs case_type

  assertSAWCoreTypeChecks sc case_ident case_rhs (Just case_type)

  -------------------------------------------------------------
  -- There's a bit of 'tedium' in creating the constructors, let's look at our
  -- running example, the SAWCore constructors we want are these:
  --
  --   > ```
  --   > C1 : (ts : sort 0) -> listSortGet (ETT__LS ts) 0 -> ETT ts;
  --   > C1 ts x =
  --   >   Left (listSortGet (ETT__LS ts) 0) (EithersV (listSortDrop (ETT__LS ts) 1))
  --   >        x;
  --   >
  --   > C2 : (ts : sort 0) -> listSortGet (ETT__LS ts) 1 -> ETT ts;
  --   > C2 ts x =
  --   >   Right (listSortGet (ETT__LS ts) 0) (EithersV (listSortDrop (ETT__LS ts) 1))
  --   >   (Left (listSortGet (ETT__LS ts) 1) (EithersV (listSortDrop (ETT__LS ts) 2))
  --   >    x);
  --   >
  --   > C3 : (ts : sort 0) -> listSortGet (ETT__LS ts) 2 -> ETT ts;
  --   > C3 ts x =
  --   >  Right   (listSortGet (ETT__LS ts) 0) (EithersV (listSortDrop (ETT__LS ts) 1))
  --   >   (Right (listSortGet (ETT__LS ts) 1) (EithersV (listSortDrop (ETT__LS ts) 2))
  --   >    (Left (listSortGet (ETT__LS ts) 2) (EithersV (listSortDrop (ETT__LS ts) 3))
  --   >    x));
  --   > ```
  --
  -- One can see that we try to encapsulate all the enum specific data in the
  -- @ETT__LS ts@ structure.


-------------------------------------------------------------
  -- Define function for N-th injection into the whole Sum (nested Either's):

  scNthInjection <-
      do
      -- Create needed SAWCore types for the Left/Right constructors
      -- (each Either in the nested Either's needs a pair of types):
      tps <- Vector.generateM numCtors $ \i->
               do
               typeLeft  <- do
                            n <- scNat sc (fromIntegral i)
                            scGlobalApply sc "Prelude.listSortGet"
                              [tl_applied, n]

               typeRight <- do
                            n <- scNat sc (fromIntegral i + 1)
                            tl_remainder <-
                              scGlobalApply sc "Prelude.listSortDrop"
                                [tl_applied, n]
                            scEithersV tl_remainder

               return (typeLeft, typeRight)

      let
        scInjectRight :: Int -> Term -> IO Term
        scInjectRight n x | n < 0     = return x
                          | otherwise = do
                              y <- scRight (fst (tps Vector.! n)) (snd (tps Vector.! n)) x
                              scInjectRight (n-1) y

        scNthInjection :: Int -> Term -> IO Term
        scNthInjection n x = do
                             y <- scLeft (fst (tps Vector.! n)) (snd (tps Vector.! n)) x
                             scInjectRight (n-1) y

      return scNthInjection

  -------------------------------------------------------------
  -- Create the definition for each constructor:
  defn_eachCtor <-
    forM (zip argTypes_eachCtor ctors) $
        \(argTypes, ctor)->
        do
        let
          ctorName   = C.ecName ctor
          ctorNumber = C.ecNumber ctor
          numArgs    = length argTypes

        -- NOTE: we don't add the constructor arguments to the Env, as
        -- the only references to these arguments are in the generated
        -- SAWCore code.

        -- create the vars (& names) for constructor arguments:
        let argNames = map (\x-> Text.pack ("x" ++ show x)) [0..numArgs-1]
        argVars <- zipWithM (scFreshVariable sc) argNames argTypes

        -- create the constructor:
        ctorBody <- addTypeAbstractions
                      =<< scAbstractTerms sc argVars
                      =<< scNthInjection ctorNumber
                      =<< scTuple sc argVars
        assertSAWCoreTypeChecks sc (C.nameIdent ctorName) ctorBody Nothing
        return (ctorName, ctorBody)

  return defn_eachCtor


-- | importCase - translates a Cryptol case expr to SAWCore: an application
--   of the generated SAWCore <NAME>__case function to appropriate arguments.
--
--   - Note missing functionality: (FIXME)
--     - not implemented yet: default case alternatives that bind the whole scrutinee,
--       i.e.,
--
--       >  case S of
--       >    C1 ... -> E
--       >    y      -> E[y]  -- y == S   <- NOT IMPLEMENTED YET
--
importCase ::
  HasCallStack =>
  SharedContext -> Env ->
  C.Type -> C.Expr -> Map C.Ident C.CaseAlt -> Maybe C.CaseAlt -> IO Term
importCase sc env b scrutinee altsMap mDfltAlt =
  do
  let scrutineeTy = fastTypeOf (envC env) scrutinee
  (nm,ctors,tyParams,tyArgs) <- case scrutineeTy of
      (C.tIsNominal -> Just (C.NominalType{C.ntDef=C.Enum ctors, ntName=nm, ntParams=tyParams},tyArgs))
        ->
          return (nm,ctors,tyParams,tyArgs)
      _ ->
          panic "importCase" [
              "`case` expression scrutinee is not an Enum type",
              Text.pack (pretty scrutineeTy)
          ]

  -- Create a sequential set of `C.CaseAlt`s that exactly match the
  -- constructors:
  --   - preconditions:
  --      Assume `altsMap` is valid, thus not checking for extraneous
  --      entries. (Call panic if a missing alternative is not covered
  --      by presence of default in `mDfltAlt`.)

  -- First, define what to do if alternative for constructor is missing:
  let
      -- | useDefaultAlt - when constructor (ctor) has no 'CaseAlt',
      -- create a ctor specific alt-function from the mDfltAlt
      -- "default expr".
      --   - For each constructor we may need to generate a default alternative,
      --     (the code cannot be shared as the arity and types for each constructor
      --     will be different).

      useDefaultAlt :: HasCallStack => C.EnumCon -> IO C.CaseAlt
      useDefaultAlt ctor = case mDfltAlt of
        Nothing ->
            panic "importCase" [
                "missing CaseAlt and no default CaseAlt: " <> Text.pack (show nm)
            ]
        Just (C.CaseAlt [(nm',_)] dfltE)
            | nameIsUnusedPat nm' ->
                do
                -- NOTE nm' is unused Name
                let sub  = C.listSubst (zip (map C.TVBound tyParams) tyArgs)
                    vts  = map
                             (\ty-> (nm',plainSubst sub ty))
                             (C.ecFields ctor)
                  -- N.B.: to avoid extra name construction, we are
                  --  using the same name (un-referenced!) nm' for
                  --  each of the arguments of the CaseAlt function.
                  --  This appears to work.  However, if the '_' name
                  --  *was* actually referenced, it would not be what
                  --  we would want However, typechecking would
                  --  ascertain this.

                return (C.CaseAlt vts dfltE)

            | otherwise ->
                panic "importCase" [
                    "Unsupported style of case expression: " <>
                        "default case alternative that binds scrutinee",
                    "pattern: " <> Text.pack (pretty nm)
                ]

          where
          nameIsUnusedPat nm'' =
            Text.take 3 (nameToLocalName nm'') == "__p"

            -- Except for the prefix, the indication that this is an unused pattern
            -- is long gone. This name is created using `getIdent` in
            --   deps/cryptol/src/Cryptol/Parser/Name.hs
            -- FIXME:
            --  - Clearly this is undesirable coupling.
            --  - Best (but non-local, pervasive) solution is to have a more
            --    precise type for default CaseAlt, the type is currently
            --    too general.

        Just (C.CaseAlt nts _) ->
            panic "importCase" [
                "Default CaseAlt breaks invariant: " <>
                    "(assumed) invariant is that exactly one variable pattern is allowed in the default CaseAlt",
                Text.pack (show $ PP.ppList $ map PP.pp (map fst nts))
            ]

  -- now create one alternative ('CaseAlt') for each ctor:
  alts <- forM ctors $ \ctor->
            case Map.lookup (C.nameIdent $ C.ecName ctor) altsMap of
              Just a  -> return a
              Nothing -> useDefaultAlt ctor

  {- |
  What we just did is, in terms of the running ETT example above, this:

  Given this Cryptol
    > case scrutinee  of
    >   C1     -> RHS1
    >   _      -> DFLT
  we transform it into this Cryptol
    > case scrutinee  of
    >   C1     -> RHS1
    >   C2 _   -> DFLT
    >   C3 _ _ -> DFLT

  And what we will do next is transform this last into this SAWCore:

    > ETT_case
    >   T1                          -- type application, the instantiation of 'a1'
    >   B                           -- type application, the result of the whole case
    >   RHS1                        -- deconstructor for C1
    >   (\(_: Nat)         -> DFLT) -- deconstructor for C2
    >   (\(_: Bool) (_:T1) -> DFLT) -- deconstructor for C3
    >                               --  - note the 'a1' has been instantiated to T1
    >   scrutinee
  -}

  -- translate each CaseAlt into a Cryptol function:
  let funcs = map (\(C.CaseAlt xs body)->
                      foldr (\(n,t) e-> C.EAbs n t e) body xs)
                  alts

  -- the Cryptol to SAWCore translations:
  tyArgs'    <- mapM (importType sc env) tyArgs
  b'         <- importType sc env b        -- b is type of whole case expr
  scrutinee' <- importExpr sc env scrutinee
  funcs'     <- mapM (importExpr sc env) funcs
  caseExpr   <- scGlobalApply sc (identOfEnumCase nm) $
                  tyArgs'             -- case is expecting the type arguments
                                      --   that the enumtype is instantiated to
                  ++ [b']             -- the result type of case expression
                  ++ funcs'           -- the eliminator funcs, one for each constructor
                  ++ [scrutinee']     -- scrutinee of case, of enum type

  return caseExpr


-- Shared naming conventions for Enum support:

identOfEnumType :: C.Name -> Ident
identOfEnumType nt = newIdent nt "__TY"

identOfEnumCase :: C.Name -> Ident
identOfEnumCase nt = newIdent nt "__case"

newIdent :: C.Name -> Text -> Ident
newIdent name suffix =
  mkIdent
    preludeName
       -- FIXME: These generated definitions should not be added to
       --        the prelude but to the module where the Enum (or ...)
       --        is defined.
    (C.identText (C.nameIdent name) `Text.append` suffix)

--------------------------------------------------------------------------------
-- Utility Functions:

mapAccumLM :: (Monad m) => (a -> x -> m (a, y)) -> a -> [x] -> m (a, [y])
mapAccumLM _ acc []     = return (acc, [])
mapAccumLM f acc (x:xs) = do
                          (acc', y) <- f acc x
                          (acc'', ys) <- mapAccumLM f acc' xs
                          return (acc'', y:ys)
  -- FIXME: When support ends for ghc-9.4.8, we can remove this
  -- definition and call Data.Traversable.mapAccumM instead.
