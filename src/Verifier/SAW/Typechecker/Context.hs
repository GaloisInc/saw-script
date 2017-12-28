{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}

{- |
Module      : Verifier.SAW.Typechecker.Context
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : jhendrix@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module Verifier.SAW.Typechecker.Context
  ( -- * Term definitions
    TCTerm(..)
  , FlatTermF(..)
  , tcMkApp
  , tcAsApp
  , tcAsStringLit
  , tcAsRecordValue
  , Prec, ppTCTerm
  , AnnPat(..)
  , TCPat
  , PatF(..)
  , tcPatVarCount
  , tcPatVarName
  , tcApply
  , tcPatApply
  , ppTCPat
  , patBoundVarsOf
  , patBoundVars
  , fmapTCPat
  , zipWithPatF
  , termFromPatF

  , TCDefGen(..)
  , TCRefDef

  , DefEqnGen(..)
  , TCDefEqn

  , DataTypeGen(..)
  , TCDataTypeGen
  , TCRefDataType
  , TCCtorType
  , TCRefCtor

  , FixedPiType(..)
  , TCDTType
  , termFromTCDTType
  , termFromTCCtorType

    -- * Global context
  , GlobalContext
  , emptyGlobalContext
  , Loc(..)
  , insertDataType
  , insertDef
  , resolveCtor
    -- * Term context
  , TermContext
  , globalContext
  , emptyTermContext
  , consBoundVar
  , InferResult(..)
  , resolveIdent
  , BoundInfo(..)
  , resolveBoundInfo
  , globalDefEqns
  , contextNames
  , ppTermContext
  , boundVarDiff
  , applyExt
  , applyExtSafe
  , boundFreeVarsWithPi
  , termBoundCount
    -- * Checking terms
  , checkTCPatOf
  , checkDefEqn
  , checkTCTerm
  ) where

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative
import Data.Foldable (Foldable)
#endif

import Control.Lens
import Control.Monad.Identity
import Control.Monad.State
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import qualified Data.Set as Set
import Data.Vector (Vector)
import qualified Data.Vector as V
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))
import qualified Text.PrettyPrint.ANSI.Leijen as PPL

import Verifier.SAW.TypedAST
import Verifier.SAW.Position
import qualified Verifier.SAW.UntypedAST as Un
import Verifier.SAW.Typechecker.Monad

data DefEqnGen p t
   = DefEqnGen [p] t -- ^ List of patterns and a right hand side
  deriving (Show)

type TCDefEqn = DefEqnGen TCPat TCTerm

data TCTerm
  = TCF !(FlatTermF TCTerm)
  | TCApp !TCTerm !TCTerm
  | TCLambda !TCPat !TCTerm !TCTerm
  | TCPi !TCPat !TCTerm !TCTerm
    -- | A local variable with its deBruijn index and type in the current context.
  | TCVar DeBruijnIndex

data AnnPat a
    -- | Variable with its annotation.
    -- Index contains order in which this variable is bound.
  = TCPVar String (DeBruijnIndex,a)
    -- | Unused variable and its type.
    -- Index contains number of variables in this pattern bound in the context of the type.
  | TCPUnused String (DeBruijnIndex,a)
  | TCPatF (PatF (AnnPat a))

type TCPat = AnnPat TCTerm

-- | Pattern functor
data PatF p
   = UPUnit
   | UPPair p p
   | UPEmpty
   | UPField p p p
   | UPCtor Ident [p]
   | UPString String
  deriving (Functor, Foldable, Traversable, Show)

tcMkApp :: TCTerm -> [TCTerm] -> TCTerm
tcMkApp = go
  where go t [] = t
        go t (a:l) = go (TCApp t a) l

tcAsApp :: TCTerm -> (TCTerm, [TCTerm])
tcAsApp = go []
  where go r (TCApp f v) = go (v:r) f
        go r f = (f,r)

tcAsStringLit :: TCTerm -> Maybe String
tcAsStringLit t =
  case t of
    TCF (StringLit s) -> Just s
    _ -> Nothing

tcAsRecordValue :: TCTerm -> Maybe (Map FieldName TCTerm)
tcAsRecordValue t =
  case t of
    TCF EmptyValue -> return Map.empty
    TCF (FieldValue (TCF (StringLit f)) v r) -> Map.insert f v <$> tcAsRecordValue r
    _ -> Nothing

asUPTuple :: AnnPat a -> Maybe [AnnPat a]
asUPTuple (TCPatF UPUnit)       = return []
asUPTuple (TCPatF (UPPair x y)) = (x :) <$> asUPTuple y
asUPTuple _                     = Nothing

-- | A pi type that accepted a statically-determined number of arguments.
data FixedPiType r
  = FPResult r
  | FPPi TCPat TCTerm (FixedPiType r)

fixedPiArgCount :: FixedPiType r -> Int
fixedPiArgCount = go 0
  where go i FPResult{} = i
        go i (FPPi _ _ r) = go (i+1) r

type TCDTType = FixedPiType Sort
type TCCtorType = FixedPiType [TCTerm]

data DataTypeGen t c =
   DataTypeGen { dtgName :: Ident
               , dtgType :: t
               , dtgCtors :: [c]
               }

type TCDataTypeGen r = DataTypeGen (r TCDTType) (Ctor (r TCCtorType))
type TCCtorGen r = Ctor (r TCCtorType)

data TCDefGen r
  = DefGen !Ident Un.DeclQualifier !(r TCTerm) !(r [TCDefEqn])

defGenIdent :: TCDefGen r -> Ident
defGenIdent (DefGen i _ _ _) = i

type TCRefDataType s = TCDataTypeGen (TCRef s)
type TCRefCtor s = TCCtorGen (TCRef s)
type TCRefDef s = TCDefGen (TCRef s)

-- | State monad for recording variables found in patterns.
type PatVarParser a = State (Int,Map Int (String,a))

-- | Add variables in pattern to state.
addPatBindings :: AnnPat a -> PatVarParser a ()
addPatBindings (TCPVar nm (i, v)) = modify $ \(c,m) -> (max c (i+1), Map.insert i (nm,v) m)
addPatBindings TCPUnused{} = return ()
addPatBindings (TCPatF pf) = traverseOf_ folded addPatBindings pf

-- | Get list of variables by running parser.
runPatVarParser :: PatVarParser a () -> Vector (String,a)
runPatVarParser pvp
   | c == Map.size m = V.generate c fn
   | otherwise = error "patBoundVarsOf given incomplete list of patterns"
  where (c,m) = execState pvp (0,Map.empty)
        fn i = r
          where Just r = Map.lookup i m

-- | Get information about bound variables from fold.
patBoundVarsOf :: Fold s (AnnPat a) -> s -> Vector (String,a)
patBoundVarsOf fold pats =
  runPatVarParser (traverseOf_ fold addPatBindings pats)

-- | Returns variables in order they are bound.
patBoundVars :: AnnPat a -> Vector (String,a)
patBoundVars pat = patBoundVarsOf id pat

-- | Returns names of bound variables in order they are bound.
patVarNames :: AnnPat a -> Vector String
patVarNames pat = fst <$> patBoundVars pat

fmapTCPat :: (Int -> TCTerm -> TCTerm)
          -> Int -> TCPat -> TCPat
fmapTCPat fn i (TCPVar nm (j,tp)) = TCPVar nm (j, fn (i+j) tp)
fmapTCPat fn i (TCPUnused nm (j,tp)) = TCPUnused nm (j, fn (i+j) tp)
fmapTCPat fn i (TCPatF pf) = TCPatF (fmapTCPat fn i <$> pf)

-- | Convert pats into equivalent termf.
termFromPatF :: PatF a -> FlatTermF a
termFromPatF UPUnit          = UnitValue
termFromPatF (UPPair x y)    = PairValue x y
termFromPatF UPEmpty         = EmptyValue
termFromPatF (UPField f x y) = FieldValue f x y
termFromPatF (UPCtor c l)    = CtorApp c l
termFromPatF (UPString s)    = StringLit s

-- | Attempt to zip two patfs together.
zipWithPatF :: (a -> b -> c) -> PatF a -> PatF b -> Maybe (PatF c)
zipWithPatF f x y =
  case (x,y) of
    (UPUnit, UPUnit) -> Just UPUnit
    (UPPair x1 x2, UPPair y1 y2) -> Just $ UPPair (f x1 y1) (f x2 y2)
    (UPEmpty, UPEmpty) ->
          Just $ UPEmpty
    (UPField x1 x2 x3, UPField y1 y2 y3) ->
          Just $ UPField (f x1 y1) (f x2 y2) (f x3 y3)
    (UPCtor cx lx, UPCtor cy ly)
      | (cx,length lx) == (cy, length ly) ->
          Just $ UPCtor cx (zipWith f lx ly)
    _ -> Nothing

termFromTCDTType :: TCDTType -> TCTerm
termFromTCDTType (FPResult s) = TCF (Sort s)
termFromTCDTType (FPPi p tp r) = TCPi p tp (termFromTCDTType r)

termFromTCCtorType :: Ident -> TCCtorType -> TCTerm
termFromTCCtorType dt (FPResult tl) = TCF (DataTypeApp dt tl)
termFromTCCtorType dt (FPPi p tp r) = TCPi p tp (termFromTCCtorType dt r)

-- | Returns number of bound variables in pat.
tcPatVarCount :: TCPat -> Int
tcPatVarCount TCPVar{} = 1
tcPatVarCount TCPUnused{} = 0
tcPatVarCount (TCPatF pf) = sumOf folded (tcPatVarCount <$> pf)

-- | Return the 'String' name of the sole variable bound by a pattern (even if
-- it is unused), for patterns that are just a single variable
tcPatVarName :: TCPat -> Maybe String
tcPatVarName (TCPVar nm _) = Just nm
tcPatVarName (TCPUnused nm _) = Just nm
tcPatVarName _ = Nothing

-- | Increment free vars in TC term by given amount if the index is at least the given level.
-- This is used for inserting extra variables to a context.
-- The context should be for the new context.
incTCVars :: Int -> Int -> TCTerm -> TCTerm
incTCVars j = go
  where pfn = fmapTCPat go
        go i (TCF tf) = TCF (go i <$> tf)
        go i (TCApp x y) = TCApp (go i x) (go i y)
        go i (TCLambda p tp r) = TCLambda (pfn i p) (go i tp) r'
          where r' = go (i+tcPatVarCount p) r
        go i (TCPi p tp r) = TCPi (pfn i p) (go i tp) r'
          where r' = go (i+tcPatVarCount p) r
        go i (TCVar l) = TCVar $ if l >= i then l+j else l


-- | @tcApply t n args@ substitutes free variables [n..length args-1] with args.
-- The args are assumed to be in the same context as @t@ after substitution.
tcApply :: TermContext s -> (TermContext s,TCTerm) -> (TermContext s,Vector TCTerm) -> TCTerm
tcApply baseTC (fTC, f) (vTC, v)
   | V.length v <= fd = tcApplyImpl vd v (fd - V.length v) f
   | otherwise = error $ show $
      text "tcApply given bad arguments:" <$$>
      ppTCTerm fTC PrecNone f <$$>
      text ("fd = " ++ show fd) <$$>
      vcat (ppTCTerm vTC PrecNone <$> V.toList v)
  where Just fd = boundVarDiff fTC baseTC
        Just vd = boundVarDiff vTC baseTC

tcPatApply :: TermContext s
           -> (TermContext s, TCPat)
           -> (TermContext s, Vector TCTerm)
           -> TCPat
tcPatApply baseTC (fTC, p) (vTC, v)
   | V.length v <= fd = fmapTCPat (tcApplyImpl vd v) (fd - V.length v) p
   | otherwise = error "tcPatApply given bad vector"
  where Just fd = boundVarDiff fTC baseTC
        Just vd = boundVarDiff vTC baseTC

tcApplyImpl :: Int -> Vector TCTerm -> Int -> TCTerm -> TCTerm
tcApplyImpl vd v = go
  where fd = V.length v
        go i (TCF tf) = TCF (go i <$> tf)
        go i (TCApp x y) = TCApp (go i x) (go i y)
        go i (TCLambda p tp r) = TCLambda (fmapTCPat go i p) (go i tp) r'
          where r' = go (i + tcPatVarCount p) r
        go i (TCPi p tp r) = TCPi (fmapTCPat go i p) (go i tp) r'
          where r' = go (i + tcPatVarCount p) r
        go i (TCVar j) | j < i = TCVar j -- Variable bound
                       | j - i < fd = incTCVars i 0 (v V.! (j - i)) -- Variable instantiated.
                       | otherwise = TCVar (vd + j - fd) -- Variable in new extended context.

-- | Extend a term with the context from the given pair to the extended context.
applyExt :: TermContext s -> (TermContext s,TCTerm) -> TCTerm
applyExt tc1 (tc0,t) = incTCVars d 0 t
  where Just d = boundVarDiff tc1 tc0

-- | Extend a term with the context from the given pair to the extended context.
applyExtSafe :: TermContext s -> (TermContext s,TCTerm) -> Maybe TCTerm
applyExtSafe tc1 (tc0,t) = (\d -> incTCVars d 0 t) <$> boundVarDiff tc1 tc0

-- Global context stuff

-- | Location contains
data Loc
  = ImportedLoc ModuleName Pos
  | LocalLoc Pos

data GlobalBinding r
  = DataTypeBinding Loc (TCDataTypeGen r)
    -- Datatype ident, ctor ident, ctor type.
  | CtorBinding Loc (TCDataTypeGen r) (TCCtorGen r)
  | DefBinding Loc (TCDefGen r)

-- | Returns location and identified of global binding.
globalBindingDesc :: GlobalBinding r -> (Loc,Ident)
globalBindingDesc gb =
  case gb of
    DataTypeBinding l dt -> (l, dtgName dt)
    CtorBinding l _ c -> (l, ctorName c)
    DefBinding l def -> (l, defGenIdent def)

type GlobalContextMap s = Map Un.Ident [GlobalBinding (TCRef s)]

data GlobalContext s = GC { gcMap :: !(GlobalContextMap s)
                          , gcEqns :: !(Map Ident (TCRef s [TCDefEqn]))
                          }

emptyGlobalContext :: GlobalContext s
emptyGlobalContext = GC { gcMap = Map.empty
                        , gcEqns = Map.empty
                        }

type UntypedBinding s = (Un.Ident, GlobalBinding (TCRef s))

insertAllBindings :: [UntypedBinding s] -> GlobalContextMap s -> GlobalContextMap s
insertAllBindings = flip (foldr ins)
  where ins (i,v) = Map.insertWith (++) i [v]


-- | Add untyped global with the given module names.
untypedBindings :: Bool
                -> [Maybe ModuleName]
                -> String
                -> GlobalBinding (TCRef s)
                -> [UntypedBinding s]
untypedBindings vis mnml nm gb
  | vis = [ (Un.mkIdent mnm nm, gb) | mnm <- mnml ]
  | otherwise = []

-- | Insert data type into global context.
insertDataType :: [Maybe ModuleName] -- ^ List of namespaces for symbols.
               -> Bool -- ^ Indicates if data type should be visible to users.
               -> Loc -- ^ Location where datatype comes from.
               -> DataTypeGen (TCRef s TCDTType) (Bool, Loc, TCRefCtor s)
               -> GlobalContext s
               -> GlobalContext s
insertDataType mnml vis loc (DataTypeGen dtnm dtp cl) gc =
    gc { gcMap = insertAllBindings bindings (gcMap gc) }
  where dt = DataTypeGen dtnm dtp (view _3 <$> cl)
        dtBindings = untypedBindings vis mnml (identName dtnm) (DataTypeBinding loc dt)
        cBindings (b, cloc, c@(Ctor cnm _)) =
          untypedBindings b mnml (identName cnm) (CtorBinding cloc dt c)
        bindings = dtBindings ++ concatMap cBindings cl

insertDef :: [Maybe ModuleName]
          -> Bool -- ^ Indicates ifd definition should be visible to users.
          -> Loc -- ^ Location where symbol comes form.
          -> TCRefDef s
          -> GlobalContext s
          -> GlobalContext s
insertDef mnml vis loc d@(DefGen nm _ _ eqs) gc =
    gc { gcMap  = insertAllBindings bindings (gcMap gc)
       , gcEqns = Map.insert nm eqs (gcEqns gc)
       }
  where bindings = untypedBindings vis mnml (identName nm) (DefBinding loc d)

showQuoted :: Show s => s -> Doc
showQuoted nm = squotes (text (show nm))

-- | Lookup ctor returning identifier and type.
resolveGlobalIdent :: GlobalContext s -> PosPair Un.Ident -> TC s (GlobalBinding (TCRef s))
resolveGlobalIdent gc (PosPair p nm) =
  case fromMaybe [] $ Map.lookup nm (gcMap gc) of
    [] -> tcFail p $ show $ text "Unknown identifier:" <+> showQuoted nm <> text "."
    [d] -> return d
    (d:r) -> tcFail p $ show $
      text "Ambiguous occurance" <+> showQuoted nm <> text "." <$$>
      ppLoc firstText (globalBindingDesc d) <$$>
      vcat (ppLoc otherText . globalBindingDesc <$> r)
 where firstText = "It could refer to either"
       otherText = "                      or"
       imporText = "                         imported from"
       ppLoc t (ImportedLoc mnm oldp, sym) =
         text t <+> showQuoted sym <> comma <$$>
         text imporText <+> showQuoted mnm <+> text ("at " ++ show oldp)
       ppLoc t (LocalLoc pm, sym) =
         text t <+> showQuoted sym <> text (", defined at " ++ show pm)

-- | Lookup ctor returning identifier and type.
resolveCtor :: GlobalContext s -> PosPair Un.Ident -> Int -> TC s (Ident, TCTerm)
resolveCtor gc (PosPair p nm) argc = do
  gb <- resolveGlobalIdent gc (PosPair p nm)
  case gb of
    CtorBinding _ dt (Ctor c rtp) -> do
      tp <- eval p rtp
      if fixedPiArgCount tp == argc then
        return $ (c, termFromTCCtorType (dtgName dt) tp)
      else
        tcFail p "Incorrect number of arguments given to constructor."
    DataTypeBinding{} -> tcFail p $ "Pattern matching data type is unsupported."
    DefBinding{} -> tcFail p $ "Not a data constructor: " ++ show nm

-- TermContext

data TermContext s where
  TopContext :: GlobalContext s -> TermContext s
  BindContext :: TermContext s -> String -> TCTerm -> TermContext s

boundVarDiff :: TermContext s -> TermContext s -> Maybe Int
boundVarDiff tc1 tc0
    | d >= 0 = Just d
    | otherwise = Nothing
  where d = termBoundCount tc1 - termBoundCount tc0

termBoundCount :: TermContext s -> Int
termBoundCount TopContext{} = 0
termBoundCount (BindContext tc _ _) = termBoundCount tc + 1

-- | Empty term context.
emptyTermContext :: GlobalContext s -> TermContext s
emptyTermContext = TopContext

-- | Add bound var to the context.
consBoundVar :: String -> TCTerm -> TermContext s -> TermContext s
consBoundVar nm tp ctx = BindContext ctx nm tp

globalContext :: TermContext s -> GlobalContext s
globalContext (BindContext tc _ _) = globalContext tc
globalContext (TopContext gc) = gc

data BoundInfo where
  BoundVar :: String -> BoundInfo

resolveBoundInfo :: DeBruijnIndex -> TermContext s -> BoundInfo
resolveBoundInfo 0 (BindContext _ nm _) = BoundVar nm
resolveBoundInfo i (BindContext tc _ _) = resolveBoundInfo (i-1) tc
resolveBoundInfo _ TopContext{} = error "resolveBoundInfo given invalid index."

globalDefEqns :: Ident -> TermContext s -> TCRef s [TCDefEqn]
globalDefEqns i tc = fromMaybe emsg $ Map.lookup i (gcEqns (globalContext tc))
  where emsg = error $ "Could not find equations for " ++ show i ++ "."

-- Haddock will not parse comments on GADT constructors :-(
data InferResult where
  --  Ctor with identifier argument list and
  PartialCtor :: Ident -- Datatype identifier
              -> Ident -- Ctor identifier.
              -> [TCTerm] -- Arguments so far.
              -> TCPat  -- Pattern for next argument
              -> TCTerm -- Type of next argument.
              -> TCCtorType -- Result ctor type.
              -> InferResult
  PartialDataType :: Ident
                  -> [TCTerm]
                  -> TCPat
                  -> TCTerm
                  -> TCDTType
                  -> InferResult
  TypedValue :: TCTerm -> TCTerm -> InferResult

matchName :: String -> Un.Ident -> Bool
matchName nm (Un.asLocalIdent -> Just nm') = nm == nm'
matchName _ _ = False

-- | Infer result of variable or ctor reference.
resolveIdent :: forall s . TermContext s
             -> PosPair Un.Ident -> TC s InferResult
resolveIdent tc0 (PosPair p ident) = go tc0
  where go tc1@(BindContext tc nm tp)
            | matchName nm ident =
                pure $ TypedValue (applyExt tc0 (tc1,TCVar 0))
                                  (applyExt tc0 (tc,tp))
            | otherwise = go tc
        go (TopContext gc) = do
          gb <- resolveGlobalIdent gc (PosPair p ident)
          case gb of
            DataTypeBinding _ (DataTypeGen dt rtp _) -> do
              ftp <- eval p rtp
              case ftp of
                FPResult s -> pure $ TypedValue (TCF (DataTypeApp dt [])) (TCF (Sort s))
                FPPi pat tp next -> pure $ PartialDataType dt [] pat tp next
            CtorBinding _ dt (Ctor c rtp) -> do
              ftp <- eval p rtp
              case ftp of
                FPResult args ->
                 pure $ TypedValue (TCF (CtorApp c []))
                                   (TCF (DataTypeApp (dtgName dt) args))
                FPPi pat tp next -> pure $ PartialCtor (dtgName dt) c [] pat tp next
            DefBinding _ (DefGen gi _ rtp _) ->
              TypedValue (TCF (GlobalDef gi)) <$> eval p rtp

-- | Return names in context.
contextNames :: TermContext s -> [String]
contextNames (BindContext tc nm _) = nm : contextNames tc
contextNames TopContext{} = []

-- Pretty printing

-- | Pretty print a term context.
ppTermContext :: TermContext s -> Doc
ppTermContext (BindContext tc nm tp) =
  text ("bind " ++ nm) <+> text "::" <+> ppTCTerm tc PrecLambda tp <$$>
  ppTermContext tc
ppTermContext TopContext{} = text "top"

-- | Pretty print a pat
ppTCPat :: AnnPat a -> Doc
ppTCPat (TCPVar nm _) = text nm
ppTCPat (TCPUnused nm _) = text nm
ppTCPat (TCPatF pf) =
  case asUPTuple (TCPatF pf) of
    Just pl -> parens $ commaSepList (ppTCPat <$> pl)
    Nothing ->
    -- FIXME: case asUPRecord (TCPatF pf) of
      case pf of
        UPUnit        -> text "()"
        UPPair x y    -> parens (ppTCPat x <+> text "#" <+> ppTCPat y)
        UPEmpty       -> text "{}"
        UPField f x y -> braces (ppFld (ppTCPat f) (ppTCPat x) <+> char '|' <+> (ppTCPat y))
          where ppFld s z = group $ nest 2 (s <+> equals PPL.<$> z)
        UPCtor c l    -> hsep (ppIdent c : fmap ppTCPat l)
        UPString s    -> text (show s)

ppTCTerm :: TermContext s -> Prec -> TCTerm -> Doc
ppTCTerm tc = ppTCTermGen (text <$> contextNames tc)

-- | Pretty print TC term with doc used for free variables.
ppTCTermGen :: [Doc] -> Prec -> TCTerm -> Doc
ppTCTermGen d pr (TCF tf) =
  runIdentity $ ppFlatTermF defaultPPOpts (\pr' t -> return (ppTCTermGen d pr' t)) pr tf
ppTCTermGen d pr (TCApp x y) = ppAppParens pr $
  ppTCTermGen d PrecApp x <+> ppTCTermGen d PrecArg y
ppTCTermGen d pr (TCLambda p l r) = ppParens (pr > PrecNone) $
  char '\\' <> parens (ppTCPat p <+> colon <+> ppTCTermGen d PrecLambda l)
            <+> text "->"
            <+> ppTCTermGen (d ++ fmap text (V.toList $ patVarNames p)) PrecLambda r
ppTCTermGen d pr (TCPi p l r) = ppParens (pr > PrecNone) $
  parens (ppTCPat p <+> colon <+> ppTCTermGen d PrecLambda l)
    <+> text "->" <+> ppTCTermGen (d ++ fmap text (V.toList $ patVarNames p)) PrecLambda r
ppTCTermGen d _ (TCVar i) | 0 <= i && i < length d = d !! i
                          | otherwise = text $ "Bad variable index " ++ show i

-- | Bound the free variables in the term with pi quantifiers.
boundFreeVarsWithPi :: (TermContext s, TCTerm) -> TermContext s -> TCTerm
boundFreeVarsWithPi (tc1,t0) tc0 = go d0 tc1 t0
  where Just d0 = boundVarDiff tc1 tc0
        go 0 _ t = t
        go d (BindContext tc nm tp) t = go (d-1) tc (TCPi (TCPVar nm (0,tp)) tp t)
        go _ _ _ = error "boundFreeVarsWithPi given bad context"

-- | Check TCPat free variables returning new number of bound variables.
checkTCPatOf :: Int -> Simple Traversal s TCPat -> s -> Maybe Int
checkTCPatOf c t s0 = finalCheck =<< execStateT (traverseOf_ t go s0) (Set.empty,Set.empty)
  where finalCheck (s,u) = do
          let sz = Set.size s
          -- Check s contains all variables in range (0..sz-1)
          let cnt = maybe 0 ((+1) . fst) (Set.maxView s)
          unless (cnt == sz) $ error $ "Set missing variables: " ++ show s
          -- Check all elements in u are at most sz.
          unless (allOf folded (<= sz) u) $ error "Invalid index in unused variable."
          return (c+sz)
        go (TCPVar _ (i,tp)) = do
          lift $ checkTCTerm (c+i) tp
          s <- use _1
          when (Set.member i s) $ error "Already encountered variable"
          _1 .= Set.insert i s
        go (TCPUnused _ (i,tp)) = do
          lift $ checkTCTerm (c+i) tp
          _2 %= Set.insert i
        go (TCPatF pf) = traverseOf_ folded go pf

checkDefEqn :: Int -> TCDefEqn -> Maybe ()
checkDefEqn c (DefEqnGen pl r) = do
  c' <- checkTCPatOf c traverse pl
  checkTCTerm c' r

-- | Check that term does not reference free variables out of given range.
checkTCTerm :: Int -> TCTerm -> Maybe ()
checkTCTerm c t0 =
  case t0 of
    TCF tf -> traverseOf_ folded (checkTCTerm c) tf
    TCApp x y -> do
      checkTCTerm c x
      checkTCTerm c y
    TCLambda p tp r -> do
      checkTCTerm c tp
      c' <- checkTCPatOf c id p
      checkTCTerm c' r
    TCPi p tp r -> do
      checkTCTerm c tp
      c' <- checkTCPatOf c id p
      checkTCTerm c' r
    TCVar i -> unless (i < c) $ error "Illegal var index"
