{-# LANGUAGE DeriveFoldable #-} 
{-# LANGUAGE DeriveFunctor #-} 
{-# LANGUAGE DeriveTraversable #-} 
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}
module Verifier.SAW.Typechecker.Context
  ( -- * Term definitions
    TCTerm(..)
  , FlatTermF(..)
  , tcMkApp
  , tcAsApp
  , Prec, ppTCTerm
  , TCPat(..)
  , PatF(..)
  , tcPatVarCount
  , fmapTCPat
  , tcApply
  , tcPatApply

  , LocalDefGen(..)
  , TCRefLocalDef
  , TCLocalDef
  , fmapTCLocalDefs
  , localVarNamesCount

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
  , gcTypes
  , gcDefs
  , insertDataType
  , insertDef
  , resolveCtor
    -- * Term context
  , TermContext
  , globalContext
  , emptyTermContext
  , consBoundVar
  , consLocalDefs
  , InferResult(..)
  , resolveIdent
  , BoundInfo(..)
  , resolveBoundInfo
  , globalDefEqns
  , contextNames
  , ppTermContext
  , boundVarDiff
  , applyExt
  , boundFreeVarsWithPi
  ) where

import Control.Applicative
import Control.Monad.Identity
import Data.Foldable
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Traversable
import Data.Vector (Vector)
import qualified Data.Vector as V
import Text.PrettyPrint

import Prelude hiding (concatMap, foldr, sum)

import Verifier.SAW.TypedAST
import Verifier.SAW.Position
import qualified Verifier.SAW.UntypedAST as Un
import Verifier.SAW.Typechecker.Monad

maybeApply :: Bool -> (a -> a) -> a -> a
maybeApply True f a = f a
maybeApply False _ a = a


data DefEqnGen p t
   = DefEqnGen [p]  -- ^ List of patterns
                t -- ^ Right hand side.
  deriving (Show)

type TCDefEqn = DefEqnGen TCPat TCTerm

-- | Local definition in its most generic form.
-- n is the identifier for name, p is the pattern, and t is the type.
-- The
-- The equations are typed in the context after all local variables are
data LocalDefGen t e
   = -- | A Local function definition with position, name, type, and equations.
     -- Type is typed in context before let bindings.
     -- Equations are typed in context after let bindings.
     LocalFnDefGen String t e
  deriving (Show)

localVarNamesGen :: [LocalDefGen t e] -> [String]
localVarNamesGen = fmap go
  where go (LocalFnDefGen nm _ _) = nm

localVarNamesCount :: [LocalDefGen t e] -> Int
localVarNamesCount = length

type TCLocalDef = LocalDefGen TCTerm [TCDefEqn]

data TCTerm
  = TCF !(FlatTermF TCTerm)
  | TCLambda !TCPat !TCTerm !TCTerm
  | TCPi !TCPat !TCTerm !TCTerm
  | TCLet [TCLocalDef] TCTerm
    -- | A local variable with its deBruijn index and type in the current context.
  | TCVar DeBruijnIndex
    -- | A reference to a let bound function with equations.
  | TCLocalDef DeBruijnIndex 

data TCPat = TCPVar String DeBruijnIndex TCTerm
           | TCPUnused String -- ^ Unused pattern
           | TCPatF (PatF TCPat)

data PatF p
   = UPTuple [p]
   | UPRecord (Map FieldName p)
   | UPCtor Ident [p]
  deriving (Functor, Foldable, Traversable, Show)

tcMkApp :: TCTerm -> [TCTerm] -> TCTerm
tcMkApp = go
  where go t [] = t
        go t (a:l) = go (TCF (App t a)) l

tcAsApp :: TCTerm -> (TCTerm, [TCTerm])
tcAsApp = go []
  where go r (TCF (App f v)) = go (v:r) f
        go r f = (f,r) 

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

data DataTypeGen t c = DataTypeGen { dtgName :: Ident
                                   , dtgType :: t
                                   , dtgCtors :: [c]
                                   }

type TCDataTypeGen r = DataTypeGen (r TCDTType) (Ctor Ident (r TCCtorType))
type TCCtorGen r = Ctor Ident (r TCCtorType)

data TCDefGen r = DefGen !Ident !(r TCTerm) !(r [TCDefEqn])

type TCRefDataType s = TCDataTypeGen (TCRef s)
type TCRefCtor s = TCCtorGen (TCRef s)
type TCRefDef s = TCDefGen (TCRef s)
type TCRefLocalDef s = LocalDefGen TCTerm (TCRef s [TCDefEqn])

patVarNames :: TCPat -> [String]
patVarNames (TCPVar nm _ _) = [nm]
patVarNames TCPUnused{} = []
patVarNames (TCPatF pf) = concatMap patVarNames pf

fmapTCPat :: (Int -> TCTerm -> TCTerm)
          -> Int -> TCPat -> TCPat
fmapTCPat fn i (TCPVar nm j tp) = TCPVar nm j (fn (i+j) tp)
fmapTCPat _ _ (TCPUnused nm) = TCPUnused nm
fmapTCPat fn i (TCPatF pf) = TCPatF (fmapTCPat fn i <$> pf)  

fmapTCLocalDefs :: (Int -> TCTerm -> TCTerm)
                -> Int -> [TCLocalDef] -> [TCLocalDef]
fmapTCLocalDefs tfn i defs = go <$> defs
  where i' = i + length defs
        go (LocalFnDefGen nm tp eqs) = LocalFnDefGen nm (tfn i tp) eqs'
          where eqs' = fmapTCDefEqn tfn i' <$> eqs

fmapTCDefEqn :: (Int -> TCTerm -> TCTerm)
             -> Int -> TCDefEqn -> TCDefEqn
fmapTCDefEqn tfn l (DefEqnGen pl r) = DefEqnGen pl' r'
  where pl' = fmapTCPat tfn l <$> pl
        r' = tfn (l+ sum (tcPatVarCount <$> pl)) r

termFromTCDTType :: TCDTType -> TCTerm
termFromTCDTType (FPResult s) = TCF (Sort s)
termFromTCDTType (FPPi p tp r) = TCPi p tp (termFromTCDTType r)

termFromTCCtorType :: Ident -> TCCtorType -> TCTerm
termFromTCCtorType dt (FPResult tl) = TCF (DataTypeApp dt tl)
termFromTCCtorType dt (FPPi p tp r) = TCPi p tp (termFromTCCtorType dt r)

tcPatVarCount :: TCPat -> Int
tcPatVarCount TCPVar{} = 1 
tcPatVarCount TCPUnused{} = 0
tcPatVarCount (TCPatF pf) = sum (tcPatVarCount <$> pf)


-- | Increment free vars in TC term by given amount if the index is at least the given level.
-- This is used for inserting extra variables to a context.
-- The context should be for the new context.
incTCVars :: Int -> Int -> TCTerm -> TCTerm
incTCVars j = go
  where pfn = fmapTCPat go
        go i (TCF tf) = TCF (go i <$> tf)
        go i (TCLambda p tp r) = TCLambda (pfn i p) (go i tp) r'
          where r' = go (i+tcPatVarCount p) r
        go i (TCPi p tp r) = TCPi (pfn i p) (go i tp) r'
          where r' = go (i+tcPatVarCount p) r
        go i (TCLet lcls t) = TCLet (fmapTCLocalDefs go i lcls) t'
          where t' = go (i+localVarNamesCount lcls) t
        go i (TCVar l) = TCVar $ if l >= i then l+j else l
        go i (TCLocalDef l) = TCLocalDef $ if l >= i then l+j else l


-- | @tcApply t n args@ substitutes free variables [n..length args-1] with args.
-- The args are assumed to be in the same context as @t@ after substitution.
tcApply :: TermContext s -> (TermContext s,TCTerm) -> (TermContext s,Vector TCTerm) -> TCTerm
tcApply baseTC (fTC, f) (vTC, v)
   | V.length v <= fd = tcApplyImpl vd v (fd - V.length v) f
   | otherwise = error $ show $ text "tcApply given bad arguments:" $$
      ppTCTerm fTC 0 f $$
      text ("fd = " ++ show fd) $$
      vcat (ppTCTerm vTC 0 <$> V.toList v) 
  where fd = boundVarDiff fTC baseTC
        vd = boundVarDiff vTC baseTC

tcPatApply :: TermContext s
           -> (TermContext s, TCPat)
           -> (TermContext s, Vector TCTerm)
           -> TCPat
tcPatApply baseTC (fTC, p) (vTC, v)
   | V.length v <= fd = fmapTCPat (tcApplyImpl vd v) (fd - V.length v) p
   | otherwise = error "tcPatApply given bad vector"
  where fd = boundVarDiff fTC baseTC
        vd = boundVarDiff vTC baseTC

tcApplyImpl :: Int -> Vector TCTerm -> Int -> TCTerm -> TCTerm
tcApplyImpl vd v = go
  where fd = V.length v
        go i (TCF tf) = TCF (go i <$> tf)
        go i (TCLambda p tp r) = TCLambda (fmapTCPat go i p) (go i tp) r'
          where r' = go (i + tcPatVarCount p) r
        go i (TCPi p tp r) = TCPi (fmapTCPat go i p) (go i tp) r'
          where r' = go (i + tcPatVarCount p) r
        go i (TCLet lcls r) = TCLet (fmapTCLocalDefs go i lcls) r'
          where r' = go (i + length lcls) r
        go i (TCVar j) | j < i = TCVar j -- Variable bound
                       | j - i < fd = incTCVars i 0 (v V.! (j - i)) -- Variable instantiated.
                       | otherwise = TCVar (vd + j - fd) -- Variable in new extended context.
        go i (TCLocalDef j)
          | j < i = TCLocalDef j
          | j - i < fd = error "Attempt to instantiate let bound definition."
          | otherwise = TCLocalDef (vd + j - fd)

-- | Extend a term with the context from the given pair to the extended context.
applyExt :: (TermContext s,TCTerm) -> TermContext s -> TCTerm
applyExt (tc0,t) tc1 = incTCVars (boundVarDiff tc1 tc0) 0 t

-- Global context stuff

data GlobalBinding r
  = DataTypeBinding (TCDataTypeGen r)
    -- Datatype ident, ctor ident, ctor type.
  | CtorBinding (TCDataTypeGen r) (TCCtorGen r)
  | DefBinding (TCDefGen r)

type GlobalContextMap s = Map Un.Ident (GlobalBinding (TCRef s))

data GlobalContext s = GC { gcMap :: !(GlobalContextMap s)
                          , gcEqns :: !(Map Ident (TCRef s [TCDefEqn]))
                          , gcTypes :: ![ TCRefDataType s ]
                          , gcDefs :: ![ TCRefDef s ]
                          } 

emptyGlobalContext :: GlobalContext s
emptyGlobalContext = GC { gcMap = Map.empty
                        , gcEqns = Map.empty
                        , gcTypes = []
                        , gcDefs = []
                        }

-- | Add untyped global with the given module names.
insGlobalBinding :: Bool
                 -> [Maybe ModuleName]
                 -> String
                 -> GlobalBinding (TCRef s)
                 -> GlobalContextMap s
                 -> GlobalContextMap s
insGlobalBinding vis mnml nm gb = maybeApply vis $ flip (foldr ins) mnml
  where ins mnm = Map.insert (Un.mkIdent mnm nm) gb  

insertDataType :: [Maybe ModuleName]
               -> Bool -- Visible in untyped context.
               -> DataTypeGen (TCRef s TCDTType) (Bool, TCRefCtor s)
               -> GlobalContext s
               -> GlobalContext s
insertDataType mnml vis (DataTypeGen dtnm dtp cl) gc = 
    gc { gcMap = flip (foldr insCtor) cl $ insDT $ gcMap gc
       , gcTypes = dt:gcTypes gc
       } 
  where dt = DataTypeGen dtnm dtp (snd <$> cl)
        insDT = insGlobalBinding vis mnml (identName dtnm) (DataTypeBinding dt)
        insCtor (b, c@(Ctor cnm _)) =
          insGlobalBinding b mnml (identName cnm) (CtorBinding dt c)

insertDef :: [Maybe ModuleName]
          -> Bool -- Visibile in untyped context.
          -> TCRefDef s
          -> GlobalContext s
          -> GlobalContext s
insertDef mnml vis d@(DefGen nm _ eqs) gc =
    gc { gcMap = ins $ gcMap gc
       , gcEqns = Map.insert nm eqs (gcEqns gc)
       , gcDefs = d:gcDefs gc
       }
  where ins = insGlobalBinding vis mnml (identName nm) (DefBinding d)

-- | Lookup ctor returning identifier and type.
resolveCtor :: GlobalContext s -> PosPair Un.Ident -> Int -> TC s (Ident, TCTerm)
resolveCtor gc (PosPair p nm) argc =
  case Map.lookup nm (gcMap gc) of
    Just (CtorBinding dt (Ctor c rtp)) -> do
      tp <- eval p rtp
      if fixedPiArgCount tp == argc then
        return $ (c, termFromTCCtorType (dtgName dt) tp)
      else
        tcFail p "Incorrect number of arguments givne to constructor."
    Just (DataTypeBinding{}) -> tcFail p $ "Pattern matching data type is unsupported."
    Just _ -> fail "Unexpected ident type"
    Nothing -> tcFail p $ "Unknown identifier: " ++ show nm ++ "."

-- TermContext

data TermContext s where
  TopContext :: GlobalContext s -> TermContext s
  LetContext :: TermContext s -> [TCRefLocalDef s] -> TermContext s
  BindContext :: TermContext s -> String -> TCTerm -> TermContext s

boundVarDiff :: TermContext s -> TermContext s -> Int
boundVarDiff tc1 tc0
    | d >= 0 = d
    | otherwise = error $ show $ 
        text "boundVarDiff given bad contexts:" $$
        ppTermContext tc1 $$
        ppTermContext tc0
  where d = termBoundCount tc1 - termBoundCount tc0

termBoundCount :: TermContext s -> Int
termBoundCount TopContext{} = 0
termBoundCount (LetContext tc lcls) = termBoundCount tc + length lcls
termBoundCount (BindContext tc _ _) = termBoundCount tc + 1

-- | Empty term context.
emptyTermContext :: GlobalContext s -> TermContext s
emptyTermContext = TopContext

-- | Add bound var to the context.
consBoundVar :: String -> TCTerm -> TermContext s -> TermContext s
consBoundVar nm tp ctx = BindContext ctx nm tp

-- | Add local definitions to context.
consLocalDefs :: [TCRefLocalDef s] -> TermContext s -> TermContext s
consLocalDefs = flip LetContext

globalContext :: TermContext s -> GlobalContext s
globalContext (BindContext tc _ _) = globalContext tc
globalContext (LetContext tc _) = globalContext tc
globalContext (TopContext gc) = gc

data BoundInfo where
  BoundVar :: String -> BoundInfo
  LocalDef :: String -> BoundInfo

resolveBoundInfo :: DeBruijnIndex -> TermContext s -> BoundInfo
resolveBoundInfo 0 (BindContext _ nm _) = BoundVar nm
resolveBoundInfo i (BindContext tc _ _) = resolveBoundInfo (i-1) tc
resolveBoundInfo i0 (LetContext tc lcls) = lclFn i0 lcls
  where lclFn 0 (LocalFnDefGen nm _ _:_) = LocalDef nm
        lclFn i (_:r) = lclFn (i-1) r
        lclFn i [] = resolveBoundInfo i tc
resolveBoundInfo _ TopContext{} = error "resolveBoundInfo given invalid index."

globalDefEqns :: Ident -> TermContext s -> TCRef s [TCDefEqn]
globalDefEqns i tc = fromMaybe emsg $ Map.lookup i (gcEqns (globalContext tc))
  where emsg = error $ "Could not find equations for " ++ show i ++ "."

data InferResult where
  -- | Ctor with identifier argument list and 
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
                pure $ TypedValue (applyExt (tc1,TCVar 0) tc0)
                                  (applyExt (tc,tp) tc0)
            | otherwise = go tc
        go tc1@(LetContext tc lcls) = lclFn 0 lcls
          where lclFn i (LocalFnDefGen nm tp _ : r)
                    | matchName nm ident =
                        pure $ TypedValue (applyExt (tc1, TCLocalDef i) tc0)
                                          (applyExt (tc,tp) tc0)
                    | otherwise = lclFn (i+1) r
                lclFn _ [] = go tc
        go (TopContext gc) =        
          case Map.lookup ident (gcMap gc) of
            Just (DataTypeBinding (DataTypeGen dt rtp _)) -> do
              ftp <- eval p rtp
              case ftp of
                FPResult s -> pure $ TypedValue (TCF (DataTypeApp dt [])) (TCF (Sort s))
                FPPi pat tp next -> pure $ PartialDataType dt [] pat tp next 
            Just (CtorBinding dt (Ctor c rtp)) -> do
              ftp <- eval p rtp
              case ftp of
                FPResult args ->
                 pure $ TypedValue (TCF (CtorApp c []))
                                   (TCF (DataTypeApp (dtgName dt) args))
                FPPi pat tp next -> pure $ PartialCtor (dtgName dt) c [] pat tp next 
            Just (DefBinding (DefGen gi rtp _)) ->
              TypedValue (TCF (GlobalDef gi)) <$> eval p rtp
            Nothing -> tcFail p $ "Unknown identifier: " ++ show ident ++ "."

contextNames :: TermContext s -> [String]
contextNames (BindContext tc nm _) = nm : contextNames tc
contextNames (LetContext tc lcls) = fmap lclName lcls ++ contextNames tc
  where lclName (LocalFnDefGen nm _ _) = nm
contextNames TopContext{} = []

-- Pretty printing

-- | Pretty print a term context.
ppTermContext :: TermContext s -> Doc
ppTermContext (BindContext tc nm tp) =
  text ("bind " ++ nm) <+> text "::" <+> ppTCTerm tc 1 tp $$
  ppTermContext tc
ppTermContext (LetContext tc lcls) =
    text "let" <+> (nest 4 (vcat (ppLcl <$> lcls))) $$
    ppTermContext tc  
  where ppLcl (LocalFnDefGen nm tp _) = text nm <+> text "::" <+> ppTCTerm tc 1 tp  
ppTermContext TopContext{} = text "top"

-- | Pretty print a pat
ppTCPat :: TCPat -> Doc
ppTCPat (TCPVar nm _ _) = text nm
ppTCPat (TCPUnused nm) = text nm
ppTCPat (TCPatF pf) = 
  case pf of
    UPTuple pl -> parens $ commaSepList (ppTCPat <$> pl)
    UPRecord m -> runIdentity $ ppRecordF (Identity . ppTCPat) m
    UPCtor c l -> hsep (ppIdent c : fmap ppTCPat l)

ppTCTerm :: TermContext s -> Prec -> TCTerm -> Doc
ppTCTerm tc = ppTCTermGen (text <$> contextNames tc)

-- | Pretty print TC term with doc used for free variables.
ppTCTermGen :: [Doc] -> Prec -> TCTerm -> Doc
ppTCTermGen d pr (TCF tf) =
  runIdentity $ ppFlatTermF (\pr' t -> return (ppTCTermGen d pr' t)) pr tf
ppTCTermGen d pr (TCLambda p l r) = ppParens (pr >= 1) $
  char '\\' <> parens (ppTCPat p <+> colon <+> ppTCTermGen d 1 l) 
             <+> text "->" <+> ppTCTermGen (d ++ fmap text (patVarNames p)) 2 r
ppTCTermGen d pr (TCPi p l r) = ppParens (pr >= 1) $
  parens (ppTCPat p <+> colon <+> ppTCTermGen d 1 l) 
    <+> text "->" <+> ppTCTermGen (d ++ fmap text (patVarNames p)) 2 r
ppTCTermGen d pr (TCLet lcls t) = ppParens (pr >= 1) $
    text "let " <> nest 4 (vcat (ppLcl <$> lcls)) $$
    text " in " <> nest 4 (ppTCTermGen (d ++ fmap text (localVarNamesGen lcls)) 1 t)
  where ppLcl (LocalFnDefGen nm tp _) = text nm <+> text "::" <+> ppTCTermGen d 1 tp
ppTCTermGen d _ (TCVar i) | 0 <= i && i < length d = d !! i
                          | otherwise = text $ "Bad variable index " ++ show i
ppTCTermGen d _ (TCLocalDef i) | 0 <= i && i < length d = d !! i
                               | otherwise = text $ "Bad local var index " ++ show i

-- | Bound the free variables in the term with pi quantifiers.
boundFreeVarsWithPi :: (TermContext s, TCTerm) -> TermContext s -> TCTerm
boundFreeVarsWithPi (tc1,t0) tc0 = go d0 tc1 t0 
  where d0 = boundVarDiff tc1 tc0
        go 0 _ t = t
        go d (BindContext tc nm tp) t = go (d-1) tc (TCPi (TCPVar nm 0 tp) tp t) 
        go _ _ _ = error "boundFreeVarsWithPi given bad context"