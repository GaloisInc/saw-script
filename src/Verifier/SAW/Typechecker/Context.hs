{-# LANGUAGE DeriveFoldable #-} 
{-# LANGUAGE DeriveTraversable #-} 
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
module Verifier.SAW.Typechecker.Context
  ( -- * Term definitions
    TCTerm(..)
  , TCTermF(..)
  , TCPat(..)
  , PatF(..)
  , TCDefGen(..)
  , TCDataTypeGen
  , TCDefEqn
  , DefEqnGen(..)
  , LocalDefGen(..)
  , DataTypeGen(..)
  , FixedPiType(..)
  , TCDTType
  , termFromTCDTType
  , TCCtorType
  , termFromTCCtorType
  , TCRefDataType
  , TCRefCtor
  , TCRefDef
  , fmapTCPat
  , fmapTCLocalDefs
  , tcPatVarCount
  , incTCVars
    -- * Global context
  , GlobalContext
  , emptyGlobalContext
  , gcTypes
  , gcDefs
  , insertDataType
  , insertDef
    -- * Term context
  , TermContext
  , emptyTermContext
  , consBoundVar
  , consLocalDefs
  , resolveCtor
  , InferResult(..)
  , resolveIdent
  , resolveBoundVar
  , resolveLocalDef
  , contextNames
  ) where

import Control.Applicative
--import Control.Monad.Trans
import Data.Foldable
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Traversable
import Data.Vector (Vector)

import Prelude hiding (foldr, sum)

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

type TCDefEqn = DefEqnGen (TCPat TCTerm) TCTerm

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

localVarNamesCount :: [LocalDefGen t e] -> Int
localVarNamesCount = length

type TCLocalDef = LocalDefGen TCTerm [TCDefEqn]

data TCTerm
  = TCF !(TCTermF TCTerm)
  | TCLambda !(TCPat TCTerm) !TCTerm !TCTerm
  | TCPi !(TCPat TCTerm) !TCTerm !TCTerm
  | TCLet [TCLocalDef] TCTerm
    -- | A local variable with its deBruijn index and type in the current context.
  | TCVar DeBruijnIndex TCTerm
    -- | A reference to a let bound function with equations.
  | TCLocalDef -- | Index of variable.
               DeBruijnIndex 
               -- | Type 
               TCTerm
 deriving (Show)

data TCPat tp = TCPVar String DeBruijnIndex tp
              | TCPUnused -- ^ Unused pattern
              | TCPatF (PatF (TCPat tp))
  deriving (Show)

data PatF p
   = UPTuple [p]
   | UPRecord (Map FieldName p)
   | UPCtor Ident [p]
  deriving (Functor, Foldable, Traversable, Show)


data TCTermF t
    -- | A global definition identifier.
  = UGlobal Ident

  | UApp t t

  | UTupleValue [t]
  | UTupleType [t]

  | URecordValue (Map FieldName t)
  | URecordSelector t FieldName
  | URecordType (Map FieldName t)

  | UCtorApp Ident [t]
  | UDataType Ident [t]

  | USort Sort
 
  | UNatLit Integer
  | UArray t (Vector t)

  deriving (Show, Functor, Foldable, Traversable)

-- | A pi type that accepted a statically-determined number of arguments.
data FixedPiType r
  = FPResult r
  | FPPi (TCPat TCTerm) TCTerm (FixedPiType r)

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

fmapTCPat :: (Int -> TCTerm -> TCTerm)
          -> Int -> TCPat TCTerm -> TCPat TCTerm
fmapTCPat fn i (TCPVar nm j tp) = TCPVar nm j (fn (i+j) tp)
fmapTCPat _ _ TCPUnused   = TCPUnused
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
termFromTCDTType (FPResult s) = TCF (USort s)
termFromTCDTType (FPPi p tp r) = TCPi p tp (termFromTCDTType r)

termFromTCCtorType :: Ident -> TCCtorType -> TCTerm
termFromTCCtorType dt (FPResult tl) = TCF (UDataType dt tl)
termFromTCCtorType dt (FPPi p tp r) = TCPi p tp (termFromTCCtorType dt r)

tcPatVarCount :: TCPat TCTerm -> Int
tcPatVarCount TCPVar{} = 1 
tcPatVarCount TCPUnused{} = 0
tcPatVarCount (TCPatF pf) = sum (tcPatVarCount <$> pf)


-- | Increment free vars in TC term by given amount if the index is at least the given level.
-- This is used for inserting extra variables to a context.
incTCVars :: Int -> DeBruijnIndex -> TCTerm -> TCTerm
incTCVars ii j = go ii
  where pfn = fmapTCPat go
        go i (TCF tf) = TCF (go i <$> tf)
        go i (TCLambda p tp r) = TCLambda (pfn i p) (go i tp) r'
          where r' = go (i+tcPatVarCount p) r
        go i (TCPi p tp r) = TCPi (pfn i p) (go i tp) r'
          where r' = go (i+tcPatVarCount p) r
        go i (TCLet lcls t) = TCLet (fmapTCLocalDefs go i lcls) t'
          where t' = go (i+localVarNamesCount lcls) t
        go i (TCVar l tp) = TCVar l' (go i tp)
          where l' = if l >= i then l+j else l
        go i (TCLocalDef l tp) = TCLocalDef l' (go i tp)
          where l' = if l >= i then l+j else l

-- Global context stuff

data GlobalBinding r
  = DataTypeBinding (TCDataTypeGen r)
    -- Datatype ident, ctor ident, ctor type.
  | CtorBinding (TCDataTypeGen r) (TCCtorGen r)
  | DefBinding (TCDefGen r)

type GlobalContextMap s = Map Un.Ident (GlobalBinding (TCRef s))

data GlobalContext s = GC { gcMap :: !(GlobalContextMap s)
                          , gcTypes :: ![ TCRefDataType s ]
                          , gcDefs :: ![ TCRefDef s ]
                          } 

emptyGlobalContext :: GlobalContext s
emptyGlobalContext = GC { gcMap = Map.empty
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
insertDef mnml vis d@(DefGen nm _ _) gc =
    gc { gcMap = ins $ gcMap gc
       , gcDefs = d:gcDefs gc
       }
  where ins = insGlobalBinding vis mnml (identName nm) (DefBinding d)

data TermContext s where
  TopContext :: GlobalContext s -> TermContext s
  LetContext :: TermContext s -> [TCRefLocalDef s] -> TermContext s
  BindContext :: TermContext s -> String -> TCTerm -> TermContext s

-- | Empty term context.
emptyTermContext :: GlobalContext s -> TermContext s
emptyTermContext = TopContext

-- | Add bound var to the context.
consBoundVar :: String -> TCTerm -> TermContext s -> TermContext s
consBoundVar nm tp ctx = BindContext ctx nm tp

consLocalDefs :: [TCRefLocalDef s] -> TermContext s -> TermContext s
consLocalDefs = flip LetContext

-- | Lookup ctor returning identifier and type.
resolveCtor :: TermContext s -> PosPair Un.Ident -> Int -> TC s (Ident, TCTerm)
resolveCtor (BindContext tc _ _) p args = resolveCtor tc p args
resolveCtor (LetContext tc _) p args = resolveCtor tc p args
resolveCtor (TopContext gc) (PosPair p nm) argc = do
  case Map.lookup nm (gcMap gc) of
    Just (CtorBinding dt (Ctor c rtp)) -> do
      tp <- eval p rtp
      if fixedPiArgCount tp == argc then
        return $ (c, termFromTCCtorType (dtgName dt) tp)
      else
        tcFail p "Incorrect number of arguments givne to constructor."
    Just (DataTypeBinding{}) -> tcFail p $ "Pattern matching data type is unsupported."
    Just _ -> fail "Unexpected ident type"
    Nothing -> tcFail p $ "Unknown identifierl: " ++ show nm ++ "."

data InferResult where
  -- | Ctor with identifier argument list and 
  PartialCtor :: Ident -- Datatype identifier
              -> Ident -- Ctor identifier.
              -> [TCTerm]
              -> TCPat TCTerm
              -> TCTerm
              -> TCCtorType
              -> InferResult
  PartialDataType :: Ident
                  -> [TCTerm] 
                  -> TCPat TCTerm
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
resolveIdent tc0 (PosPair p ident) = go 0 tc0
  where go i (BindContext tc nm tp)
            | matchName nm ident = pure (TypedValue (TCVar i tp') tp')
            | otherwise = go (i+1) tc
          where tp' = incTCVars 0 (i+1) tp
        go i0 (LetContext tc lcls) = lclFn i0 lcls
          where lclFn i (LocalFnDefGen nm tp _ : r)
                    | matchName nm ident = pure (TypedValue (TCLocalDef i tp') tp')
                    | otherwise = lclFn (i+1) r
                  where tp' = incTCVars 0 (i+1) tp
                lclFn i [] = go i tc
        go _ (TopContext gc) =        
          case Map.lookup ident (gcMap gc) of
            Just (DataTypeBinding (DataTypeGen dt rtp _)) -> do
              ftp <- eval p rtp
              case ftp of
                FPResult s -> pure $ TypedValue (TCF (UDataType dt [])) (TCF (USort s))
                FPPi pat tp next -> pure $ PartialDataType dt [] pat tp next 
            Just (CtorBinding dt (Ctor c rtp)) -> do
              ftp <- eval p rtp
              case ftp of
                FPResult args ->
                 pure $ TypedValue (TCF (UCtorApp c []))
                                   (TCF (UDataType (dtgName dt) args))
                FPPi pat tp next -> pure $ PartialCtor (dtgName dt) c [] pat tp next 
            Just (DefBinding (DefGen gi rtp _)) ->
              TypedValue (TCF (UGlobal gi)) <$> eval p rtp
            Nothing -> tcFail p $ "Unknown identifier: " ++ show ident ++ "."

resolveBoundVar :: DeBruijnIndex -> TermContext s -> String
resolveBoundVar 0 (BindContext _ nm _) = nm
resolveBoundVar i (BindContext tc _ _) = resolveBoundVar (i-1) tc
resolveBoundVar i (LetContext tc lcls)
    | i >= l = resolveBoundVar (i-l) tc
    | otherwise = error "resolveBoundVar given index that refers to let binding"
  where l = length lcls
resolveBoundVar _ TopContext{} = error "resolveBoundVar given invalid index."

resolveLocalDef :: DeBruijnIndex -> TermContext s -> String
resolveLocalDef 0 BindContext{} = 
  error "resolveLocalDef given index that refers to bound var"
resolveLocalDef i (BindContext tc _ _) = resolveLocalDef (i-1) tc
resolveLocalDef i0 (LetContext tc lcls) = lclFn i0 lcls
  where lclFn 0 (LocalFnDefGen nm _ _:_) = nm
        lclFn i (_:r) = lclFn (i-1) r
        lclFn i [] = resolveLocalDef i tc
resolveLocalDef _ TopContext{} = error "resolveLocalDef given invalid index."

contextNames :: TermContext s -> [String]
contextNames (BindContext tc nm _) = nm : contextNames tc
contextNames (LetContext tc lcls) = fmap lclName lcls ++ contextNames tc
  where lclName (LocalFnDefGen nm _ _) = nm
contextNames TopContext{} = []

{-
-- | Checks that references in term point to valid variables.
-- Used for sanity checking terms.
validTermContext :: TermContext s -> TCTerm -> Bool
validTermContext tc it = go 0 it
  where goPat _ _ = True
        go i (TCF tf) = all (go i) tf
        go i (TCLambda p tp r) =
          go i tp && goPat i p && go (i+tcPatVarCount p) r
        go i (TCPi p tp r) =
          go i tp && goPat i p && go (i+tcPatVarCount p) r
        go i (TCLet lcls t) = all goLocal lcls && go i' t
          where i' = i + localVarNamesCount lcls
                goLocal (LocalFnDefGen _ tp eqs) = go i tp && all goEq eqs
                goEq (DefEqnGen pl r) = all (goPat i') pl && go i2 r
                  where i2 = i' + sum (tcPatVarCount <$> pl)
        go i (TCVar j t) = 0 <= j && j < i + tcLevel tc
        go i (TCLocalDef j t) = 0 <= j && j < i + tcLevel tc
-}