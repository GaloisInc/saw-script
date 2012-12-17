{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveFoldable #-} 
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Verifier.SAW.Typechecker
  ( unsafeMkModule
  ) where

import Control.Applicative ((<$>))
import Control.Exception (assert)

import Control.Monad (liftM2, liftM3, zipWithM_)
import Control.Monad.State hiding (forM, forM_, mapM, mapM_)
import Control.Monad.Identity (Identity)

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe, isNothing)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Traversable
import Data.Vector (Vector)
import qualified Data.Vector as V

import Prelude hiding (all, concatMap, foldl, foldr, mapM, mapM_)

import Debug.Trace

import Verifier.SAW.Utils

import Verifier.SAW.Position
import Verifier.SAW.UntypedAST ( PosPair(..))
import Verifier.SAW.TypedAST
import qualified Verifier.SAW.UntypedAST as Un

lift2 :: (a -> b) -> (b -> b -> c) -> a -> a -> c
lift2 f h x y = h (f x) (f y) 

mkEdgeMap :: Ord a => [(a,a)] -> Map a [a]
mkEdgeMap = foldl' fn Map.empty
  where fn m (x,y) = Map.insertWith (++) x [y] m

-- | Given a project function returning a key and a list of values, return a map
-- from the keys to values.
projMap :: Ord k => (a -> k) -> [a] -> Map k a
projMap f l = Map.fromList [ (f e,e) | e <- l ] 

flipPair :: (a,b) -> (b,a)
flipPair (x,y) = (y,x)

-- | Given a list of keys and values, construct a map that maps each key to the list
-- of values.
multiMap :: Ord k => [(k,a)] -> Map k [a]
multiMap = foldl' fn Map.empty
  where fn m (k,v) = Map.insertWith (++) k [v] m

orderedListMap :: Ord a => [a] -> Map a Int
orderedListMap l = Map.fromList (l `zip` [0..])

sepKeys :: Map k v -> ([k],[v])
sepKeys m = (Map.keys m, Map.elems m)

topSort :: forall a . Ord a
        => Set a -- List of vertices.
        -> [(a,a)] -- List of edges
        -> Either (Map a Int) [a]
topSort vertices e = go (initNulls, initMap) []
  where vl = Set.toList vertices
        outEdgeMap = mkEdgeMap e
        outEdges v = Map.findWithDefault [] v outEdgeMap
        inEdgeMap = mkEdgeMap (flipPair <$> e)
        -- Nodes that have edge to the given node. 
        inEdges :: a -> [a]
        inEdges v = Map.findWithDefault [] v inEdgeMap
        initNulls = filter (null . inEdges) vl
        initMap = Map.fromList [  (v,l) | v <- vl
                               , let l = length (inEdges v)
                               , l > 0
                               ]
        decInEdgeCount :: ([a], Map a Int) -> a -> ([a], Map a Int)
        decInEdgeCount (l,zm) v = 
            case Map.lookup v zm of
                    Nothing -> error "internal: topSort did not maintain edge count"
                    Just 1 -> (v:l, Map.delete v zm)
                    Just n -> assert (n > 1) $ (l, Map.insert v (n-1) zm)
        go :: ([a], Map a Int) -> [a] -> Either (Map a Int) [a]
        go ([],zm) r | Map.null zm = Right (reverse r)
                     | otherwise = Left zm
        go (h:l,zm) r = go (foldl' decInEdgeCount (l,zm) (outEdges h)) (h:r)

mapDefEqn :: (p -> q) -> (s -> t) -> DefEqnGen p s -> DefEqnGen q t
mapDefEqn pfn tfn (DefEqnGen pl rhs) = DefEqnGen (pfn <$> pl) (tfn rhs)

failPos :: Monad m => Pos -> String -> m a
failPos p msg = fail $ show p ++ ": " ++ msg
 

type DeBruijnLevel = DeBruijnIndex

-- Global context declarations.

data RigidVarRef = RigidVarRef { rvrPos :: !(Maybe Un.Pos)
                               , rvrName :: String
                               , rvrIndex :: !Int
                               }

instance Eq RigidVarRef where
  (==) = lift2 rvrIndex (==)

instance Ord RigidVarRef where
  compare = lift2 rvrIndex compare

instance Show RigidVarRef where
  showsPrec p r = case rvrPos r of
                    Nothing -> (rvrName r ++)
                    Just po -> showParen (p >= 10) f
                      where f = (++) (ppPos "" po ++ " " ++ rvrName r)


data LocalDefGen n p t
   = LocalFnDefGen n t [DefEqnGen p t]
  deriving (Show)

localVarNamesGen :: LocalDefGen n p e -> [n]
localVarNamesGen (LocalFnDefGen nm _ _) = [nm]

data DefEqnGen p t
   = DefEqnGen [p]  -- ^ List of patterns
                t -- ^ Right hand side.
  deriving (Show)

type UnPat = (Un.ParamType, [Un.Pat])
type UnCtor = Ctor String Un.Term
type UnDataType = DataType String Un.Term
type UnDefEqn = DefEqnGen Un.Pat Un.Term
type UnLocalDef = LocalDefGen (PosPair String) Un.Pat Un.Term

{-
type NormalizedCtorType = CtorType Un.Pat Un.Term

normalizeUnCtorType :: UnCtorType -> NormalizedCtorType
normalizeUnCtorType = go
  where go (CtorResult r) = CtorResult r
        go (CtorArg (_,pats) l r) = foldr ins (go r) pats
          where ins p = CtorArg p l
-}

data GlobalBinding 
  = CtorIdent Ident
  | DataTypeIdent Ident
  | DefIdent Ident

-- | Tracks untyped theory and provides information for parsing typed terms.
data GlobalContext = GlobalContext {
        gcModule :: Module
        -- | Maps untyped identifiers for constructors to the typed identifier.
      , ctxGlobalBindings :: Map Un.Ident GlobalBinding
      , ctxNewDataTypes :: [UnDataType]
      , ctxNewDefTypes :: [(String, Un.Term)]
      , ctxNewEqns :: [(String, UnDefEqn)]
      }

ctxModuleName :: GlobalContext -> ModuleName
ctxModuleName = moduleName . gcModule

data TermContext = TermContext {
   tcGlobalContext :: !GlobalContext
   -- | Maps each variable to the term it is bound to in the current
   -- context.
 , tcVarBindings :: !(Map Un.Ident UnifyTerm)
 }

emptyTermContext :: GlobalContext -> TermContext
emptyTermContext ctx = TermContext ctx Map.empty

tcFindGlobalBinding :: Un.Ident -> TermContext -> Maybe GlobalBinding
tcFindGlobalBinding i tc = Map.lookup i (ctxGlobalBindings (tcGlobalContext tc))

tcFindLocalBinding :: Un.Ident -> TermContext -> Maybe UnifyTerm
tcFindLocalBinding i tc = mplus (Map.lookup i (tcVarBindings tc)) globalRes
  where globalRes =
          case tcFindGlobalBinding i tc of
            Just (DefIdent i) -> Just (UGlobal i)
            _ -> Nothing

bindLocalTerm :: String -> UnifyTerm -> TermContext -> TermContext
bindLocalTerm nm t ctx = ctx { tcVarBindings = Map.insert (Un.localIdent nm) t m }
  where m = tcVarBindings ctx

addLocalBindings :: TermContext -> [RigidVarRef] -> TermContext
addLocalBindings ctx l = ctx { tcVarBindings = foldl' fn (tcVarBindings ctx) l }
  where fn m r = Map.insert (Un.localIdent (rvrName r)) (URigidVar r) m

-- | Organizes information about local declarations.
type LocalDeclsGroup = [UnLocalDef]

type GroupLocalDeclsState = ( Map String (PosPair String, Un.Term)
                            , Map String [UnDefEqn]
                            )

groupLocalDecls :: [Un.Decl] -> LocalDeclsGroup
groupLocalDecls = finalize . foldl groupDecl (Map.empty,Map.empty)
  where finalize :: GroupLocalDeclsState -> LocalDeclsGroup
        finalize (tpMap,eqMap) = fn <$> Map.elems tpMap
          where fn :: (PosPair String, Un.Term) -> UnLocalDef
                fn (pnm,tp) = LocalFnDefGen pnm tp eqs
                  where Just eqs = Map.lookup (val pnm) eqMap
        groupDecl :: GroupLocalDeclsState -> Un.Decl -> GroupLocalDeclsState
        groupDecl (tpMap,eqMap) (Un.TypeDecl idl tp) = (tpMap',eqMap)
          where tpMap' = foldr (\k -> Map.insert (val k) (k,tp)) tpMap idl
        groupDecl (tpMap,eqMap) (Un.TermDef pnm pats rhs) = (tpMap, eqMap')
          where eq = DefEqnGen (snd <$> pats) rhs
                eqMap' = Map.insertWith (++) (val pnm) [eq] eqMap
        groupDecl _ Un.DataDecl{} = error "Unexpected data declaration in let binding"


data VarIndex = VarIndex { fvrIndex :: !Int
                         , _fvrName :: !(PosPair String)
                         }
  deriving (Show)

instance Eq VarIndex where
  (==) = lift2 fvrIndex (==)

instance Ord VarIndex where
  compare = lift2 fvrIndex compare

data UVar = UPRigid RigidVarRef | UIVar VarIndex
  deriving (Eq, Ord, Show)

data PatF c f p
   = UPTuple [p]
   | UPRecord (Map f p)
   | UPCtor c [p]
  deriving (Foldable, Show)

data UPat = UPVar RigidVarRef
          | UPUnused VarIndex -- ^ Unused pattern
          | UPatF (Maybe Un.Pos) (PatF Ident FieldName UPat)
  deriving (Show)

upatBoundVars :: UPat -> [RigidVarRef]
upatBoundVars (UPVar r) = [r]
upatBoundVars UPUnused{} = []
upatBoundVars (UPatF _ pf) = concatMap upatBoundVars pf

upatBoundVarCount :: UPat -> DeBruijnIndex
upatBoundVarCount UPVar{} = 1
upatBoundVarCount UPUnused{} = 0
upatBoundVarCount (UPatF _ pf) = sumBy upatBoundVarCount pf

upatToTerm :: UPat -> UnifyTerm
upatToTerm (UPVar r) = URigidVar r
upatToTerm (UPUnused i) = UnificationVar i
upatToTerm (UPatF _ pf) =
  case pf of
    UPTuple l  -> UTupleValue  (upatToTerm <$> l)
    UPRecord m -> URecordValue (upatToTerm <$> m)
    UPCtor c l -> UCtorApp c   (upatToTerm <$> l)

type UnifyLocalDef = LocalDefGen RigidVarRef UPat UnifyTerm

data UnifyTerm
  = URigidVar RigidVarRef -- ^ Rigid variable that cannot be instantiated.
  | UnificationVar VarIndex

    -- | A global definition.
  | UGlobal Ident
  
  | ULambda UPat UnifyTerm UnifyTerm
  | UApp UnifyTerm UnifyTerm
  | UPi UPat UnifyTerm UnifyTerm

  | UTupleValue [UnifyTerm]
  | UTupleType [UnifyTerm]

  | URecordValue (Map FieldName UnifyTerm)
  | URecordSelector UnifyTerm FieldName
  | URecordType (Map FieldName UnifyTerm)

  | UCtorApp Ident [UnifyTerm]
  | UDataType Ident [UnifyTerm]

  | USort Sort
 
  | ULet [UnifyLocalDef] UnifyTerm
  | UIntLit Integer
  | UArray UnifyTerm (Vector UnifyTerm)

  deriving (Show)

addUnifyTermVars :: Set UVar -> UnifyTerm -> Set UVar
addUnifyTermVars = go
  where go s (URigidVar sym) = Set.insert (UPRigid sym) s
        go s (ULambda _ x y) = go (go s x) y
        go s (UApp x y)      = go (go s x) y
        go s (UPi _ x y)     = go (go s x) y
        go s (UTupleValue l) = foldl' go s l
        go s (UTupleType l)  = foldl' go s l
        go s (URecordValue m) = foldl' go s m
        go s (URecordSelector x _) = go s x
        go s (URecordType m) = foldl' go s m
        go s (UCtorApp _ l) = foldl' go s l
        go s (UDataType _ l) = foldl' go s l
        go s (ULet _ x) = go s x
        go s (UArray x v) = foldl' go (go s x) v
        go s (UnificationVar i) = Set.insert (UIVar i) s
        go s _ = s

data UnifyEq
    -- | Assert two terms are equal types (i.e., have type Set a for some a).
  = UnifyEqTypes UnifyTerm UnifyTerm
  | UnifyEqValues UnifyTerm UnifyTerm UnifyTerm
  | UnifyPatHasType UPat UnifyTerm

data VarBinding = TypeBinding UnifyTerm
                  -- | ValueBinding contains term and type.
                | ValueBinding UnifyTerm UnifyTerm

varBindingTerm :: VarBinding -> UnifyTerm
varBindingTerm (TypeBinding t) = t
varBindingTerm (ValueBinding t _) = t

type UnifyDataType = DataType Ident UnifyTerm
type UnifyCtor = Ctor Ident UnifyTerm
type UnifyDefEqn = DefEqnGen UPat UnifyTerm

--type UnifyCtorType = CtorType UPat UnifyTerm

data UnifyState = US { usGlobalContext :: Maybe GlobalContext
                     , usTypeMap :: Map RigidVarRef UnifyTerm
                     , usVarBindings :: Map VarIndex VarBinding
                     , usCtorTypes :: Map Ident (Either Un.Term Term)
                     , unifyEqs :: [UnifyEq]
                     , usVars :: Set UVar
                       -- An element (p,s) in usEdges asserts that p must come before s.
                     , usEdges :: Set (UVar,UVar)
                     , nextVarIndex :: Int
                     , nextRigidIndex :: Int
                     }

emptyUnifyState :: UnifyState
emptyUnifyState =
    US { usGlobalContext = Nothing
       , usTypeMap = Map.empty
       , usVarBindings = Map.empty
       , usCtorTypes = Map.empty
       , unifyEqs = []
       , usVars = Set.empty
       , usEdges = Set.empty
       , nextVarIndex = 0
       , nextRigidIndex = 0
       }

pushUnifyEqs :: [UnifyEq] -> UnifyState -> UnifyState
pushUnifyEqs eqs s = s { unifyEqs = eqs ++ unifyEqs s }

type Unifier = State UnifyState

addEdge :: UVar -> UVar -> Unifier ()
addEdge p q = modify $ \s -> s { usEdges = Set.insert (p,q) (usEdges s) }

newRigidVar :: Maybe Un.Pos -> String -> Unifier RigidVarRef
newRigidVar p nm = state fn
  where fn s = (v, s')
          where idx = nextRigidIndex s
                v = RigidVarRef p nm idx 
                s' = s { usVars = Set.insert (UPRigid v) (usVars s)
                       , nextRigidIndex = idx + 1
                       }

-- | Set the type of a rigid variable.
setRigidVarType :: RigidVarRef -> UnifyTerm -> Unifier ()
setRigidVarType sym tp = modify $ \s ->
  case Map.lookup sym (usTypeMap s) of
    Just prevTp ->
      pushUnifyEqs [UnifyEqTypes tp prevTp] s
    Nothing ->
      s { usTypeMap = Map.insert sym tp (usTypeMap s) }

newUnifyVarIndex :: PosPair String -> Unifier VarIndex
newUnifyVarIndex nm = state fn
  where fn us = (v, us')
          where idx = nextVarIndex us
                v = VarIndex idx nm
                us' = us { usVars = Set.insert (UIVar v) (usVars us) 
                         , nextVarIndex = idx + 1
                         }

addUnifyEqs :: [UnifyEq] -> Unifier ()
addUnifyEqs = modify . pushUnifyEqs

bindVar :: VarIndex -> VarBinding -> Unifier ()
bindVar i b = modify fn
  where fn s = case Map.lookup i m of
                 Nothing -> s { usVarBindings = Map.insert i b m }
                 Just (TypeBinding u) -> do
                   case b of
                     TypeBinding t -> pushUnifyEqs [UnifyEqTypes t u] s
                     ValueBinding t tp -> pushUnifyEqs [UnifyEqValues t u tp] s
                 Just (ValueBinding u utp) -> do
                   case b of
                     TypeBinding t -> pushUnifyEqs [UnifyEqValues t u utp] s
                     ValueBinding t ttp -> pushUnifyEqs eqs s
                       where eqs = [ UnifyEqTypes ttp utp
                                   , UnifyEqValues t u ttp]
          where m = usVarBindings s

addTypeEq :: UnifyTerm -> UnifyTerm -> Unifier ()
addTypeEq x y = addUnifyEqs [UnifyEqTypes x y]

unifyTypes :: UnifyTerm -> UnifyTerm -> Unifier ()
unifyTypes (URigidVar x) (URigidVar y) | x == y = return ()
unifyTypes (UnificationVar i) y = bindVar i (TypeBinding y)
unifyTypes x (UnificationVar j) = bindVar j (TypeBinding x)
unifyTypes (UGlobal x) (UGlobal y) | x == y = return ()
unifyTypes (UTupleType l) (UTupleType r)   = zipWithM_ addTypeEq l r
unifyTypes (URecordType l) (URecordType r) =
  assert (Map.keys l == Map.keys r) $
    zipWithM_ addTypeEq (Map.elems l) (Map.elems r)
unifyTypes (UDataType ld l) (UDataType rd r) =
  assert (ld == rd) $
    zipWithM_ addTypeEq l r
unifyTypes (USort s) (USort t) | s == t = return ()
unifyTypes x y = fail $ "unifyTypes failed " ++ show (x,y)

unifyTerms :: UnifyTerm -> UnifyTerm -> UnifyTerm -> Unifier ()
unifyTerms (UTupleValue l) (UTupleValue r) (UTupleType tpl)
  | (length l == length tpl && length r == length tpl) 
  = addUnifyEqs $ zipWith3 UnifyEqValues l r tpl

unifyTerms (URecordValue l) (URecordValue r) (URecordType tpm)
    | (lk == tpk && rk == tpk) = addUnifyEqs $ zipWith3 UnifyEqValues le re tpe
  where (lk, le)  = sepKeys l
        (rk, re)  = sepKeys r
        (tpk,tpe) = sepKeys tpm

unifyTerms x y USort{} = unifyTypes x y
unifyTerms x y tp = internalError $ "unifyTerms failed " ++ show (x,y,tp)

-- | Add untyped pat bindings to context, each of which have the given type,
consPatVars :: TermContext
            -> [Un.Pat]
            -> UnifyTerm
            -> Unifier (TermContext, [UPat])
consPatVars ctx upl tp = do
  pl <- mapM (indexUnPat (tcGlobalContext ctx)) upl
  addUnifyEqs $ (\p -> UnifyPatHasType p tp) <$> pl
  let ctx' = addLocalBindings ctx (concatMap upatBoundVars pl)
  return (ctx', pl)

-- | Create a set of constraints for matching a list of patterns against a given pi type.
instPiType -- | Continuation to generate final constraints
           :: [UPat] -- ^ Patterns to match
           -> UnifyTerm -- ^ Expected pi type 
           -> Unifier UnifyTerm
instPiType = go
  where go [] ltp = return ltp
        go (p:pl) ltp =
          case ltp of
            UPi pat lhs rhs -> do
              addUnifyEqs [UnifyPatHasType p lhs]
              let lhsSub = matchPat p pat
              rhs' <- applyUnifyPatSub lhsSub rhs
              go pl rhs' 
            _ -> internalError $ "Could not parse " ++  show ltp ++ " as pi type"

convertEqn :: TermContext
           -> UnifyTerm
           -> UnDefEqn
           -> Unifier UnifyDefEqn
convertEqn ctx tp (DefEqnGen unpats unrhs) = do
  pats <- mapM (indexUnPat (tcGlobalContext ctx)) unpats
  _rhsTp <- instPiType pats tp
  let ctx' = addLocalBindings ctx (concatMap upatBoundVars pats)
  rhs <- convertTerm ctx' unrhs
  return (DefEqnGen pats rhs)

-- | Insert local definitions the terms belong to the given context.
consLocalDecls :: TermContext -> [Un.Decl] -> Unifier (TermContext, [UnifyLocalDef])
consLocalDecls tc udl = do
  let procDef (LocalFnDefGen pnm utp ueqs) = do
        let nm = val pnm
        r <- newRigidVar (Just (pos pnm)) nm
        tp <- convertTerm tc utp
        setRigidVarType r tp
        return (r, (r, tp, ueqs))
  (nl,dl') <- unzip <$> mapM procDef (groupLocalDecls udl)
  let tc1 = addLocalBindings tc nl
  let procEqns (r, tp, ueqs) = do
        res <- forM ueqs $ \(DefEqnGen unpat unrhs) -> do
          pat <- mapM (indexUnPat (tcGlobalContext tc)) unpat
          _rhsTp <- instPiType pat tp
          let tc2 = addLocalBindings tc1 (concatMap upatBoundVars pat)
          rhs <- convertTerm tc2 unrhs
          return (DefEqnGen pat rhs)
        return (LocalFnDefGen r tp res)
  dl <- mapM procEqns dl'
  return (tc1, dl)

-- | Convert an untyped expression into a term for unification.
convertTerm :: TermContext -> Un.Term -> Unifier UnifyTerm
convertTerm ctx (Un.asApp -> (Un.Con i, uargs)) = do
  args <- mapM (convertTerm ctx) uargs
  case tcFindGlobalBinding (val i) ctx of
    Just (CtorIdent c)      -> return $ UCtorApp c args
    Just (DataTypeIdent dt) -> return $ UDataType dt args
    Just DefIdent{} -> internalError "Found def identifier bound to constructor ident"
    Nothing -> fail $ "Failed to find constructor for " ++ show i ++ "."
convertTerm tc uut =
  case uut of
    Un.Var i ->
      case tcFindLocalBinding (val i) tc of
        Just t -> return t
        Nothing -> failPos (pos i) $ show (val i) ++ " unbound in current context."
    Un.Unused{} -> fail "Pattern syntax when term expected"
    Un.Con{} -> fail "Unexpected constructor"
    Un.Sort _ s -> return (USort s)
    Un.Lambda _ args rhs -> procArgs tc args
      where procArgs :: TermContext
                     -> [(Un.ParamType, [Un.Pat], Un.Term)]
                     -> Unifier UnifyTerm
            procArgs lctx [] = convertTerm lctx rhs 
            procArgs lctx ((_,patl,utp):l) = do
              tp <- convertTerm lctx utp
              (lctx',pl) <- consPatVars lctx patl tp
              rest <- procArgs lctx' l
              return $ foldr (\p -> ULambda p tp) rest pl
    Un.App f _ t -> liftM2 UApp (convertTerm tc f) (convertTerm tc t)
    Un.Pi _ pats utp _ rhs -> do
      tp <- convertTerm tc utp
      (tc', pl) <- consPatVars tc pats tp
      rest <- convertTerm tc' rhs
      return $ foldr (\p -> UPi p tp) rest pl

    Un.TupleValue _ tl -> UTupleValue <$> mapM (convertTerm tc) tl
    Un.TupleType _ tl  -> UTupleType <$> mapM (convertTerm tc) tl

    Un.RecordValue _ fl -> do
      let (fields,uterms) = unzip fl
      terms <- mapM (convertTerm tc) uterms
      return $ URecordValue (Map.fromList (fmap val fields `zip` terms))
    Un.RecordSelector ux i -> (flip URecordSelector (val i)) <$> convertTerm tc ux
    Un.RecordType _ fl -> do
      let (fields,uterms) = unzip fl
      terms <- mapM (convertTerm tc) uterms
      return $ URecordType (Map.fromList (fmap val fields `zip` terms))

    Un.TypeConstraint t _ _ -> convertTerm tc t
    Un.Paren _ t -> convertTerm tc t
    Un.LetTerm _ udl urhs -> do
      (tc',dl) <- consLocalDecls tc udl
      rhs <- convertTerm tc' urhs
      return $ ULet dl rhs
    Un.IntLit _ i -> return $ UIntLit i
    Un.BadTerm p -> fail $ "Encountered bad term from position " ++ show p

type UnifyPatSubst = Map RigidVarRef UPat

matchUnPat :: UPat -> Un.Pat -> TermContext -> TermContext
matchUnPat = go
  where goList :: [(UPat, Un.Pat)] -> TermContext -> TermContext
        goList [] ctx = ctx
        goList ((s,p):l) ctx = goList l (go s p ctx)
        go :: UPat -> Un.Pat -> TermContext -> TermContext
        go t (Un.PVar v) ctx = bindLocalTerm (val v) (upatToTerm t) ctx
        go _ Un.PUnused{}  ctx = ctx
        go (UPatF _ (UPTuple sl)) (Un.PTuple _ pl) ctx
          | length sl == length pl = goList (zip sl pl) ctx
        go (UPatF _ (UPRecord sm)) (Un.PRecord _ pl) ctx
            | sk == pk =  goList (zip se pe) ctx
          where pm = Map.fromList [ (val f, p) | (f,p) <- pl ]
                (sk,se) = sepKeys sm
                (pk,pe) = sepKeys pm
        go (UPatF _ (UPCtor sc sl)) (Un.PCtor pc pl) ctx
            | sc == c && length sl == length pl
            = goList (zip sl pl) ctx
          where Just (CtorIdent c) = tcFindGlobalBinding (val pc) ctx

-- | @matchPat vpat tppat pattype@ matches the pattern @vpat@ against the variables
-- in @tppat@ which is assumed to have the type @pattype@.  It returns the a substituion
-- from the vars bound in tppat to terms in vpat.
-- @tppat@ is assumed to have type @pattype".
matchPat :: UPat -> UPat -> UnifyPatSubst
matchPat = go Map.empty 
  where goList :: UnifyPatSubst -> [(UPat, UPat)] -> UnifyPatSubst
        goList sub [] = sub
        goList sub ((s,p):l) = goList (go sub s p) l
        go :: UnifyPatSubst -> UPat -> UPat -> UnifyPatSubst
        go sub s (UPVar r) = Map.insert r s sub
        go sub _ UPUnused{} = sub
        go sub s@(UPatF _ sf) p@(UPatF _ pf) =
          case (sf,pf) of
            (UPTuple sl, UPTuple pl)
              | length sl == length pl -> goList sub (zip sl pl)
            (UPRecord sm, UPRecord pm)
                | sk == pk -> goList sub (zip se pe)
              where (sk, se)  = sepKeys sm
                    (pk, pe)  = sepKeys pm
            (UPCtor sc sl, UPCtor pc pl)
                | sc == pc -> goList sub (zip sl pl)
            _ -> internalError $ "matchPat failed to match " ++ show (s,p)  
        go _ s p = internalError $ "matchPat failed to match " ++ show (s,p)  

-- | @checkCtorType c cpl tp@ checks that the pattern @c(cpl)@ has type @tp@.
checkCtorType :: Ident -> [UPat] -> UnifyTerm -> Unifier ()
checkCtorType c cpl ctorType = do
  Just gctx <- gets usGlobalContext
  m <- gets usCtorTypes
  case Map.lookup c m of
    Nothing -> internalError $ "Could not find ctor type for " ++ show c ++ "."
    Just (Left untp) -> go (emptyTermContext gctx) cpl untp
      where go :: TermContext -> [UPat] -> Un.Term -> Unifier ()
            go ctx initPl (Un.Pi _ initPats ulhs _ rhsTp) = do
              lhs <- convertTerm ctx ulhs
              let procPat (p:pl) (pat:patl) c = do
                   hasType p lhs 
                   procPat pl patl (matchUnPat p pat c)
                  procPat pl [] c = go c pl rhsTp
              procPat initPl initPats ctx
            go ctx [] urhsTp = do
              rhsTp <- convertTerm ctx urhsTp 
              addUnifyEqs [UnifyEqTypes rhsTp ctorType]
    Just (Right _tp) -> internalError "Typed ctor types unsupported"

hasType :: UPat
        -> UnifyTerm
        -> Unifier ()
hasType (UPVar v) tp = setRigidVarType v tp
hasType (UPUnused _) _ = return ()
hasType (UPatF _ pf) tp =
  case pf of
    UPTuple pl ->
      case tp of
        UTupleType tpl | length pl == length tpl ->
          zipWithM_ hasType pl tpl
        _ -> internalError $ "Could not match tuple pattern against type " ++ show tp
    UPRecord pm ->
      case tp of
        URecordType tpm | Map.keys pm == Map.keys tpm ->
          zipWithM_ hasType (Map.elems pm) (Map.elems tpm)
        _ -> internalError "Could not match record pattern"
    UPCtor c cpl -> checkCtorType c cpl tp

applyUnifyPatSub :: UnifyPatSubst -> UnifyTerm -> Unifier UnifyTerm
applyUnifyPatSub sub = go 
  where boundv = Map.keys sub
        isUnbound v = Map.notMember v sub
        go :: UnifyTerm -> Unifier UnifyTerm
        go t@(URigidVar r) = return $ fromMaybe t (upatToTerm <$> Map.lookup r sub)
        -- Unification variables had to be bound in an outer context, and hence cannot
        -- refer to variables in the substitution.
        go t@(UnificationVar v) = do
          mapM_ (\r -> addEdge (UPRigid r) (UIVar v)) boundv
          return t
        go t@UGlobal{} = return t
        go (ULambda pat tp rhs) 
          | all isUnbound (upatBoundVars pat) =
            liftM2 (ULambda pat) (go tp) (go rhs)
        go (UApp x y) = liftM2 UApp (go x) (go y)
        go (UPi pat tp rhs)
          | all isUnbound (upatBoundVars pat) =
            liftM2 (UPi pat) (go tp) (go rhs)
        go (UTupleValue l) = UTupleValue <$> mapM go l
        go (UTupleType l)  = UTupleType <$> mapM go l
        go (URecordValue m) = URecordValue <$> mapM go m
        go (URecordSelector t f) = (flip URecordSelector f) <$> go t
        go (URecordType m) = URecordType <$> mapM go m
        go (UCtorApp i l) = UCtorApp i <$> mapM go l
        go (UDataType i l) = UDataType i <$> mapM go l
        go t@USort{} = return t
        go ULet{} = internalError "applyUnifyPatSub does not support ULet"
        go t@UIntLit{} = return t
        go (UArray tp v) = liftM2 UArray (go tp) (mapM go v)

{-
-- | Instantiate local variables with patterns.
instWithUnPat :: UnifyTerm -> V.Vector UnifyTerm -> Unifier UnifyTerm
instWithUnPat pv = go 0
  where plen = V.length pv
        go :: Int -> UnifyTerm -> Unifier UnifyTerm
        go _ _ = internalError "instWithUnPat undefined"
        go bnd (Term tf) = 
          case tf of 
            LocalVar i tp
              | i < bnd        -> return (ULocalVar i tp)
              | i - bnd < plen -> return (pv V.! (i-bnd))
              | otherwise      -> return (ULocalVar (i-bnd) tp)
            GlobalDef d -> return (UGlobal d)

            Lambda pat lhs rhs ->
                liftM3 ULambda
                       (indexPat pat)
                       (go bnd lhs)
                       (go (bnd + patBoundVarCount pat) rhs)
            App x y ->
              liftM2 UApp (go bnd x) (go bnd y)
            Pi pat lhs rhs ->
                liftM3 UPi
                       (indexPat pat)
                       (go bnd lhs)
                       (go (bnd + patBoundVarCount pat) rhs)

            TupleValue l -> UTupleValue <$> mapM (go bnd) l
            TupleType l  -> UTupleType  <$> mapM (go bnd) l

            RecordValue m -> URecordValue <$> mapM (go bnd) m
            RecordSelector x f -> flip URecordSelector f <$> go bnd x
            RecordType m  -> URecordType <$> mapM (go bnd) m

            CtorValue c l -> UCtorApp c <$> mapM (go bnd) l
            CtorType dt l -> UDataType dt <$> mapM (go bnd) l

            Sort s -> return (USort s)
            Let dl t -> ULet dl <$> go (bnd + length dl) t
            IntLit i -> return (UIntLit i)
            ArrayValue tp v -> do
               liftM2 UArray (go bnd tp) (mapM (go bnd) v)
-}


data UnifyResult =
       UResult { -- Maps each rigid variable to the number of variables
                 -- in the patterns bound before it, and the type.
                 urRigidIndexMap :: Map RigidVarRef (Int,UnifyTerm)
                 -- | Maps unification vars to the term
               , urVarBindings :: Map VarIndex UnifyTerm
               , urModule :: Module
               , urLevel :: !DeBruijnLevel
                  -- | Maps rigid var refs in the current context to the level
                  -- and type when they were bound.
               , urRigidTypeMap :: Map RigidVarRef (DeBruijnLevel,Term)
               }

completePat :: DeBruijnLevel -> UnifyResult -> UPat -> Pat Term
completePat lvl0 r = go
  where go (UPVar v) = assert (i >= lvl0) $ PVar (rvrName v) (i-lvl0) tp
          where Just (i,tp) = Map.lookup v (urRigidTypeMap r)
        go UPUnused{} = PUnused
        go (UPatF _ pf) =
          case pf of
            UPTuple l -> PTuple (go <$> l)
            UPRecord m -> PRecord (go <$> m)
            UPCtor uc l -> PCtor c (go <$> l) 
              where Just c = findCtor (urModule r) uc

-- | Bind list of rigid variables in result.
bindPatImpl :: UnifyResult -> [RigidVarRef] -> UnifyResult
bindPatImpl r [] = r
bindPatImpl r0 bvl = rf
  where err v = internalError $ "bindPatImpl: Cannot find binding for " ++ show v
        -- Get rigid vars sorted by index
        uvl = Map.elems
            $ Map.fromList [ (i,(v,tp))
                           | v <- bvl
                           , let (i,tp) = fromMaybe (err v)
                                        $ Map.lookup v (urRigidIndexMap r0)
                           ]
        addVar :: UnifyResult -> (RigidVarRef,UnifyTerm) -> UnifyResult
        addVar r (v,utp) = r'
         where tp = completeTerm r utp
               lvl = urLevel r
               r' = r { urLevel = lvl + 1
                      , urRigidTypeMap = Map.insert v (lvl,tp) (urRigidTypeMap r)
                      }
        rf = foldl' addVar r0 uvl

bindPat :: UnifyResult -> UPat -> (UnifyResult, Pat Term)
bindPat r0 up = (r,completePat (urLevel r0) r up)
  where r = bindPatImpl r0 (upatBoundVars up)

bindPats :: UnifyResult -> [UPat] -> (UnifyResult, [Pat Term])
bindPats r0 upl = (r, completePat (urLevel r0) r <$> upl)
  where r = bindPatImpl r0 (concatMap upatBoundVars upl)

-- | Returns the type of a unification term in the current context.
completeTerm :: UnifyResult
             -> UnifyTerm
             -> Term
completeTerm = go
  where go r ut =
          case ut of
            URigidVar v -> incVars 0 (urLevel r - l) t
              where err = "Could not complete term: unknown type " ++ show (v,urRigidTypeMap r)
                    (l,t) = fromMaybe (internalError err) $
                              Map.lookup v (urRigidTypeMap r)
            UnificationVar i -> go r t
              where Just t = Map.lookup i (urVarBindings r)
            UGlobal i -> Term (GlobalDef d)
              where Just d = findDef (urModule r) i
            ULambda p lhs rhs -> Term (Lambda p' (go r lhs) (go r' rhs))
              where (r',p') = bindPat r p
            UApp x y  -> Term $ App (go r x) (go r y)
            UPi p lhs rhs -> Term (Pi p' (go r lhs) (go r' rhs))
              where (r',p') = bindPat r p
            UTupleValue l -> Term $ TupleValue (go r <$> l)
            UTupleType l  -> Term $ TupleType  (go r <$> l)
            URecordValue m      -> Term $ RecordValue (go r <$> m)
            URecordSelector x f -> Term $ RecordSelector (go r x) f
            URecordType m       -> Term $ RecordType (go r <$> m)
            UCtorApp i l   -> Term $ CtorValue c (go r <$> l)
              where Just c = findCtor (urModule r) i
            UDataType i l -> Term $ CtorType dt (go r <$> l)
              where Just dt = findDataType (urModule r) i
            USort s   -> Term $ Sort s
            ULet dl t -> Term $ Let (completeLocalDef <$> dl) (go r' t)
              where r' = bindPatImpl r (concatMap localVarNamesGen dl)
                    completeLocalDef (LocalFnDefGen v tp eqs) =
                        LocalFnDef (rvrName v) (go r tp) (completeEqn r' <$> eqs)
            UIntLit i -> Term $ IntLit i
            UArray tp v -> Term $ ArrayValue (go r tp) (go r <$> v)

completeEqn :: UnifyResult -> UnifyDefEqn -> TypedDefEqn
completeEqn r (DefEqnGen upl urhs) = DefEqn pl (completeTerm r' urhs)
  where (r',pl) = bindPats r upl


{-
-- | Perform Unification, and add bindings from unify state to context.
-- Returns context and function for translating unifyterms in original context.
withUResult :: TermContext
            -> (UnifyResult -> a)
            -> Unifier a
withUResult ctx fn = state sfn
  where sfn s = (fn (addVarBindings ctx s'), s')
          where s' = unifyCns s

addVarBindings :: TermContext
               -> UnifyState
               -> UnifyResult
addVarBindings tc s = undefined tc s
  where varSubvars :: UVar -> Set UVar
        varSubvars (UPRigid sym) = addUnifyTermVars Set.empty tp
          where err = error $ "Could not find type for " ++ show sym
                tp = fromMaybe err $ rigidType sym us
        varSubvars (UIVar i) = 
          case inaccessibleBinding us i of
            Just t -> addUnifyTermVars Set.empty t
            Nothing -> Set.empty
        vars = usVars us
        edges = [ (v, u)
                      | u <- Set.toList vars
                      , v <- Set.toList (varSubvars u)
                      ]
        allOrdering =
          case topSort vars edges of
            Left zm -> error $ "Found cyclic dependencies: " ++ show zm
            Right o -> o
        ordering = V.fromList [ i | UPRigid i <- allOrdering ]
        pIdxMap :: Map RigidVarRef DeBruijnIndex
        pIdxMap = orderedListMap (V.toList ordering)
        varUnifyTypes :: Vector UnifyTerm
        varUnifyTypes = V.generate (V.length ordering) fn
          where fn idx = tp
                  where Just tp = rigidType (ordering V.! idx) us
        -- Vector of types.  The term is in the context of the term it is bound to.
        varTypes :: Vector Term
        varTypes = V.generate (V.length varUnifyTypes) fn
          where fn idx = completeTerm ur (inaccessibleBinding us) idx
                           0 (varUnifyTypes V.! idx)
        pVarMap = (\i -> (i,varTypes V.! i)) <$> pIdxMap
        -- Inner context
        ctx' = foldl' (uncurry . consLocalVar) tc (V.zip (rvrName <$> ordering) varTypes)
        ur = UResult { urRigidMap = pVarMap
                     }
-}

{-
termUnPat :: (?ctx :: TermContext) => UPat -> UnifyTerm
termUnPat = go
  where go (UPVar sym) = URigidVar sym
        go (UPUnused i) = UnificationVar i
        go (UPatF _ pf) =
          case pf of
            UPTuple pl    -> UTupleValue (go <$> pl)
            UPRecord pm   -> URecordValue (go <$> pm)
            UPCtor sym pl -> UCtorApp c (go <$> pl)
              where Just c = findCon ?ctx sym
            UPIntLit i  -> UIntLit i
-}

indexUnPat :: GlobalContext -> Un.Pat -> Unifier UPat
indexUnPat ctx pat = 
  case pat of
    Un.PVar psym -> UPVar <$> newRigidVar (Just (pos psym)) (val psym)
    Un.PUnused s -> UPUnused <$> newUnifyVarIndex s
    Un.PTuple p pl   -> (UPatF (Just p) . UPTuple) <$> mapM (indexUnPat ctx) pl
    Un.PRecord p fpl -> (UPatF (Just p) . UPRecord . Map.fromList . zip (val <$> fl))
                                   <$> mapM (indexUnPat ctx) pl
      where (fl,pl) = unzip fpl

    Un.PCtor i l ->
      case Map.lookup (val i) (ctxGlobalBindings ctx) of
        Just (CtorIdent c) ->
          (UPatF (Just (pos i)) . UPCtor c) <$> mapM (indexUnPat ctx) l 
        Just _ -> fail $ show (val i) ++ " does not refer to a constructor."
        Nothing -> fail $ "Unknown symbol " ++ show (val i)

{-
declEqs :: TermContext -> [Un.Decl] -> (String -> [DefEqn Pat Term])
declEqs ctx d = \i -> Map.findWithDefault [] i eqMap
  where insertEq m (Un.TermDef psym lhs rhs) = Map.insertWith (++) sym v m
          where sym = val psym
                tp = case findDefType ctx (Un.localIdent sym) of
                       Just tp' -> tp'
                       Nothing -> internalError $ "Could not find " ++ show sym
                (ctx',lhs') = convertLhsPatterns ctx (snd <$> lhs) tp
                v = [DefEqn lhs' (convertTerm ctx' rhs)]
        insertEq m _ = m
        eqMap = foldl' insertEq Map.empty d
-}

addImportNameStrings :: Un.ImportName -> Set String -> Set String
addImportNameStrings im s =
  case im of
    Un.SingleImport pnm -> Set.insert (val pnm) s
    Un.AllImport pnm -> Set.insert (val pnm) s
    Un.SelectiveImport pnm cl -> foldr Set.insert s (val <$> (pnm:cl)) 

-- | Returns set of names identified in a given list of names to import.
importNameStrings :: [Un.ImportName] -> Set String
importNameStrings = foldr addImportNameStrings Set.empty

includeNameInModule :: Maybe Un.ImportConstraint -> String -> Bool
includeNameInModule mic =
  case mic of
    Nothing -> \_ -> True
    Just (Un.SpecificImports iml) -> flip Set.member imset
      where imset = importNameStrings iml
    Just (Un.HidingImports iml) -> flip Set.notMember imset
      where imset = importNameStrings iml

{-
-- | Return a term representing the given local var.
varIndex :: GlobalContext -> Un.Ident -> Maybe UnifyTerm
varIndex tc i = fn <$> Map.lookup i (tcMap tc)
  where fn (Left (lvl,t)) = Term $ LocalVar idx t
          where idx = tcDeBruijnLevel tc - lvl - 1
        fn (Right d) = Term $ GlobalDef d
-}

{-
-- | Returns constructor or data type associated with given identifier.
-- Calls error if attempt to find constructor failed.
findCon :: TermContext -> Un.Ident -> Maybe (Ctor Ident UnifyTerm)
findCon tc i = Map.lookup i (tcDataDecls tc)
-}

type ContextInitializer = State GlobalContext

-- | Create a 
newUnifyDataType :: UnDataType -> ContextInitializer ()
newUnifyDataType dt = modify fn
  where fn :: GlobalContext -> GlobalContext
        fn ctx = ctx'
          where ctxIdent = mkIdent (ctxModuleName ctx)
                insCtor m c = Map.insert (Un.localIdent nm) (CtorIdent sym) m
                  where nm = ctorName c
                        sym = ctxIdent nm
                dnm = dtName dt
                dnmIdent = DataTypeIdent (ctxIdent dnm)
                b1 = foldl' insCtor (ctxGlobalBindings ctx) (dtCtors dt)     
                b2 = Map.insert (Un.localIdent dnm) dnmIdent b1
                ctx' = ctx { ctxGlobalBindings = b2
                           , ctxNewDataTypes = dt : ctxNewDataTypes ctx
                           }

-- | Insert identifiers with given type into global context.
newUnifyDefs :: [Un.PosPair String] -> Un.Term -> ContextInitializer ()
newUnifyDefs idl tp = modify fn
  where newDefs = (\i -> (val i,tp)) <$> idl 
        fn ctx = ctx { ctxGlobalBindings = foldl' ins (ctxGlobalBindings ctx) idl
                     , ctxNewDefTypes = ctxNewDefTypes ctx ++ newDefs
                     }
          where ins m nm = Map.insert (Un.localIdent (val nm)) (DefIdent sym) m
                  where sym = mkIdent (ctxModuleName ctx) (val nm)

newUnifyEqn :: Un.Pos -> String -> [Un.Pat] -> Un.Term  -> ContextInitializer ()
newUnifyEqn _ nm pats rhs = modify fn
  where fn gc = gc { ctxNewEqns = (nm, eqn) :  ctxNewEqns gc }
          where eqn = DefEqnGen pats rhs

{-
importTerm :: Term -> ContextInitializer UnifyTerm
importTerm = go []
  where go :: [RigidVarRef] -> ContextInitializer UnifyTerm 
        go bindings (Term tf) =
          case tf of
            LocalVar i _ -> return (URigidVar (bindings !! i))
            GlobalDef d -> do
              StateT $ \s -> do 
                case Map.lookup (defIdent d) (ctxImports s) of
                  Just r -> return (URigidVar r,s')

importedRigidVar :: [Maybe ModuleName]
                 -> Bool
                 -> Ident
                 -> Term -- ^ Type of imported term
                 -> (Module -> Module) -- ^ Module update function
                 -> ContextInitializer ()
importedRigidVar mnml v sym tp moduleFn = do
  utp <- undefined tp
  let nm = identName sym
      unm | v = Un.mkIdent (head mnml) nm
          | otherwise = Un.mkIdent (Just (identModule sym)) nm
  let fn s = (v, s')
        where idx = nextRigidIndex s
              v = RigidVarRef Nothing unm idx 
              s' = s { usTypeMap = Map.insert v utp (usTypeMap s) 
                     , usVars = Set.insert (UPRigid v) (usVars s)
                     , nextRigidIndex = idx + 1
                     }
  r <- lift $ state fn
  let ctxFn ctx = ctx { ctxVarBindings = m'
                      , gcModule = moduleFn (gcModule ctx)
                      }
        where m = ctxVarBindings ctx
              ins m mnm = Map.insert (Un.mkIdent mnm nm) (Left d) m
              m' | v = foldl' ins m mnml
                 | otherwise = m
  modify ctxFn
-}

addDataType :: [Maybe ModuleName] -- ^ Untyped module names to add symbols to.
            -> TypedDataType
               -- | Indicates if datatype itself should be visibile in untyped context.
            -> Bool
               -- | List of ctors to make visible in untyped context.
            -> [TypedCtor]
            -> ContextInitializer ()
addDataType _mnml dt _ _ = do
  let ctxFn gc = gc { gcModule = insDataType (gcModule gc) dt
                    , ctxGlobalBindings = internalError "addDataType undefined"
                    }
  modify ctxFn

addDef :: [Maybe ModuleName]
       -> Bool -- ^ Indicates if definition should be visible to untyped context.
       -> Def Term
       -> ContextInitializer ()
addDef mnml v def = do
  let nm = identName (defIdent def)
  let ctxFn ctx = ctx { ctxGlobalBindings = m'
                      , gcModule = insDef (gcModule ctx) def
                      }
        where m = ctxGlobalBindings ctx
              ins mnm = Map.insert (Un.mkIdent mnm nm) (DefIdent (defIdent def))
              m' | v = foldl' (flip ins) m mnml
                 | otherwise = m
  modify ctxFn

{-
completeCtorType :: UnifyResult -> UnifyCtorType -> TypedCtorType
completeCtorType = go
  where go r (CtorResult t) = CtorResult (completeTerm r t)
        go r (CtorArg p tp rhs) = CtorArg p' (completeTerm r tp) (go r' rhs)
          where (r',p') = bindPat r p
-}

completeCtor :: UnifyResult -> UnifyCtor -> TypedCtor
completeCtor r (Ctor nm tp) = Ctor nm (completeTerm r tp)

completeDataType :: UnifyResult 
                 -> UnifyDataType
                 -> TypedDataType
completeDataType r dt =
  DataType { dtName = dtName dt
           , dtType = completeTerm r (dtType dt)
           , dtCtors = completeCtor r <$> dtCtors dt
           }

convertDataType :: GlobalContext -> UnDataType -> Unifier UnifyDataType
convertDataType ctx dt = do
  let mnm = moduleName (gcModule ctx)
  let tc = emptyTermContext ctx
  tp <- convertTerm tc (dtType dt)
  ctors <- mapM (convertCtor ctx) (dtCtors dt)
  return DataType { dtName = mkIdent mnm (dtName dt)
                  , dtType = tp
                  , dtCtors = ctors
                  }

convertCtor :: GlobalContext -> UnCtor -> Unifier UnifyCtor
convertCtor ctx c = do
  let mnm = moduleName (gcModule ctx)
  let tc = emptyTermContext ctx
  tp <- convertTerm tc (ctorType c)
  return Ctor { ctorName = mkIdent mnm (ctorName c)
              , ctorType = tp
              }

{-
convertCtorType :: GlobalContext -> NormalizedCtorType -> Unifier UnifyCtorType
convertCtorType = go . emptyTermContext
  where go tc (CtorResult t) = CtorResult <$> convertTerm tc t
        go tc (CtorArg upat utp ur) = do
          tp <- convertTerm tc utp
          (tc',[pat]) <- consPatVars tc [upat] tp
          r <- go tc' ur
          return $ CtorArg pat tp r
-}

unifierModule :: Module
              -> [UnifyDataType]
              -> [(String, UnifyTerm)]
              -> Map String [UnifyDefEqn]
              -> Unifier Module
unifierModule ctxm udtl defs eqnMap = do
  let mnm = moduleName ctxm
  s <- get
  case unifyEqs s of
    eq:eqs -> do
      put s { unifyEqs = eqs }
      case eq of
        UnifyEqTypes x y -> unifyTypes x y
        UnifyEqValues x y tp -> unifyTerms x y tp
        UnifyPatHasType p tp -> hasType p tp
      unifierModule ctxm udtl defs eqnMap
    [] -> do
      let completeDef :: String -> UnifyTerm -> Def Term
          completeDef nm tp =
            Def { defIdent = mkIdent mnm nm
                , defType = completeTerm r tp
                , defEqs = completeEqn r <$> eqs
                }
            where eqs = fromMaybe [] $ Map.lookup nm eqnMap
          m = flip (foldl' insDef) (map (uncurry completeDef) defs)
            $ flip (foldl' insDataType) (completeDataType r <$> udtl)
            $ ctxm
          varSubvars :: UVar -> Set UVar
          varSubvars (UPRigid sym) = addUnifyTermVars Set.empty tp
            where err = "Could not find type for " ++ show sym
                  tp = fromMaybe (internalError err) $ Map.lookup sym (usTypeMap s)
          varSubvars (UIVar i) = 
            case Map.lookup i (usVarBindings s) of
              Just t -> addUnifyTermVars Set.empty (varBindingTerm t)
              Nothing -> Set.empty
          vars = usVars s
          edges = [ (v, u)
                  | u <- Set.toList vars
                  , v <- Set.toList (varSubvars u)
                  ]
          allOrdering =
            case topSort vars edges of
              Left zm -> error $ "Found cyclic dependencies: " ++ show zm
              Right o -> o
          ordering :: Vector RigidVarRef
          ordering = V.fromList [ i | UPRigid i <- allOrdering ]
          pIdxMap :: Map RigidVarRef DeBruijnIndex
          pIdxMap = orderedListMap (V.toList ordering)
          varUnifyTypes :: Vector UnifyTerm
          varUnifyTypes = fn <$> ordering
            where fn v = tp
                    where Just tp = Map.lookup v (usTypeMap s)
--          varTypes :: Vector Term
--          varTypes = V.generate (V.length ordering) fn
--            where fn idx = completeTerm r (varUnifyTypes V.! idx)
          getRigidVarType i = (i,varUnifyTypes V.! i)
          r = UResult { urRigidIndexMap = getRigidVarType <$> pIdxMap
                      , urVarBindings = varBindingTerm <$> usVarBindings s
                      , urModule = m
                      , urLevel = 0
                      , urRigidTypeMap = Map.empty
                      }
      return m

runUnification :: ModuleName -> ContextInitializer () -> Module
runUnification nm initialization = flip evalState emptyUnifyState $ do
  let gc0 = GlobalContext {
                gcModule = emptyModule nm
              , ctxGlobalBindings = Map.empty
              , ctxNewDataTypes = []
              , ctxNewDefTypes = []
              , ctxNewEqns = []
              }
  let ctx = execState initialization gc0
  modify $ \s -> s { usGlobalContext = Just ctx }
  do let ctors = concatMap dtCtors (ctxNewDataTypes ctx)
     let newCtorBindings c = (mkIdent nm (ctorName c), Left (ctorType c))
     let updateCtors s = s { usCtorTypes = Map.fromList (newCtorBindings <$> ctors) }
     modify updateCtors
  udtl <- mapM (convertDataType ctx) (ctxNewDataTypes ctx)
  let (defNames,untps) = unzip (ctxNewDefTypes ctx)
  let tc = emptyTermContext ctx
  defTypes <- mapM (convertTerm tc) untps
  let defTypeMap = Map.fromList (defNames `zip` defTypes)

  eqnMap <- fmap multiMap $ 
    forM (ctxNewEqns ctx) $ \(sym,uneqn) -> do
      let Just tp = Map.lookup sym defTypeMap
      eqn <- convertEqn tc tp uneqn
      return (sym, eqn)
  unifierModule (gcModule ctx) udtl (defNames `zip` defTypes) eqnMap


-- | Creates a module from a list of untyped declarations.
unsafeMkModule :: [Module] -- ^ List of modules loaded already.
               -> Un.Module
               -> Module
unsafeMkModule ml (Un.Module (PosPair _ nm) iml d) = r
  where moduleMap = projMap moduleName ml
        r = runUnification nm $ do
              mapM_ insertImport iml
              mapM_ insertDef d
        insertImport :: Un.Import -> ContextInitializer ()
        insertImport (Un.Import q pm mAsName mcns) = mapM_ insDecl (moduleDecls m) 
          where Just m = Map.lookup (val pm) moduleMap
                qnm = maybe (moduleName m)
                            (\s -> Un.mkModuleName [s])
                            (val <$> mAsName) 
                -- Return true if this identifer should be added to module.
                identPred :: Ident -> Bool
                identPred = nmPred . identName
                  where nmPred = includeNameInModule mcns
                mnml | q = [Just qnm]
                     | otherwise = [Nothing, Just qnm]
                -- Insert individual declaration from module.
                insDecl :: ModuleDecl -> ContextInitializer ()
                insDecl md = 
                  case md of
                    TypeDecl dt -> addDataType mnml dt dtVis ctors
                      where dtVis = identPred (dtName dt)
                            ctors = filter (identPred . ctorName) (dtCtors dt)
                    DefDecl def -> addDef mnml defVis def
                      where defVis = identPred (defIdent def) 
        insertDef :: Un.Decl -> ContextInitializer ()
        insertDef (Un.TypeDecl idl untp) = newUnifyDefs idl untp
        insertDef (Un.DataDecl psym untp ucl) = do
          let ctorDef (Un.Ctor pnm ctorTp) = Ctor (val pnm) ctorTp
          newUnifyDataType DataType { dtName = val psym
                                    , dtType = untp
                                    , dtCtors = ctorDef <$> ucl
                                    }
        insertDef (Un.TermDef psym lhs rhs) =
          newUnifyEqn (Un.pos psym) (val psym) (snd <$> lhs) rhs