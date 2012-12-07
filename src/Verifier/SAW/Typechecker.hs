{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Verifier.SAW.Typechecker
  ( unsafeMkModule
  ) where

import Control.Applicative ((<$>))
import Control.Exception (assert)
import Data.Foldable
import Data.List (mapAccumL)

import Data.Map (Map)
import qualified Data.Map as Map

import Data.Maybe (fromMaybe)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Vector (Vector)
import qualified Data.Vector as V

import Prelude hiding (concatMap, foldr)

import Verifier.SAW.UntypedAST ( PosPair(..))
import Verifier.SAW.TypedAST
import qualified Verifier.SAW.UntypedAST as Un

internalError :: String -> a
internalError msg = error $ "internal: " ++ msg

mapSnd :: (b -> c) -> (a,b) -> (a,c)
mapSnd f (a,b) = (a,f b) 

mkEdgeMap :: Ord a => [(a,a)] -> Map a [a]
mkEdgeMap = foldl' fn Map.empty
  where fn m (x,y) = Map.insertWith (++) x [y] m

-- | Given a project function returning a key and a list of values, return a map
-- from the keys to values.
projMap :: Ord k => (a -> k) -> [a] -> Map k a
projMap f l = Map.fromList [ (f e,e) | e <- l ] 

flipPair :: (a,b) -> (b,a)
flipPair (x,y) = (y,x)

orderedListMap :: Ord a => [a] -> Map a Int
orderedListMap l = Map.fromList (l `zip` [0..])

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

type DeBruijnLevel = DeBruijnIndex

data TermContext = TermContext {
         tcDeBruijnLevel :: !DeBruijnLevel
       , tcMap :: !(Map Un.Ident (Either (DeBruijnLevel,Term) (Def Term)))
       , tcDataDecls :: !(Map Un.Ident (Either (Ctor Term) (DataType Term)))
       , tcEqs :: !(Map String [DefEqn Pat Term])
       , tcModule  :: Module
       }

instance Show TermContext where
  show tc = "tcDeBruijnLevel: " ++ show (tcDeBruijnLevel tc) ++ "\n"
         ++ "tcMap:\n" ++ ppm ppVar (tcMap tc)
         ++ "tcDataDecls:\n" ++ ppm ppData (tcDataDecls tc)
   where ppe :: (a -> String) -> (Un.Ident,a) -> String
         ppe fn (i,v) = "  " ++ show i ++ " = " ++ fn v ++ "\n"
         ppm :: (a -> String) -> Map Un.Ident a -> String
         ppm fn m = concatMap (ppe fn) (Map.toList m) 
         ppVar (Left (l,_))  = "Local " ++ show l
         ppVar (Right d) = "Global " ++ show (defIdent d) 
         ppData (Left c) = "Ctor " ++ show (ctorIdent c)
         ppData (Right dt) = "ADT " ++ show (dtIdent dt)

emptyContext :: ModuleName -> TermContext
emptyContext nm =
  TermContext { tcDeBruijnLevel = 0
              , tcMap = Map.empty
              , tcDataDecls = Map.empty
              , tcEqs = Map.empty
              , tcModule = emptyModule nm
              }

tcModuleName :: TermContext -> ModuleName
tcModuleName = moduleName . tcModule

addDataType :: [Maybe ModuleName] -- ^ Untyped module names to add symbols to.
            -> TermContext
            -> DataType Term
            -> Bool -- ^ Indicates if datatype itself should be visibile in untyped context.
            -> [Ctor Term] -- ^ List of ctors to make visibile in untyped context.
            -> TermContext
addDataType mnml ctx dt visible vCtors =
    ctx { tcDataDecls = foldl' (flip insDT) (tcDataDecls ctx) mnml  
        , tcModule = insDataType (tcModule ctx) dt
        }
  where insCtor mnm dd c = Map.insert sym (Left c) dd
          where sym = Un.mkIdent mnm (identName (ctorIdent c))
        insDT mnm dd = foldl' (insCtor mnm) dd1 vCtors
          where sym = Un.mkIdent mnm (identName (dtIdent dt))
                dd1 | visible = Map.insert sym (Right dt) dd
                    | otherwise = dd      

addDef :: [Maybe ModuleName]
       -> Bool -- ^ Indicates if definition should be visible to untyped context.
       -> TermContext
       -> Def Term
       -> TermContext
addDef mnml visible ctx def = ctx { tcMap = dd'
                                  , tcModule = insDef (tcModule ctx) def
                                  }
  where nm = identName (defIdent def)
        insSym dd mnm = Map.insert sym (Right def) dd
          where sym = Un.mkIdent mnm nm
        dd' | visible = foldl' insSym (tcMap ctx) mnml
            | otherwise = tcMap ctx

addEqn :: TermContext -> String -> DefEqn Pat Term -> TermContext
addEqn ctx sym eqn = ctx { tcEqs = Map.insertWith (++) sym [eqn] (tcEqs ctx) }

findEqns :: TermContext -> String -> [DefEqn Pat Term]
findEqns ctx i = Map.findWithDefault [] i (tcEqs ctx)

-- | Add a new local var to the context.
consLocalVar :: TermContext -> String -> Term -> TermContext
consLocalVar ctx nm tp = ctx { tcDeBruijnLevel = lvl + 1
                             , tcMap = Map.insert (Un.localIdent nm) (Left (lvl,tp)) (tcMap ctx)
                             }
  where lvl = tcDeBruijnLevel ctx

contextModule :: TermContext -> Module
contextModule = tcModule

-- | Insert local definitions the terms belong to the given context.
consLocalVarBlock :: TermContext -> [(String,Term)] -> TermContext
consLocalVarBlock = go 0
  where go _ tc [] = tc
        go i tc ((sym,tp):r) = go (i+1) tc' r
          where tc' = consLocalVar tc sym (incVars 0 i tp)

-- | Returns constructor or data type associated with given identifier.
-- Calls error if attempt to find constructor failed.
findCon :: TermContext -> Un.Ident -> Maybe (Either (Ctor Term) (DataType Term))
findCon tc i = Map.lookup i (tcDataDecls tc)

-- TODO: See if we can replace this was "typeOf <$> varIndex ctx sym"
findDefType :: TermContext -> Un.Ident -> Maybe Term
findDefType tc i = getType <$> Map.lookup i (tcMap tc)
  where getType (Left (lvl,tp)) = incVars 0 idx tp
          where idx = tcDeBruijnLevel tc - lvl - 1         
        getType (Right d) = defType d

-- | Return a term representing the given local var.
varIndex :: TermContext -> Un.Ident -> Maybe Term
varIndex tc i = fn <$> Map.lookup i (tcMap tc)
  where fn (Left (lvl,t)) = Term $ LocalVar idx t
          where idx = tcDeBruijnLevel tc - lvl - 1
        fn (Right d) = Term $ GlobalDef d

addUnPatIdents :: Set String -> Un.Pat a -> Set String
addUnPatIdents s pat =
  case pat of
    Un.PVar (PosPair _ sym) -> Set.insert sym s
    Un.PTuple _ pl -> foldl' addUnPatIdents s pl
    Un.PRecord _ fpl -> foldl' addUnPatIdents s (snd <$> fpl)
    Un.PCtor _ pl -> foldl' addUnPatIdents s pl
    _ -> s

data VarIndex = VarIndex Int (PosPair String)
  deriving (Eq,Ord,Show)


-- | Replace each inaccessible term with a unique index.
indexUnPat :: UnifyState -> Un.Pat String -> (UnifyState,Un.Pat VarIndex)
indexUnPat us pat =
  case pat of
    Un.PUnused s -> (us', Un.PUnused (fmap (const i) s))
      where (i,us') = newUnifyVarIndex us s
    Un.PVar psym -> (us,Un.PVar psym)
    Un.PTuple p pl   -> mapSnd (Un.PTuple p)   $ mapAccumL indexUnPat us pl
    Un.PRecord p fpl -> mapSnd (Un.PRecord p . zip fl) $ mapAccumL indexUnPat us pl
      where (fl,pl) = unzip fpl 
    Un.PCtor psym pl -> mapSnd (Un.PCtor psym) $ mapAccumL indexUnPat us pl
    Un.PIntLit p j -> (us,Un.PIntLit p j)

data UVar = UPVar String | UIVar VarIndex
  deriving (Eq, Ord, Show)

type UPat = Pat UnifyTerm

data UnifyTerm
  = URigidVar String -- ^ Rigid variable that cannot be instantiated.
  | ULocalVar DeBruijnIndex Term  -- ^ Variable bound by context with type.
  | UGlobal (Def Term)
  
  | ULambda UPat UnifyTerm UnifyTerm
  | UApp UnifyTerm UnifyTerm
  | UPi UPat UnifyTerm UnifyTerm

  | UTupleValue [UnifyTerm]
  | UTupleType [UnifyTerm]

  | URecordValue (Map FieldName UnifyTerm)
  | URecordSelector UnifyTerm FieldName
  | URecordType (Map FieldName UnifyTerm)

  | UCtorApp (Ctor Term) [UnifyTerm]
  | UDataType (DataType Term) [UnifyTerm]

  | USort Sort
 
  | ULet [Def Term] UnifyTerm
  | UIntLit Integer
  | UArray UnifyTerm (Vector UnifyTerm)

  | UInaccessible VarIndex
  deriving (Eq, Show)

addUnifyTermVars :: Set UVar -> UnifyTerm -> Set UVar
addUnifyTermVars = go
  where go s (URigidVar sym) = Set.insert (UPVar sym) s
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
        go s (UInaccessible i) = Set.insert (UIVar i) s
        go s _ = s

data UnifyState = US { usTypeMap :: Map String UnifyTerm
                     , usVarTermMap :: Map VarIndex UnifyTerm
                     , termEqs :: [(UnifyTerm,UnifyTerm)]
                     , usVars :: Set UVar
                     , nextVarIndex :: Int
                     }

emptyUnifyState :: Set String -- ^ Identifiers bound in patterns.
                -> UnifyState
emptyUnifyState vs =
    US { usTypeMap = Map.empty
       , usVarTermMap = Map.empty
       , termEqs = []
       , usVars = Set.map UPVar vs
       , nextVarIndex = 0
       }

newUnifyVarIndex :: UnifyState -> PosPair String -> (VarIndex,UnifyState)
newUnifyVarIndex us nm = (v, us')
  where idx = nextVarIndex us
        v = VarIndex idx nm
        us' = us { usVars = Set.insert (UIVar v) (usVars us) 
                 , nextVarIndex = idx + 1
                 }


identType :: String -> UnifyState -> Maybe UnifyTerm
identType i us = Map.lookup i (usTypeMap us)

inaccessibleBinding :: VarIndex -> UnifyState -> Maybe UnifyTerm
inaccessibleBinding i us = Map.lookup i (usVarTermMap us)

addTermEq :: UnifyTerm -> UnifyTerm -> UnifyState -> UnifyState
addTermEq x y s  = s { termEqs = (x,y):termEqs s }

addTermEqs :: [(UnifyTerm, UnifyTerm)] -> UnifyState -> UnifyState
addTermEqs eqs s = foldr (uncurry addTermEq) s eqs

unifyCns :: UnifyState -> UnifyState
unifyCns s =
  case termEqs s of
    [] -> s
    (x,y):eqs -> unifyCns $ unifyTerms x y (s { termEqs = eqs })

bindPatVarType :: String -> UnifyTerm -> UnifyState -> UnifyState
bindPatVarType sym tp s = s { usTypeMap = Map.insert sym tp (usTypeMap s) }

bindVar :: VarIndex -> UnifyTerm -> UnifyState -> UnifyState
bindVar i t s =
  case Map.lookup i m of
    Nothing -> s { usVarTermMap = Map.insert i t m }
    Just u -> assert (t == u) s
 where m = usVarTermMap s

unifyTerms :: UnifyTerm -> UnifyTerm -> UnifyState -> UnifyState
unifyTerms (ULambda _ lx ly) (ULambda _ rx ry) s =
  addTermEqs [(lx,rx), (ly,ry)] s
unifyTerms (UApp lx ly) (UApp rx ry) s =
  addTermEqs [(lx,rx), (ly,ry)] s
unifyTerms (UPi _ lx ly) (UPi _ rx ry) s =
  addTermEqs [(lx, rx), (ly, ry)] s

unifyTerms (UTupleValue l) (UTupleValue r) s = addTermEqs (zip l r) s
unifyTerms (UTupleType l) (UTupleType r) s = addTermEqs (zip l r) s

unifyTerms (URecordValue l) (URecordValue r) s =
  assert (Map.keys l == Map.keys r) $
    addTermEqs (Map.elems l `zip` Map.elems r) s
unifyTerms (URecordSelector l lf) (URecordSelector r rf) s =
  assert (lf == rf) $ unifyTerms l r s
unifyTerms (URecordType l) (URecordType r) s =
  assert (Map.keys l == Map.keys r) $
    addTermEqs (Map.elems l `zip` Map.elems r) s

unifyTerms (UCtorApp lc l) (UCtorApp rc r) s =
  assert (lc == rc) $
    addTermEqs  (l `zip` r) s
unifyTerms (UDataType ld l) (UDataType rd r) s =
  assert (ld == rd) $
    addTermEqs (l `zip` r) s
unifyTerms (UArray _ltp l) (UArray _rtp r) s =
  addTermEqs (V.toList (l `V.zip` r)) s
unifyTerms (UInaccessible i) y s = bindVar i y s
unifyTerms x (UInaccessible j) s = bindVar j x s

unifyTerms x y s | x == y = s
                 | otherwise = internalError $ "unifyTerms failed " ++ show (x,y)

-- | Create a set of constraints for matching a list of patterns against a given pi type.
instPiType :: (?ctx :: TermContext)
              -- | Continuation to generate final constraints
           => (UnifyTerm -> UnifyState -> UnifyState)
           -> [Un.Pat VarIndex] -- ^ Patterns to match
           -> Term -- ^ Expected pi type 
           -> UnifyState
           -> UnifyState
instPiType cont = \pl tp s -> go s pl V.empty tp
  where go s [] ctx ltp = cont (instWithUnPat ctx ltp) s
        go s (p:pl) pctx ltp =
          case ltp of
            Term (Pi _ lhs rhs) -> go s' pl (V.cons (termUnPat p) pctx) rhs
                where s' = hasType s (p, instWithUnPat pctx lhs)
            _ -> error "internal: Too many arguments to pi type"

preludeModuleName :: ModuleName
preludeModuleName = Un.mkModuleName ["Prelude"]

preludeIdent :: String -> Ident
preludeIdent nm = mkIdent preludeModuleName nm

hasType :: (?ctx :: TermContext)
        => UnifyState
        -> (Un.Pat VarIndex, UnifyTerm)
        -> UnifyState

hasType s (Un.PVar (PosPair _ i), tp) = bindPatVarType i tp s
hasType s (Un.PTuple _ pl, tp) =
  case tp of
    UTupleType tpl -> foldl' hasType s (zip pl tpl)
    _ -> internalError "Could not match tuple pattern"
hasType s (Un.PRecord _ pm, tp) =
  case tp of
    URecordType tpm -> foldl' hasType s elts
      where elts = Map.elems (Map.fromList pm) `zip` Map.elems tpm
    _ -> internalError "Could not match record pattern"
hasType s (Un.PCtor sym pl, tp) = instPiType cont pl (ctorType c) s
 where Just (Left c) = findCon ?ctx (val sym)
       cont ltp = addTermEq ltp tp
hasType s (Un.PUnused{}, _) = s
hasType s (Un.PIntLit{}, tp) =
  case tp of
    UDataType dt _ | dtIdent dt == preludeIdent "Integer" -> s
    _ -> internalError "Could not match integer literal"

-- | Instantiate local variables with patterns.
instWithUnPat :: V.Vector UnifyTerm -> Term -> UnifyTerm
instWithUnPat pv = go 0
  where plen = V.length pv
        go bnd (Term tf) = 
          case tf of 
            LocalVar i tp
              | i < bnd    -> ULocalVar i tp
              | i - bnd < plen -> pv V.! (i-bnd)
              | otherwise -> ULocalVar (i-bnd) tp
            GlobalDef d -> UGlobal d
            Lambda sym lhs rhs -> ULambda (go bnd <$> sym) l (go (bnd+cnt) rhs)
              where l = go bnd lhs
                    cnt = patBoundVarCount sym
            App x y -> UApp (go bnd x) (go bnd y)
            Pi sym lhs rhs -> UPi (go bnd <$> sym) l (go (bnd+cnt) rhs)
              where l = go bnd lhs
                    cnt = patBoundVarCount sym
            TupleValue l -> UTupleValue (go bnd <$> l)
            TupleType l -> UTupleType (go bnd <$> l)
            RecordValue m -> URecordValue (go bnd <$> m)
            RecordSelector x f -> URecordSelector (go bnd x) f
            RecordType m -> URecordType (go bnd <$> m)
            CtorValue c l -> UCtorApp c (go bnd <$> l)
            CtorType dt l -> UDataType dt (go bnd <$> l)
            Sort s -> USort s
            Let dl t -> ULet dl (go (bnd + length dl) t)
            IntLit i -> UIntLit i
            ArrayValue tp v -> UArray (go bnd tp) (go bnd <$> v)

-- | Perform Unification, and add bindings from unify state to context.
-- Returns context and function for translating unifyterms in original context.
addVarBindings :: UnifyState -> TermContext -> ( Map String (DeBruijnIndex,Term)
                                               , TermContext)
addVarBindings us0 tc = (pVarMap, ctx')
  where us = unifyCns us0
        completeTerm :: Int -- Ident of this term in ordering.
                     -> DeBruijnIndex
                     -> UnifyTerm
                     -> Term
        completeTerm idx j ut =
          case ut of
            URigidVar sym -> assert (prevIdx < idx) $
               Term $ LocalVar (j + idx')
                               (incVars 0 idx' (varTypes V.! prevIdx))
              where Just prevIdx = Map.lookup sym pIdxMap
                    idx' = idx - prevIdx - 1
            ULocalVar i tp -> Term $ LocalVar i tp
            UGlobal d      -> Term $ GlobalDef d
            ULambda s l r  -> Term $ Lambda (go j <$> s)
                                            (go j l)
                                            (go (j+patBoundVarCount s) r)
            UApp x y  -> Term $ App (go j x) (go j y)
            UPi s l r -> Term $ Pi (go j <$> s)
                                   (go j l)
                                   (go (j+patBoundVarCount s) r)
            UTupleValue l -> Term $ TupleValue (go j <$> l)
            UTupleType l  -> Term $ TupleType  (go j <$> l)
            URecordValue m      -> Term $ RecordValue (go j <$> m)
            URecordSelector x f -> Term $ RecordSelector (go j x) f
            URecordType m       -> Term $ RecordType (go j <$> m)
            UCtorApp c l   -> Term $ CtorValue c (go j <$> l)
            UDataType dt l -> Term $ CtorType dt (go j <$> l)
            USort s   -> Term $ Sort s
            ULet dl t -> Term $ Let dl (go (j + length dl) t)
            UIntLit i -> Term $ IntLit i
            UArray tp v -> Term $ ArrayValue (go j tp) (go j <$> v)
            UInaccessible i -> go j t
              where Just t = inaccessibleBinding i us
         where go = completeTerm idx
        varSubvars :: UVar -> Set UVar
        varSubvars (UPVar sym) = addUnifyTermVars Set.empty tp
          where err = error $ "Could not find type for " ++ show sym
                tp = fromMaybe err $ identType sym us
        varSubvars (UIVar i) = 
          case inaccessibleBinding i us of
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
        ordering = V.fromList [ i | UPVar i <- allOrdering ]
        pIdxMap :: Map String DeBruijnIndex
        pIdxMap = orderedListMap (V.toList ordering)
        -- Vector of types.  The term is in the context of the term it is bound to.
        varTypes :: Vector Term
        varTypes = V.generate (V.length ordering) fn
          where fn idx = completeTerm idx 0 tp
                  where Just tp = identType (ordering V.! idx) us
        pVarMap :: Map String (DeBruijnIndex,Term)
        pVarMap = (\i -> (i,varTypes V.! i)) <$> pIdxMap
        -- Inner context
        ctx' = foldl' (uncurry . consLocalVar) tc (V.zip ordering varTypes)

termUnPat :: (?ctx :: TermContext) => Un.Pat VarIndex -> UnifyTerm
termUnPat = go
  where go (Un.PVar (PosPair _ sym)) = URigidVar sym
        go (Un.PUnused i) = UInaccessible (val i)
        go (Un.PTuple _ pl) = UTupleValue (go <$> pl)
        go (Un.PRecord _ pm) = URecordValue (Map.fromList (fn <$> pm))
           where fn (pf,p) = (val pf, go p)
        go (Un.PCtor sym pl) = UCtorApp c (go <$> pl)
          where Just (Left c) = findCon ?ctx (val sym)
        go (Un.PIntLit _ i) = UIntLit i

-- | Convert term with context already extended.
                -- | Maps strings to associated constructor
convertUnPat :: (Un.Ident -> Ctor Term)
                -- | Maps bound variables to their type.
             -> (String -> (DeBruijnIndex,Term))
             -> Un.Pat VarIndex
             -> Pat Term
convertUnPat ctorFn typeFn = go
  where go :: Un.Pat VarIndex -> Pat Term
        go (Un.PVar (PosPair _ sym)) = uncurry (PVar sym) (typeFn sym)
        go (Un.PUnused _) = PUnused
        go (Un.PCtor i l) = PCtor (ctorFn (val i)) (go <$> l)
        go (Un.PTuple _ l) = PTuple (go <$> l)
        go (Un.PRecord _ l) = PRecord (Map.fromList (fn <$> l))
          where fn (i,q) = (val i, go q)
        go (Un.PIntLit _ i) = PIntLit i

-- | Insert vars bound by patterns into context; returning new context and typechecked patterns.
convertLhsPatterns :: TermContext
                   -> [Un.Pat String]
                   -> Term -- ^ Lamda type.
                   -> (TermContext, [Pat Term])
convertLhsPatterns ctx pl tp = (ctx', convertUnPat ctorFn typeFn <$> pl')
 where s0 = emptyUnifyState vs
       (si,pl') = mapAccumL indexUnPat s0 pl
       vs = foldl' addUnPatIdents Set.empty pl'
       s = let ?ctx = ctx in instPiType (\_ -> id) pl' tp si
       (bvm, ctx') = addVarBindings s ctx
       ctorFn sym = c
         where Just (Left c) = findCon ctx sym
       typeFn nm = r
           where Just r = Map.lookup nm bvm

consPatVars :: TermContext -> Un.Pat String -> Term -> (TermContext, Pat Term)
consPatVars ctx p tp = (ctx', convertUnPat ctorFn typeFn p')
  where s0 = emptyUnifyState vs
        (si,p') = indexUnPat s0 p
        vs = addUnPatIdents Set.empty p
        s = let ?ctx = ctx in hasType si (p', instWithUnPat V.empty tp)
        (bvm,ctx') = addVarBindings s ctx
        ctorFn sym = c
          where Just (Left c) = findCon ctx sym
        typeFn nm = r
          where Just r = Map.lookup nm bvm


convertTerm :: TermContext -> Un.Term -> Term
convertTerm ctx (Un.asApp -> (Un.Con i, uargs)) = Term (fn args)
 where fn = case findCon ctx (val i) of
              Just (Left c)   -> CtorValue c
              Just (Right dt) -> CtorType dt
              Nothing -> error $ "Failed to find constructor for " ++ show i ++ "."
       args = convertTerm ctx <$> uargs
convertTerm ctx uut =
  case uut of
    Un.Var i -> fromMaybe (error err) $ varIndex ctx (val i)
      where err = "Variable " ++ show i ++ " unbound in current context."
    Un.Unused{} -> internalError "Pattern syntax when term expected"
    Un.Con{} -> internalError "Unexpected constructor"
    Un.Sort _ s -> Term (Sort s)
    Un.Lambda _ args f -> procArgs ctx args
      where procPat lctx _ l [] = procArgs lctx l
            procPat lctx t l (pat:l2) = Term (Lambda i t r)
              where (lctx',i) = consPatVars lctx pat t
                    r = procPat lctx' t l l2
            procArgs lctx [] = convertTerm lctx f 
            procArgs lctx ((_,patl,ut):l) = procPat lctx t l patl
              where t = convertTerm lctx ut
    Un.App f _ t -> Term $ App (convertTerm ctx f) (convertTerm ctx t)
    Un.Pi _ idl ut _ f -> procId ctx idl $! convertTerm ctx ut
      where procId lctx [] _ = convertTerm lctx f
            procId lctx (pat:l) !t = Term (Pi i t r)
              where (lctx',i) = consPatVars lctx pat t
                    r = seq lctx' $ procId lctx' l (incVars 0 1 t)
    Un.TupleValue _ tl -> Term $ TupleValue (convertTerm ctx <$> tl)
    Un.TupleType _ tl -> Term $ TupleType (convertTerm ctx <$> tl)
    Un.RecordValue _ fl -> Term $ RecordValue (Map.fromList (fieldFn <$> fl))
      where fieldFn (pf,t) = (val pf, convertTerm ctx t)
    Un.RecordSelector t i -> Term $ RecordSelector (convertTerm ctx t) (val i)
    Un.RecordType _ fl -> Term $ RecordType (Map.fromList (fieldFn <$> fl))
      where fieldFn (pf,t) = (val pf, convertTerm ctx t)
    Un.TypeConstraint t _ _ -> convertTerm ctx t
    Un.Paren _ t -> convertTerm ctx t
    Un.LetTerm _ udl ut -> Term $ Let (mkDef <$> dl) t
      where ctx' = consLocalVarBlock ctx dl
            t = convertTerm ctx' ut
            lookupEqs = declEqs ctx' udl
            mkDef (i,tp) = Def { defIdent = mkIdent (tcModuleName ctx) i
                               , defType = tp
                               , defEqs = lookupEqs i
                               }
            convertDecl (Un.TypeDecl idl utp) = (\i -> (val i,tp)) <$> idl 
              where tp = convertTerm ctx utp
            convertDecl Un.TermDef{} = []
            convertDecl Un.ImportDecl{} = error "Unexpected import in let binding"
            convertDecl Un.DataDecl{} = error "Unexpected data declaration in let binding"
            dl = concatMap convertDecl udl
    Un.IntLit _ i -> Term $ IntLit i
    Un.BadTerm p -> error $ "Encountered bad term from position " ++ show p

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

-- | Creates a module from a list of untyped declarations.
unsafeMkModule :: [Module] -- ^ List of modules loaded already.
               -> Un.Module
               -> Module
unsafeMkModule ml (Un.Module (PosPair _ nm) d) = contextModule gloCtx
  where moduleMap = projMap moduleName ml
        insertDef ctx (Un.ImportDecl q pm mAsName mcns) = insDecls ctx
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
                -- Insert declarations for imported module with a possible prefix.
                insDecls :: TermContext -> TermContext
                insDecls lctx = foldl' insDecl lctx (moduleDecls m)
                -- Insert individual declaration from module.
                insDecl :: TermContext -> ModuleDecl -> TermContext
                insDecl lctx md = 
                  case md of
                    TypeDecl dt -> addDataType mnml lctx dt dtVis ctors
                      where dtVis = identPred (dtIdent dt)
                            ctors = filter (identPred . ctorIdent) (dtCtors dt)
                    DefDecl def -> addDef mnml defVis lctx def
                      where defVis = identPred (defIdent def) 
        insertDef ctx (Un.TypeDecl idl untp) = foldl' (addDef [Nothing] True) ctx (idDef <$> idl)
          where tp = convertTerm gloCtx untp
                idDef i = Def { defIdent = mkIdent nm (val i)
                              , defType = tp
                              , defEqs = findEqns gloCtx (val i)
                              }
        insertDef ctx (Un.DataDecl psym untp cl) = addDataType [Nothing] ctx dt True ctors
          where ctors = ctorDef <$> cl
                dt = DataType { dtIdent = mkIdent nm (val psym)
                              , dtType = convertTerm gloCtx untp
                              , dtCtors = ctors
                              }
                ctorDef (Un.Ctor ctorId ctorTp) =
                      Ctor { ctorIdent = mkIdent nm (val ctorId)
                           , ctorType = convertTerm gloCtx ctorTp
                           }
        insertDef ctx (Un.TermDef psym lhs rhs) = addEqn ctx sym eqn
          where sym = val psym
                tp = case findDefType ctx (Un.localIdent sym) of
                       Just tp' -> tp'
                       Nothing -> internalError $ "Could not find " ++ show sym
                (ctx',lhs') = convertLhsPatterns ctx (snd <$> lhs) tp
                eqn = DefEqn lhs' (convertTerm ctx' rhs)
        gloCtx = foldl' insertDef (emptyContext nm) d