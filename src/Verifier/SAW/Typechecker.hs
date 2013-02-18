{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveFoldable #-} 
{-# LANGUAGE DeriveTraversable #-} 
{-# LANGUAGE DoAndIfThenElse #-} 
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE GADTs  #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}
module Verifier.SAW.Typechecker
  ( tcModule
  ) where

import Control.Applicative
import Control.Arrow ((***), first, second)
import Control.Monad.State hiding (forM, forM_, mapM, mapM_, sequence, sequence_)
import Control.Monad.Identity (Identity(..))
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Traversable
import Data.Vector (Vector)
import qualified Data.Vector as V
import Text.PrettyPrint

import Prelude hiding ( all
                      , concat
                      , concatMap
                      , foldl
                      , foldr
                      , mapM
                      , mapM_
                      , sequence
                      , sequence_
                      , sum)

import Verifier.SAW.Utils

import Verifier.SAW.Position
import Verifier.SAW.Typechecker.Context
import Verifier.SAW.Typechecker.Monad
import Verifier.SAW.Typechecker.Simplification
import Verifier.SAW.Typechecker.Unification
import Verifier.SAW.TypedAST
import qualified Verifier.SAW.UntypedAST as Un

-- | Given a project function returning a key and a list of values, return a map
-- from the keys to values.
projMap :: Ord k => (a -> k) -> [a] -> Map k a
projMap f l = Map.fromList [ (f e,e) | e <- l ] 

-- | Given a list of keys and values, construct a map that maps each key to the list
-- of values.
multiMap :: Ord k => [(k,a)] -> Map k [a]
multiMap = foldl' fn Map.empty
  where fn m (k,v) = Map.insertWith (++) k [v] m

{-

mkEdgeMap :: Ord a => [(a,a)] -> Map a [a]
mkEdgeMap = foldl' fn Map.empty
  where fn m (x,y) = Map.insertWith (++) x [y] m

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
-}

-- Global context declarations.

-- | Type synonyms in untyped world.
type UnDefEqn = DefEqnGen Un.Pat Un.Term
type UnLocalDef = LocalDefGen Un.Term [UnDefEqn]

{-
-- | @extendModule m base@ returns base with the additional imports in @m@. 
extendModule :: Module -> Module -> Module
extendModule m base = flip (foldl' insDef) (moduleDefs m)
                    $ flip (foldl' insDataType) (moduleDataTypes m)
                    $ base
-}

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
                fn (PosPair _ nm,tp) = LocalFnDefGen nm tp eqs
                  where eqs = fromMaybe [] $ Map.lookup nm eqMap
        groupDecl :: GroupLocalDeclsState -> Un.Decl -> GroupLocalDeclsState
        groupDecl (tpMap,eqMap) (Un.TypeDecl idl tp) = (tpMap',eqMap)
          where tpMap' = foldr (\k -> Map.insert (val k) (k,tp)) tpMap idl
        groupDecl (tpMap,eqMap) (Un.TermDef pnm pats rhs) = (tpMap, eqMap')
          where eq = DefEqnGen (snd <$> pats) rhs
                eqMap' = Map.insertWith (++) (val pnm) [eq] eqMap
        groupDecl _ Un.DataDecl{} = error "Unexpected data declaration in let binding"

type TCDataType = DataTypeGen TCDTType (Ctor Ident TCCtorType)
type TCDef = TCDefGen Identity

fmapTCApply :: Functor f
            => (TermContext s, f TCTerm)
            -> (TermContext s, Vector TCTerm)
            -> f TCTerm
fmapTCApply (sTC, s) (vTC,v) = (\t -> tcApply vTC (sTC,t) (vTC,v)) <$> s

-- | Apply a vector of arguments to a fixed pi term.
tcFixedPiApply :: -- Function for base case.
                  -- Takes base value and its context along with extended version of arguments
                  -- in their context.
                  ((TermContext s, r) -> (TermContext s, Vector TCTerm) -> r)
                  -- Context for fixed pi type and itself.
                  -- The fixed pi type context should be an extension of the vector context.
               -> (TermContext s, FixedPiType r)
                  -- Context for vectors
               -> (TermContext s, Vector TCTerm)
                  -- Resulting fixed pi type will be in context for vectors.
               -> FixedPiType r
tcFixedPiApply baseFn i0 v@(vtc, _) = go i0
  where go (itc, FPResult r) = FPResult (baseFn (itc, r) v)
        go (itc, FPPi pat tp r) = FPPi pat' tp' (go (extendPatContext itc pat, r))
          where pat' = tcPatApply vtc (itc, pat) v
                tp' = tcApply vtc (itc, tp) v

tcDTTypeApply :: (TermContext s, TCDTType)
              -> (TermContext s, Vector TCTerm) -> TCDTType
tcDTTypeApply i0 (vtc0, v0) = tcFixedPiApply (\(_,s) _ -> s) i0 (vtc0, v0)

tcCtorTypeApply :: (TermContext s, TCCtorType)
                -> (TermContext s, Vector TCTerm)
                -> TCCtorType
tcCtorTypeApply = tcFixedPiApply base
  where base (itc, tl) (vtc,v) = (\t -> tcApply vtc (itc,t) (vtc, v)) <$> tl

tcEqns :: TermContext s -> [UnDefEqn] -> TCTerm -> TC s [TCDefEqn]
tcEqns tc ueqs tp = traverse (\eq -> tcEqn tc eq tp) ueqs

-- | Typecheck equation is returns a term with the given type.
tcEqn :: TermContext s -> UnDefEqn -> TCTerm -> TC s TCDefEqn
tcEqn tc (DefEqnGen [] unrhs) tp = DefEqnGen [] <$> tcTerm tc unrhs tp
tcEqn tc (DefEqnGen unpats unrhs) tp = do
  ((pats,rhsTp), tc') <- typecheckPiPats tc unpats tp
  DefEqnGen pats <$> tcTerm tc' unrhs rhsTp

tcTerm :: TermContext s
       -- Typecheck term
       -> Un.Term
          -- | Required type type (actual type may be a subtype).
       -> TCTerm
       -- Typechecked term.
       -> TC s TCTerm
tcTerm tc ut rtp = do
  (v,tp) <- inferTypedValue tc ut
  v <$ checkTypeSubtype tc (pos ut) tp rtp

 
-- | Check that term is equivalent to Sort i for some i.
checkIsSort :: TermContext s -> Pos -> TCTerm -> TC s Sort
checkIsSort tc p t0 = do
  t <- reduce tc t0
  case t of
    TCF (Sort s) -> return s
    _ -> tcFailD p $ ppTCTerm tc 0 t <+> text "could not be interpreted as a sort."

-- | Typecheck a term as a type, returning a term equivalent to it, and
-- with the same type as the term.
tcType :: TermContext s -> Un.Term -> TC s (TCTerm,Sort)
tcType tc t = do
  (v,tp) <- inferTypedValue tc t
  (v,) <$> checkIsSort tc (pos t) tp

tcSort :: TermContext s -> Un.Term -> TC s Sort
tcSort tc t = checkIsSort tc (pos t) . fst =<< inferTypedValue tc t

tcSpecificDataType :: Ident -> TermContext s -> Un.Term -> TC s [TCTerm]
tcSpecificDataType expected tc ut = do
  (v,_) <- inferTypedValue tc ut
  rtp <- reduce tc v
  case rtp of
    TCF (DataTypeApp i tl) | i == expected -> pure tl
    _ -> tcFail (pos ut) $ "Expected " ++ show expected


tcFixedPiType :: forall r s . (TermContext s -> Un.Term -> TC s r)
              -> TermContext s -> Un.Term -> TC s (FixedPiType r)
tcFixedPiType fn = go 
  where go tc (Un.Pi _ upats0 utp _ rhs) = do
          (tp0, _) <- tcType tc utp
          let tcPats :: TermContext s
                     -> [Un.SimplePat]
                     -> TCTerm
                     -> TC s (FixedPiType r)
              tcPats tc1 [] _ = go tc1 rhs
              tcPats tc1 (upat:upats) tp = do
                ([pat], tc2) <- typecheckPats tc1 [Un.PSimple upat] tp
                FPPi pat tp <$> tcPats tc2 upats (applyExt (tc1, tp) tc2)
          tcPats tc upats0 tp0
        go tc ut = FPResult <$> fn tc ut

tcDTType :: TermContext s -> Un.Term -> TC s TCDTType
tcDTType = tcFixedPiType tcSort

tcCtorType :: Ident -> TermContext s -> Un.Term -> TC s TCCtorType
tcCtorType i = tcFixedPiType (tcSpecificDataType i)

maximumSort :: Foldable f => f Sort -> Sort
maximumSort = foldl' maxSort (mkSort 0)

inferTypedValue :: TermContext s -> Un.Term -> TC s (TCTerm, TCTerm)
inferTypedValue tc ut = do
  r <- inferTerm tc ut
  case r of
    PartialCtor{} ->
      tcFail (pos ut) $ "Expected additional argument to constructor."
    PartialDataType{} ->
      tcFail (pos ut) $ "Expected additional argument to data type."
    TypedValue v tp -> pure (v, tp)

inferLambda  :: TermContext s
             -> [(Un.ParamType, [Un.Pat], Un.Term)] -- Patterns.
             -> Un.Term -- Right hand side of lambda expression
             -> TC s InferResult
inferLambda tc0 pl0 urhs = go [] tc0 pl0
  where go args tc [] = mkRes <$> inferTypedValue tc urhs
          where mkRes (v,tp) = TypedValue v' tp'
                  where v'  = foldr (uncurry TCLambda) v args
                        tp' = foldr (uncurry TCPi) tp args
        go args tc1 ((_,patl,utp):l) = do
          (tp,_) <- tcType tc1 utp
          (pl,tc') <- typecheckPats tc1 patl tp
          let typedPL = (,tp) <$> pl 
          go (args ++ typedPL) tc' l

inferTerm :: TermContext s -> Un.Term -> TC s InferResult
inferTerm tc uut = do
  case uut of
    Un.Var i -> resolveIdent tc i
    Un.Unused{} -> fail "Pattern syntax when type expected."
    Un.Con i -> resolveIdent tc i
    Un.Sort _ s -> return $ TypedValue (TCF (Sort s)) (TCF (Sort (sortOf s)))
    Un.Lambda _ pl r -> inferLambda tc pl r
    Un.App uf _ ua -> mkRes =<< inferTerm tc uf
      where mkRes (PartialCtor dt i rargs pat tp cur) = do
              (args, a) <- matchPat tc (pos ua) pat =<< tcTerm tc ua tp
              let tc1 = extendPatContext tc pat
              case cur of
                FPResult dtArgs -> pure $ TypedValue v tp'
                  where v = TCF (CtorApp i (reverse (a:rargs)))
                        tp' = TCF (DataTypeApp dt (fmapTCApply (tc1, dtArgs) (tc,args)))
                FPPi pat1 tp1 next -> pure $ PartialCtor dt i (a:rargs) pat1' tp1' next'
                  where pat1' = tcPatApply tc (tc1,pat1) (tc,args)
                        tp1' = tcApply tc (tc1,tp1) (tc,args)
                        next' = tcCtorTypeApply (extendPatContext tc1 pat1, next) (tc,args)
            mkRes (PartialDataType dt rargs pat tp cur) = do
              (args, a) <- matchPat tc (pos ua) pat =<< tcTerm tc ua tp
              case cur of
                FPResult s -> pure $ TypedValue v (TCF (Sort s))
                  where v = TCF (DataTypeApp dt (reverse (a:rargs)))
                FPPi pat1 tp1 next -> pure $ PartialDataType dt (a:rargs) pat1' tp1' next'
                  where tc1 = extendPatContext tc pat
                        pat1' = tcPatApply tc (tc1,pat1) (tc, args)
                        tp1'  = tcApply tc (tc1,tp1) (tc, args)
                        next' = tcDTTypeApply (extendPatContext tc1 pat1, next) (tc, args)
            mkRes (TypedValue v tp0) = do
              (pat,patTp,tp) <- reduceToPiExpr tc (pos uf) tp0
              (args, a) <- matchPat tc (pos ua) pat =<< tcTerm tc ua patTp
              let tc1 = extendPatContext tc pat
              return $ TypedValue (TCF (App v a)) (tcApply tc (tc1,tp) (tc, args))
    Un.Pi _ [] _ _ _ -> fail "Pi with no paramters encountered."
    Un.Pi _ upats0 utp _ rhs -> do
      (tp0,tps) <- tcType tc utp
      let tcPats :: TermContext s -> [Un.SimplePat] -> TCTerm -> TC s (TCTerm, Sort)
          tcPats tc1 [] _ = tcType tc1 rhs
          tcPats tc1 (upat:upats) tp = do
            ([pat], tc2) <- typecheckPats tc1 [Un.PSimple upat] tp
            first (TCPi pat tp) <$> tcPats tc2 upats (applyExt (tc1, tp) tc2)
      (v',rps) <- tcPats tc upats0 tp0
      return $ TypedValue v' (TCF (Sort (maxSort rps tps)))
    Un.TupleValue _ tl -> do
      (vl,tpl) <- unzip <$> traverse (inferTypedValue tc) tl
      return $ TypedValue (TCF (TupleValue vl)) (TCF (TupleType tpl))
    Un.TupleType _ tl  -> do
      (tpl,sl) <- unzip <$> traverse (tcType tc) tl
      return $ TypedValue (TCF (TupleType tpl))
                          (TCF (Sort (maximumSort sl)))

    Un.RecordValue p (unzip -> (fmap val -> fl,vl))
        | hasDups fl -> tcFail p "Duplicate fields in record"
        | otherwise -> uncurry TypedValue . mkRes . unzip <$> traverse (inferTypedValue tc) vl
      where mkMap fn vals = TCF (fn (Map.fromList (fl `zip` vals)))
            mkRes = mkMap RecordValue *** mkMap RecordType
    Un.RecordSelector ux (PosPair p f) -> do
      (x,tp) <- inferTypedValue tc ux
      m <- reduceToRecordType tc p tp
      case Map.lookup f m of
        Nothing -> tcFail p $ "No field named " ++ f ++ " in record."
        Just ftp -> return $ TypedValue (TCF (RecordSelector x f)) ftp
    Un.RecordType p (unzip -> (fmap val -> fl,vl))
        | hasDups fl -> tcFail p "Duplicate fields in record"
        | otherwise -> uncurry TypedValue . mkRes . unzip <$> traverse (tcType tc) vl
      where mkMap fn vals = TCF (fn (Map.fromList (fl `zip` vals)))
            mkRes = (mkMap RecordType) *** (TCF . Sort . maximumSort)
    Un.TypeConstraint ut _ utp -> do
      (tp,_) <- tcType tc utp
      flip TypedValue tp <$> tcTerm tc ut tp
    Un.Paren _ t -> uncurry TypedValue <$> inferTypedValue tc t
    Un.LetTerm p udl urhs -> do
      (tc', lcls) <- tcLocalDecls tc p udl
      (rhs,rhsTp) <- inferTypedValue tc' urhs
      return $ TypedValue (TCLet lcls rhs) (TCLet lcls rhsTp)
    Un.IntLit p i | i < 0 -> fail $ ppPos p ++ " Unexpected negative natural number literal."
                  | otherwise -> pure $ TypedValue (TCF (NatLit i)) nattp
      where nattp = TCF (DataTypeApp preludeNatIdent [])
    Un.BadTerm p -> fail $ "Encountered bad term from position " ++ show p

tcLocalDecls :: TermContext s
             -> Pos
             -> [Un.Decl]
             -> TC s (TermContext s, [TCLocalDef])
tcLocalDecls tc0 p lcls = do
    (tps,pending) <- unzip <$> traverse tcLclType (groupLocalDecls lcls)
    let tc = consLocalDefs tps tc0
    traverse_ ($ tc) pending
    let mkDef (LocalFnDefGen nm tp r) = LocalFnDefGen nm tp <$> eval p r
    (tc,) <$> traverse mkDef tps
  where tcLclType (LocalFnDefGen nm utp ueqs) = do
          (tp,_) <- tcType tc0 utp
          r <- newRef nm
          let pendingFn tc = do
                let tp' = applyExt (tc0,tp) tc
                assign r (tcEqns tc ueqs tp')
          return (LocalFnDefGen nm tp r, pendingFn)

-- | @checkTypeSubtype tc p x y@ checks that @x@ is a subtype of @y@.
checkTypeSubtype :: forall s . TermContext s -> Pos -> TCTerm -> TCTerm -> TC s ()
checkTypeSubtype tc p x y = do
  xr <- reduce tc x
  yr <- reduce tc y
  let ppFailure = tcFailD p msg
        where msg = ppTCTerm tc 0 xr <+> text "is not a subtype of" <+> ppTCTerm tc 0 yr <> char '.'
  case (tcAsApp xr, tcAsApp yr) of
    ( (TCF (Sort xs), []), (TCF (Sort ys), []) )
      | xs <= ys -> return ()
      | otherwise -> ppFailure
    _ -> checkTypesEqual' p [] tc xr yr

-- | Match untyped term against pattern, returning variables in reverse order.
-- so that last-bound variable is first.  Also returns the term after it was matched.
-- This may differ to the input term due to the use of reduction during matching.
matchPat :: forall s
          . TermContext s
         -> Pos -> TCPat -> TCTerm -> TC s (Vector TCTerm, TCTerm)
matchPat tc p pat t = do
  mr <- tryMatchPat tc pat t
  case mr of
    Nothing -> tcFail p $ "Pattern match failed."
    Just r -> return r

reduceToRecordType :: TermContext s -> Pos -> TCTerm -> TC s (Map FieldName TCTerm)
reduceToRecordType tc p tp = do
  rtp <- reduce tc tp
  case rtp of
    TCF (RecordType m) -> return m
    _ -> tcFailD p $ text "Attempt to dereference field of term with type:" $$ 
                       nest 2 (ppTCTerm tc 0 rtp)

topEval :: TCRef s v -> TC s v
topEval r = eval (internalError $ "Cyclic error in top level" ++ show r) r

evalDataType :: TCRefDataType s -> TC s TCDataType
evalDataType (DataTypeGen n tp ctp) =
  liftM2 (DataTypeGen n)
         (topEval tp) 
         (traverse (traverse topEval) ctp)

evalDef :: TCRefDef s -> TC s TCDef
evalDef (DefGen nm tpr elr) =
  liftA2 (DefGen nm) (Identity <$> topEval tpr) (Identity <$> topEval elr)

data CompletionContext
  = CCGlobal Module
  | CCBinding CompletionContext Term

addPatTypes :: CompletionContext -> [(String,TCTerm)] -> (CompletionContext, [Term])
addPatTypes cc0 vars = mapAccumL ins cc0 vars
  where ins cc (_,tp) = (CCBinding cc tp', tp')
          where tp' = completeTerm cc tp

ccVarType :: CompletionContext -> DeBruijnIndex -> Term
ccVarType cc0 i0 = go cc0 i0
  where go (CCBinding cc t) i
          | i == 0 = incVars 0 (i0+1) t
          | otherwise = go cc (i-1)
        go CCGlobal{} _ = error "Could not find var with index in context."

completeDataType :: CompletionContext
                 -> TCDataType
                 -> TypedDataType
completeDataType cc (DataTypeGen dt tp cl) = 
  ( DataType { dtName = dt
             , dtType = completeTerm cc (termFromTCDTType tp)
             }
  , fmap (completeTerm cc . termFromTCCtorType dt) <$> cl
  )

completeDef :: CompletionContext
            -> TCDef
            -> TypedDef
completeDef cc (DefGen nm tp el) = def
  where def = Def { defIdent = nm 
                  , defType = completeTerm cc (runIdentity tp)
                  , defEqs = completeDefEqn cc <$> (runIdentity el) 
                  }

completeDefEqn :: CompletionContext -> TCDefEqn -> TypedDefEqn
completeDefEqn cc (DefEqnGen pats rhs) = eqn
  where bindings = runPatVarParser (mapM_ addPatBindings pats)
        (cc', v) = second V.fromList $ addPatTypes cc bindings
        eqn = DefEqn (completePat' v <$> pats) (completeTerm cc' rhs)

completePat :: CompletionContext -> TCPat -> (Pat Term, CompletionContext)
completePat cc0 pat = (completePat' v pat, cc')
  where (cc', v) = second V.fromList $ addPatTypes cc0 (patBoundVars pat)

completePat' :: Vector Term -> TCPat -> Pat Term
completePat' v = go
  where go (TCPVar nm i _) = PVar nm i (v V.! i)
        go TCPUnused{} = PUnused
        go (TCPatF pf) =
          case pf of
            UPTuple l -> PTuple (go <$> l)
            UPRecord m -> PRecord (go <$> m)
            UPCtor c l -> PCtor c (go <$> l)

localBoundVars :: TCLocalDef -> (String, TCTerm)
localBoundVars (LocalFnDefGen nm tp _) = (nm,tp)

-- | Returns the type of a unification term in the current context.
completeTerm :: CompletionContext -> TCTerm -> Term
completeTerm cc (TCF tf) = Term $ FTermF $ fmap (completeTerm cc) tf
completeTerm cc (TCLambda pat tp r) =
    Term $ Lambda pat' (completeTerm cc tp) (completeTerm cc' r)
  where (pat', cc') = completePat cc pat
completeTerm cc (TCPi pat@(TCPVar nm _ _) tp r) =
    Term $ Pi nm (completeTerm cc tp) (completeTerm cc' r)
  where (_, cc') = completePat cc pat
completeTerm cc (TCPi pat@(TCPUnused nm) tp r) =
    Term $ Pi nm (completeTerm cc tp) (completeTerm cc' r)
  where (_, cc') = completePat cc pat
completeTerm _ (TCPi TCPatF{} _ _) = internalError "Illegal TCPi term" 
completeTerm cc (TCLet lcls t) = Term $ Let lcls' (completeTerm cc' t)
  where (cc',tps) = addPatTypes cc (localBoundVars <$> lcls)
        completeLocal (LocalFnDefGen nm _ eqns) tp =
          LocalFnDef nm tp (completeDefEqn cc' <$> eqns)
        lcls' = zipWith completeLocal lcls tps
completeTerm cc (TCVar i) = Term $ LocalVar i (ccVarType cc i)
completeTerm cc (TCLocalDef i) = Term $ LocalVar i (ccVarType cc i)


addImportNameStrings :: Un.ImportName -> Set String -> Set String
addImportNameStrings im s =
  case im of
    Un.SingleImport pnm -> Set.insert (val pnm) s
    Un.AllImport pnm -> Set.insert (val pnm) s
    Un.SelectiveImport pnm cl -> foldr Set.insert s (val <$> (pnm:cl)) 

-- | Returns set of names identified in a given list of names to import.
importNameStrings :: [Un.ImportName] -> Set String
importNameStrings = foldr addImportNameStrings Set.empty

includeNameInModule :: Maybe Un.ImportConstraint -> Ident -> Bool
includeNameInModule mic = fn . identName
  where fn = case mic of
               Nothing -> \_ -> True
               Just (Un.SpecificImports iml) -> flip Set.member imset
                 where imset = importNameStrings iml
               Just (Un.HidingImports iml) -> flip Set.notMember imset
                 where imset = importNameStrings iml

-- | Creates a module from a list of untyped declarations.
tcModule :: [Module] -- ^ List of modules loaded already.
               -> Un.Module
               -> Either Doc Module
tcModule ml (Un.Module (PosPair _ nm) iml d) = do
  let moduleMap = projMap moduleName ml
  runTC $ do
    let gc0 = emptyGlobalContext
    let is0 = IS { isModuleName = nm
                 , isCtx = gc0
                 , isPending = []
                 }
    let eqnMap = multiMap [ (val psym, DefEqnGen (snd <$> lhs) rhs)
                          | Un.TermDef psym lhs rhs <- d
                          ]
    -- Parse imports and declarations.
    let actions = fmap (parseImport moduleMap) iml
               ++ fmap (parseDecl eqnMap) d
    is <- execStateT (sequenceA_ actions) is0
    let gc = isCtx is
    let tc = emptyTermContext gc
    -- Execute pending assignments with final TermContext.
    sequence_ $ (($ tc) <$> isPending is)
    
    let mkFinal tps defs = m
          where cc = CCGlobal m
                m = flip (foldl' insDef) (completeDef cc <$> defs)
                  $ flip (foldl' insDataType) (completeDataType cc <$> tps)
                  $ emptyModule nm
    liftA2 mkFinal
           (traverse evalDataType (gcTypes gc))
           (traverse evalDef (gcDefs gc))

type VarCollector = State (Map Int (String, Term)) ()

runVarCollector :: TermContext s -> VarCollector -> TC s (Vector TCTerm, TermContext s)
runVarCollector tc0 vc = runStateT (traverse fn v) tc0
  where m = execState vc Map.empty
        v = V.fromList (Map.elems m)
        fn (nm,tp) = StateT $ \tc ->
          (\tp' -> (tp', consBoundVar nm tp' tc)) <$> liftTCTerm tc tp

patVarInfo :: Pat Term -> VarCollector
patVarInfo = go
  where go (PVar nm i tp) = modify $ Map.insert i (nm,tp)
        go PUnused = return ()
        go (PTuple l) = traverse_ go l
        go (PRecord m) = traverse_ go m
        go (PCtor _ l) = traverse_ go l

liftTCPat :: Vector TCTerm -> Pat Term -> TCPat
liftTCPat tps = go
  where go (PVar nm i _) = TCPVar nm i (tps V.! i)
        go PUnused  = TCPUnused "_"
        go (PTuple pl)  = TCPatF (UPTuple  (go <$> pl))
        go (PRecord pm) = TCPatF (UPRecord (go <$> pm))
        go (PCtor c pl) = TCPatF (UPCtor c (go <$> pl))

liftEqn :: TermContext s -> DefEqn Term -> TC s TCDefEqn
liftEqn tc0 (DefEqn pl r) = do
  (tps, tc) <- runVarCollector tc0 (traverse_ patVarInfo pl)
  DefEqnGen (liftTCPat tps <$> pl) <$> liftTCTerm tc r

liftLocalDefs :: TermContext s -> [LocalDef Term] -> TC s ([TCLocalDef], TermContext s)
liftLocalDefs tc0 lcls = do
    (tps,pending) <- unzip <$> traverse tcLclType lcls
    let tc = consLocalDefs tps tc0
    traverse_ ($ tc) pending
    let mkDef (LocalFnDefGen nm tp r) = LocalFnDefGen nm tp <$> topEval r
    (,tc) <$> traverse mkDef tps
  where tcLclType (LocalFnDef nm tp0 eqs) = do
          tp <- liftTCTerm tc0 tp0
          r <- newRef nm
          let pendingFn tc = do
                assign r (traverse (liftEqn tc) eqs)
          return (LocalFnDefGen nm tp r, pendingFn)

liftTCTerm :: TermContext s -> Term -> TC s TCTerm
liftTCTerm tc (Term tf) = 
  case tf of
    FTermF ftf -> TCF <$> traverse (liftTCTerm tc) ftf
    Lambda pat tp rhs -> do
       (tps, tc') <- runVarCollector tc (patVarInfo pat)
       TCLambda (liftTCPat tps pat) <$> liftTCTerm tc tp <*> liftTCTerm tc' rhs
    Pi nm tp rhs -> do
      tp' <- liftTCTerm tc tp
      let tc' = consBoundVar nm tp' tc
      TCPi (TCPVar nm 0 tp') tp' <$> liftTCTerm tc' rhs
    Let lcls r -> do
      (lcls', tc') <- liftLocalDefs tc lcls
      TCLet lcls' <$> liftTCTerm tc' r
    LocalVar i _ -> return $ 
      case resolveBoundInfo i tc of
        BoundVar{} -> TCVar i
        LocalDef{} -> TCLocalDef i


liftFixedType :: (TermContext s -> Term -> TC s (FixedPiType r))
              -> TermContext  s -> Term -> TC s (FixedPiType r)
liftFixedType fn tc (Term (Pi nm t r)) = do
  t' <- liftTCTerm tc t
  let tc' = consBoundVar nm t' tc
  FPPi (TCPVar nm 0 t') t' <$> liftFixedType fn tc' r
liftFixedType fn tc t = fn tc t

liftTCDataType :: TermContext s -> Term -> TC s TCDTType
liftTCDataType = liftFixedType fn
  where fn _ (Term (FTermF (Sort s))) = return (FPResult s)
        fn _ _ = fail "Unexpected term to liftTCDataType"

liftTCCtorType :: Ident -> TermContext s -> Term -> TC s TCCtorType
liftTCCtorType dt tc0 t0 = liftFixedType fn tc0 t0
  where fn tc (Term (FTermF (DataTypeApp i tl))) | dt == i = do
          FPResult <$> traverse (liftTCTerm tc) tl
        fn _ _ = fail $ "Unexpected term to liftTCCtorType " ++ show dt ++ ":\n  " ++ show t0

-- | Typechecker computation that needs input before running.
type PendingAction s a = a -> TC s ()

mkPendingAssign :: TCRef s v -> (a -> TC s v) -> PendingAction s a
mkPendingAssign r f a = assign r (f a)

data InitState s = IS { isModuleName :: ModuleName
                      , isCtx :: GlobalContext s
                      , isPending :: [ PendingAction s (TermContext s) ]
                      }

type Initializer s a = StateT (InitState s) (TC s) a

initModuleName :: Initializer s ModuleName
initModuleName = gets isModuleName

updateIsCtx :: (GlobalContext s -> GlobalContext s) -> Initializer s ()
updateIsCtx f = modify $ \s -> s { isCtx = f (isCtx s) }

addPending :: NodeName -> (TermContext s -> TC s r) -> Initializer s (TCRef s r)
addPending nm fn = do
  r <- lift $ newRef nm  
  r <$ modify (\s -> s { isPending = mkPendingAssign r fn : isPending s })

parseCtor :: Ident -> Un.CtorDecl -> Initializer s (Bool, TCRefCtor s)
parseCtor dt (Un.Ctor pnm utp) = do
  mnm <- initModuleName
  tp <- addPending (val pnm) (\tc -> tcCtorType dt tc utp)
  let ci = mkIdent mnm (val pnm)
  return (True, Ctor { ctorName = ci, ctorType = tp })

parseDecl :: Map String [UnDefEqn] -> Un.Decl -> Initializer s ()
parseDecl eqnMap d = do
  mnm <- initModuleName
  case d of
    Un.TypeDecl idl utp -> do
      let id1:_ = idl
      rtp <- addPending (val id1) (\uc -> fst <$> tcType uc utp)
      for_ idl $ \(PosPair p nm) -> do
        let ueqs = fromMaybe [] $ Map.lookup nm eqnMap
        eqs <- addPending ("Equations for " ++ nm) $ \tc -> do
          tp <- eval p rtp
          tcEqns tc ueqs tp
        let di = mkIdent mnm nm
        updateIsCtx $ insertDef [Nothing] True (DefGen di rtp eqs)
    Un.DataDecl psym utp ucl -> do
      let dti = mkIdent mnm (val psym)
      dt <- liftA2 (DataTypeGen dti)
                   (addPending (val psym) (\tc -> tcDTType tc utp))
                   (traverse (parseCtor dti) ucl)
      updateIsCtx $ insertDataType [Nothing] True dt
    Un.TermDef{} -> return ()

parseImport :: Map ModuleName Module
            -> Un.Import
            -> Initializer s ()
parseImport moduleMap (Un.Import q (PosPair p nm) mAsName mcns) = do
  case Map.lookup nm moduleMap of
    Nothing -> lift $ tcFail p $ "Cannot find module " ++ show nm ++ "."
    Just m -> do
      -- Get list of module names to use for local identifiers.
      let mnml | q = [Just qnm]
               | otherwise = [Nothing, Just qnm]
            where qnm = maybe (moduleName m)
                              (\s -> Un.mkModuleName [s])
                              (val <$> mAsName)
      -- Add datatypes to module
      for_ (moduleDataTypes m) $ \(dt, ctors) -> do
        let dtnm = dtName dt
        dtr <- addPending (identName dtnm) $ \tc -> liftTCDataType tc (dtType dt)
        -- Add constructors to module.
        cl <- for ctors $ \c -> do
          let cnm = ctorName c
              cfn tc = liftTCCtorType dtnm tc (ctorType c)
          let use = includeNameInModule mcns cnm
          (use,) . Ctor cnm <$> addPending (identName cnm) cfn
        let dtuse = includeNameInModule mcns dtnm
        updateIsCtx $ insertDataType mnml dtuse (DataTypeGen dtnm dtr cl)
      -- Add definitions to module.
      for_ (moduleDefs m) $ \def -> do
        let inm = identName (defIdent def)
        tpr <- addPending inm $ \tc ->
          liftTCTerm tc (defType def)
        eqr <- addPending inm $ \tc ->
          traverse (liftEqn tc) (defEqs def)
        let use = includeNameInModule mcns (defIdent def)
        updateIsCtx $ insertDef mnml use (DefGen (defIdent def) tpr eqr)