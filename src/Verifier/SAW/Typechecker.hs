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
import Control.Arrow ((***), first)
import Control.Lens hiding (assign)
import Control.Monad.State
import Control.Monad.Identity (Identity(..))
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe, isJust)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Vector (Vector)
import qualified Data.Vector as V
import Text.PrettyPrint

import Verifier.SAW.Utils (internalError)

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
multiMap = foldlOf' folded fn Map.empty
  where fn m (k,v) = Map.insertWith (++) k [v] m

-- Global context declarations.

-- | Type synonyms in untyped world.
type UnDefEqn = DefEqnGen Un.Pat Un.Term
type UnLocalDef = LocalDefGen Un.Term [UnDefEqn]

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

-- | Typecheck equation is returns a term with the given type.
tcEqn :: TermContext s -> TCTerm -> UnDefEqn -> TC s TCDefEqn
tcEqn tc tp (DefEqnGen [] unrhs) = DefEqnGen [] <$> tcTerm tc unrhs tp
tcEqn tc tp (DefEqnGen unpats@(up:_) unrhs) = do
  ((pats,rhsTp), tc') <- typecheckPiPats tc (pos up) unpats tp
  let c = termBoundCount tc
  unless (isJust $ checkTCPatOf c traverse pats) $ error "tcEqn patterns failed"
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
                FPPi pat tp <$> tcPats tc2 upats (applyExt tc2 (tc1, tp))
          tcPats tc upats0 tp0
        go tc ut = FPResult <$> fn tc ut

tcDTType :: TermContext s -> Un.Term -> TC s TCDTType
tcDTType = tcFixedPiType tcSort

tcCtorType :: Ident -> TermContext s -> Un.Term -> TC s TCCtorType
tcCtorType i = tcFixedPiType (tcSpecificDataType i)

maximumSortOf :: Fold s Sort -> s -> Sort
maximumSortOf fold = foldlOf' fold maxSort (mkSort 0)

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
            first (TCPi pat tp) <$> tcPats tc2 upats (applyExt tc2 (tc1, tp))
      (v',rps) <- tcPats tc upats0 tp0
      return $ TypedValue v' (TCF (Sort (maxSort rps tps)))
    Un.TupleValue _ tl -> do
      (vl,tpl) <- unzip <$> traverse (inferTypedValue tc) tl
      return $ TypedValue (TCF (TupleValue vl)) (TCF (TupleType tpl))
    Un.TupleType _ tl  -> do
      (tpl,sl) <- unzip <$> traverse (tcType tc) tl
      return $ TypedValue (TCF (TupleType tpl))
                          (TCF (Sort (maximumSortOf folded sl)))
    Un.TupleSelector ux (PosPair p i) -> do
      (x,tp) <- inferTypedValue tc ux
      ts <- reduceToTupleType tc p tp
      case lookup i (zip [1..] ts) of
        Nothing -> tcFail p $ "No component number " ++ show i ++ " in tuple."
        Just ftp -> return $ TypedValue (TCF (TupleSelector x (fromIntegral i))) ftp

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
            mkRes = (mkMap RecordType) *** (TCF . Sort . maximumSortOf folded)
    Un.TypeConstraint ut _ utp -> do
      (tp,_) <- tcType tc utp
      flip TypedValue tp <$> tcTerm tc ut tp
    Un.Paren _ t -> uncurry TypedValue <$> inferTypedValue tc t
    Un.LetTerm p udl urhs -> do
      (tc', lcls) <- tcLocalDecls tc p udl
      (rhs,rhsTp) <- inferTypedValue tc' urhs
      return $ TypedValue (TCLet lcls rhs) (TCLet lcls rhsTp)
    Un.NatLit p i | i < 0 -> fail $ ppPos p ++ " Unexpected negative natural number literal."
                  | otherwise -> pure $ TypedValue (TCF (NatLit i)) nattp
      where nattp = TCF (DataTypeApp preludeNatIdent [])
    Un.VecLit p [] -> tcFail p "SAWCore parser does not support empty array literals."
    Un.VecLit _ (h:l) -> do
      (v,tp) <- inferTypedValue tc h
      vl <- traverse (\u -> tcTerm tc u tp) l
      let vals = V.fromList (v:vl)
      let n = TCF (NatLit (toInteger (V.length vals)))
      return $ TypedValue (TCF (ArrayValue tp vals)) (TCF (DataTypeApp preludeVecIdent [n,tp]))
    Un.BadTerm p -> fail $ "Encountered bad term from position " ++ show p

tcLocalDecls :: TermContext s
             -> Pos
             -> [Un.Decl]
             -> TC s (TermContext s, [TCLocalDef])
tcLocalDecls tc0 p lcls = do
    (tps,pending) <- unzip <$> traverse tcLclType (groupLocalDecls lcls)
    let tc = consLocalDefs tps tc0
    traverseOf_ folded ($ tc) pending
    let mkDef (LocalFnDefGen nm tp r) = LocalFnDefGen nm tp <$> eval p r
    (tc,) <$> traverse mkDef tps
  where tcLclType (LocalFnDefGen nm utp ueqs) = do
          (tp,_) <- tcType tc0 utp
          r <- newRef nm
          let pendingFn tc = do
                let tp' = applyExt tc (tc0,tp)
                assignRef r (traverse (tcEqn tc tp') ueqs)
          return (LocalFnDefGen nm tp r, pendingFn)

-- | @checkTypeSubtype tc p x y@ checks that @x@ is a subtype of @y@.
checkTypeSubtype :: forall s . TermContext s -> Pos -> TCTerm -> TCTerm -> TC s ()
checkTypeSubtype tc p x y = do
  xr <- reduce tc x
  yr <- reduce tc y
  let ppFailure = tcFailD p msg
        where msg = ppTCTerm tc 0 xr <+> text "is not a subtype of"
                                     <+> ppTCTerm tc 0 yr <> char '.'
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

reduceToTupleType :: TermContext s -> Pos -> TCTerm -> TC s [TCTerm]
reduceToTupleType tc p tp = do
  rtp <- reduce tc tp
  case rtp of
    TCF (TupleType ts) -> return ts
    _ -> tcFailD p $ text "Attempt to dereference component of term with type:" $$
                       nest 2 (ppTCTerm tc 0 rtp)

topEval :: TCRef s v -> TC s v
topEval r = eval (internalError $ "Cyclic error in top level" ++ show r) r

evalDataType :: TCRefDataType s -> TC s TCDataType
evalDataType (DataTypeGen n tp ctp) =
  DataTypeGen n <$> topEval tp
                <*> traverse (traverse topEval) ctp

evalDef :: TCRefDef s -> TC s TCDef
evalDef (DefGen nm tpr elr) =
  DefGen nm <$> (Identity <$> topEval tpr)
            <*> (Identity <$> topEval elr)

data CompletionContext
  = CCGlobal Module
  | CCBinding CompletionContext Term

addPatTypes :: CompletionContext
            -> Vector (String,TCTerm)
            -> (CompletionContext, Vector Term)
addPatTypes cc0 bl =
 mapAccumLOf traverse ins cc0 (snd <$> bl)
  where ins cc tp = (CCBinding cc tp', tp')
          where tp' = completeTerm cc tp

-- | Returns var with index in context or nothing if it not defined.
ccVarType :: CompletionContext -> DeBruijnIndex -> Maybe Term
ccVarType cc0 i0 = go cc0 i0
  where go (CCBinding cc t) i
          | i == 0 = Just $ incVars 0 (i0+1) t
          | otherwise = go cc (i-1)
        go CCGlobal{} _ = Nothing

completeDataType :: CompletionContext
                 -> TCDataType
                 -> TypedDataType
completeDataType cc (DataTypeGen dt tp cl) =
  DataType { dtName = dt
           , dtType = completeTerm cc (termFromTCDTType tp)
           , dtCtors = fmap (completeTerm cc . termFromTCCtorType dt) <$> cl
           }

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
  where (pats',cc') = completePatT cc pats
        eqn = DefEqn pats' (completeTerm cc' rhs)


completePatT :: Traversable f
             => CompletionContext
             -> f TCPat
             -> (f (Pat Term), CompletionContext)
completePatT cc0 pats = (pats', cc')
  where bl = patBoundVarsOf folded pats
        ins cc tp = (CCBinding cc tp', (cc,tp'))
          where tp' = completeTerm cc tp
        (cc', v) =  mapAccumLOf traverse ins cc0 (snd <$> bl)
        ctxv = fmap fst v `V.snoc` cc'
        boundTypes = snd <$> v
        go (TCPVar nm (i,_)) = PVar nm i tp
          where Just tp = boundTypes V.!? i
        go (TCPUnused _ (i,tp)) = PUnused i (completeTerm cc tp)
          where Just cc = ctxv V.!? i
        go (TCPatF pf) =
          case pf of
            UPTuple l -> PTuple (go <$> l)
            UPRecord m -> PRecord (go <$> m)
            UPCtor c l -> PCtor c (go <$> l)
        pats' = go <$> pats


completePat :: CompletionContext -> TCPat -> (Pat Term, CompletionContext)
completePat cc0 pat = over _1 runIdentity $ completePatT cc0 (Identity pat)

localBoundVars :: TCLocalDef -> (String, TCTerm)
localBoundVars (LocalFnDefGen nm tp _) = (nm,tp)

-- | Returns the type of a unification term in the current context.
completeTerm :: CompletionContext -> TCTerm -> Term
completeTerm cc (TCF tf) = Term $ FTermF $ fmap (completeTerm cc) tf
completeTerm cc (TCLambda pat tp r) =
    Term $ Lambda pat' (completeTerm cc tp) (completeTerm cc' r)
  where (pat', cc') = completePat cc pat
completeTerm cc (TCPi pat@(TCPVar nm _) tp r) =
    Term $ Pi nm (completeTerm cc tp) (completeTerm cc' r)
  where (_, cc') = completePat cc pat
completeTerm cc (TCPi pat@(TCPUnused nm _) tp r) =
    Term $ Pi nm (completeTerm cc tp) (completeTerm cc' r)
  where (_, cc') = completePat cc pat
completeTerm _ (TCPi TCPatF{} _ _) = internalError "Illegal TCPi term"
completeTerm cc (TCLet lcls t) = Term $ Let lcls' (completeTerm cc' t)
  where (cc',tps) = addPatTypes cc (localBoundVars <$> V.fromList lcls)
        completeLocal (LocalFnDefGen nm _ eqns) tp =
          LocalFnDef nm tp (completeDefEqn cc' <$> eqns)
        lcls' = zipWith completeLocal lcls (V.toList tps)
completeTerm cc (TCVar i) = Term $ LocalVar i tp
  where Just tp = ccVarType cc i
completeTerm cc (TCLocalDef i) = Term $ LocalVar i tp
  where Just tp = ccVarType cc i

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
    let is0 = IS { _isModule = emptyModule nm
                 , _isCtx = gc0
                 , _isTypes = []
                 , _isDefs = []
                 , _isPending = []
                 }
    let eqnMap = multiMap [ (val psym, DefEqnGen (snd <$> lhs) rhs)
                          | Un.TermDef psym lhs rhs <- d
                          ]
    -- Parse imports and declarations.
    let actions = fmap (parseImport moduleMap) iml
               ++ fmap (parseDecl eqnMap) d
    is <- execStateT (sequenceOf_ folded actions) is0
    let tc = emptyTermContext (is^.isCtx)
    -- Execute pending assignments with final TermContext.
    sequence_ $ (($ tc) <$> is^.isPending)
    let mkFinal tps defs = m
          where cc = CCGlobal m
                m = flip (foldl insDef) (completeDef cc <$> defs)
                  $ flip (foldl insDataType) (completeDataType cc <$> tps)
                  $ is^.isModule
    mkFinal <$> traverse evalDataType (is^.isTypes)
            <*> traverse evalDef (is^.isDefs)

type VarCollector = State (Map Int (String, Term))

patVarInfo :: Pat Term -> VarCollector ()
patVarInfo = go
  where go (PVar nm i tp) = modify $ Map.insert i (nm,tp)
        go PUnused{} = return ()
        go (PTuple l)  = traverseOf_ folded go l
        go (PRecord m) = traverseOf_ folded go m
        go (PCtor _ l) = traverseOf_ folded go l

-- | Iterators over a structure of Pat Terms and returns corresponding
-- structure with TCpats.
liftTCPatT :: forall s f
            . Traversable f
           => TermContext s
           -> f (Pat Term) -> TC s (f TCPat, TermContext s)
liftTCPatT tc0 a = do
  let vinfo :: Vector (String,Term)
      vinfo = V.fromList $ Map.elems $ execState (traverse patVarInfo a) Map.empty
      fn (nm,tp) = do
        tc <- get
        tp' <- lift $ liftTCTerm tc tp
        let tc' = consBoundVar nm tp' tc
        (tp', tc') <$ put tc'
  (pairs,tcFinal) <- runStateT (traverse fn vinfo) tc0
  let boundTps = fst <$> pairs
      tcv = fmap snd pairs `V.snoc` tcFinal
  let go :: Pat Term -> TC s TCPat
      go (PVar nm i _) = return $ TCPVar nm (i, tp)
        where Just tp = boundTps V.!? i
      go (PUnused i tp) = do
        let Just tc = tcv V.!? i
        tp' <- liftTCTerm tc tp
        return $ TCPUnused "_" (i,tp')
      go (PTuple pl)  = TCPatF . UPTuple  <$> traverse go pl
      go (PRecord pm) = TCPatF . UPRecord <$> traverse go pm
      go (PCtor c pl) = TCPatF . UPCtor c <$> traverse go pl
  (,tcFinal) <$> traverse go a


liftEqn :: TermContext s -> DefEqn Term -> TC s TCDefEqn
liftEqn tc0 (DefEqn pl r) = do
  (pl', tc) <- liftTCPatT tc0 pl
  DefEqnGen pl' <$> liftTCTerm tc r

liftLocalDefs :: TermContext s -> [LocalDef Term] -> TC s ([TCLocalDef], TermContext s)
liftLocalDefs tc0 lcls = do
    (tps,pending) <- unzip <$> traverse tcLclType lcls
    let tc = consLocalDefs tps tc0
    traverseOf_ folded ($ tc) pending
    let mkDef (LocalFnDefGen nm tp r) = LocalFnDefGen nm tp <$> topEval r
    (,tc) <$> traverse mkDef tps
  where tcLclType (LocalFnDef nm tp0 eqs) = do
          tp <- liftTCTerm tc0 tp0
          r <- newRef nm
          let pendingFn tc = do
                assignRef r (traverse (liftEqn tc) eqs)
          return (LocalFnDefGen nm tp r, pendingFn)

liftTCTerm :: TermContext s -> Term -> TC s TCTerm
liftTCTerm tc (Term tf) =
  case tf of
    FTermF ftf -> TCF <$> traverse (liftTCTerm tc) ftf
    Lambda pat tp rhs -> do
       (Identity pat',tc') <- liftTCPatT tc (Identity pat)
       TCLambda pat' <$> liftTCTerm tc tp <*> liftTCTerm tc' rhs
    Pi nm tp rhs -> do
      tp' <- liftTCTerm tc tp
      let tc' = consBoundVar nm tp' tc
      TCPi (TCPVar nm (0, tp')) tp' <$> liftTCTerm tc' rhs
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
  FPPi (TCPVar nm (0, t')) t' <$> liftFixedType fn tc' r
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
mkPendingAssign r f a = assignRef r (f a)

data InitState s = IS { _isModule :: Module
                      , _isCtx :: GlobalContext s
                      , _isTypes :: ![ TCRefDataType s ] 
                      , _isDefs  :: ![ TCRefDef s ]
                      , _isPending :: [ PendingAction s (TermContext s) ]
                      }

isModule :: Simple Lens (InitState s) Module
isModule = lens _isModule (\s v -> s { _isModule = v })

isCtx :: Simple Lens (InitState s) (GlobalContext s)
isCtx = lens _isCtx (\s v -> s { _isCtx = v })

isTypes :: Simple Lens (InitState s) [TCRefDataType s] 
isTypes = lens _isTypes (\s v -> s { _isTypes = v })

isDefs :: Simple Lens (InitState s) [ TCRefDef s ]
isDefs = lens _isDefs (\s v -> s { _isDefs = v })

isPending :: Simple Lens (InitState s) [ PendingAction s (TermContext s) ]
isPending = lens _isPending (\s v -> s { _isPending = v })

type Initializer s a = StateT (InitState s) (TC s) a

initModuleName :: Initializer s ModuleName
initModuleName = moduleName <$> use isModule

addPending :: NodeName -> (TermContext s -> TC s r) -> Initializer s (TCRef s r)
addPending nm fn = do
  r <- lift $ newRef nm  
  r <$ (isPending %= (mkPendingAssign r fn :))

parseCtor :: Ident -> Un.CtorDecl -> Initializer s (Bool, Loc, TCRefCtor s)
parseCtor dt (Un.Ctor pnm utp) = do
  mnm <- initModuleName
  tp <- addPending (val pnm) (\tc -> tcCtorType dt tc utp)
  let ci = mkIdent mnm (val pnm)
  return (True, LocalLoc (pos pnm), Ctor { ctorName = ci, ctorType = tp })

parseDecl :: Map String [UnDefEqn] -> Un.Decl -> Initializer s ()
parseDecl eqnMap d = do
  mnm <- initModuleName
  case d of
    Un.TypeDecl idl utp -> do
      let id1:_ = idl
      rtp <- addPending (val id1) (\uc -> fst <$> tcType uc utp)
      forOf_ folded idl $ \(PosPair p nm) -> do
        let ueqs = fromMaybe [] $ Map.lookup nm eqnMap
        eqs <- addPending ("Equations for " ++ nm) $ \tc -> do
          tp <- eval p rtp
          eqs <- traverse (tcEqn tc tp) ueqs
          return eqs
        let def = DefGen (mkIdent mnm nm) rtp eqs
        isCtx  %= insertDef [Nothing] True (LocalLoc p) def
        isDefs %= (def:)
    Un.DataDecl psym utp ucl -> do
      let dti = mkIdent mnm (val psym)
      dtp <- addPending (val psym) (\tc -> tcDTType tc utp)
      cl  <- traverse (parseCtor dti) ucl
      let dt = DataTypeGen dti dtp cl
      isCtx   %= insertDataType [Nothing] True (LocalLoc (pos psym)) dt
      isTypes %= (DataTypeGen dti dtp (view _3 <$> cl):)
    Un.TermDef{} -> return ()

parseImport :: Map ModuleName Module
            -> Un.Import
            -> Initializer s ()
parseImport moduleMap (Un.Import q (PosPair p nm) mAsName mcns) = do
  case Map.lookup nm moduleMap of
    Nothing -> lift $ tcFail p $ "Cannot find module " ++ show nm ++ "."
    Just m -> do
      let mnm = moduleName m
      isModule %= insImport m 
      -- Get list of module names to use for local identifiers.
      let mnml | q = [Just qnm]
               | otherwise = [Nothing, Just qnm]
            where qnm = maybe (moduleName m)
                              (\s -> Un.mkModuleName [s])
                              (val <$> mAsName)
      let loc = ImportedLoc mnm p
      -- Add datatypes to module
      forOf_ folded (moduleDataTypes m) $ \dt -> do
        let dtnm = dtName dt
        dtr <- addPending (identName dtnm) $ \tc -> liftTCDataType tc (dtType dt)
        -- Add constructors to module.
        cl <- forOf traverse (dtCtors dt) $ \c -> do
          let cnm = ctorName c
              cfn tc = liftTCCtorType dtnm tc (ctorType c)
          let addInModule = includeNameInModule mcns cnm
          (addInModule,loc,) . Ctor cnm <$> addPending (identName cnm) cfn
        let dtuse = includeNameInModule mcns dtnm
        isCtx %= insertDataType mnml dtuse loc (DataTypeGen dtnm dtr cl)
      -- Add definitions to module.
      forOf_ folded (moduleDefs m) $ \def -> do
        let inm = identName (defIdent def)
        tpr <- addPending inm $ \tc ->
          liftTCTerm tc (defType def)
        eqr <- addPending inm $ \tc ->
          traverse (liftEqn tc) (defEqs def)
        let addInModule = includeNameInModule mcns (defIdent def)
        isCtx %= insertDef mnml addInModule loc (DefGen (defIdent def) tpr eqr)

_checkDef :: TCDef -> Maybe ()
_checkDef (DefGen _ (Identity tp) (Identity eqns)) = do
  checkTCTerm 0 tp
  traverseOf_ folded (checkDefEqn 0) eqns
