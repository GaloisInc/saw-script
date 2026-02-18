{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE LambdaCase #-}

{- |
Module      : SAWCore.Typechecker
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : saw@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module SAWCore.Typechecker
  ( inferCompleteTerm
  , tcInsertModule
  ) where

import Control.Monad (forM, forM_, guard, mzero, void, unless)
import Control.Monad.Except (ExceptT(..), runExceptT, catchError, throwError)
import Control.Monad.IO.Class (MonadIO(..))
import Control.Monad.Reader (ReaderT(..), asks, lift, local)
import Control.Monad.Trans.Maybe
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (mapMaybe)
import Data.Text (Text)
import qualified Data.Text as Text

import Prettyprinter hiding (Doc)

import qualified SAWSupport.Pretty as PPS (Doc, Opts, defaultOpts, render)

import SAWCore.Panic (panic)

import SAWCore.Module
  ( emptyModule
  , findDataTypeInMap
  , resolvedNameName
  , CtorArg(..)
  , DefQualifier(..)
  , DataType(dtName), ResolvedName, lookupVarIndexInMap, resolvedNameInfo
  )
import qualified SAWCore.Parser.AST as Un
import SAWCore.Name
import qualified SAWCore.QualName as QN
import SAWCore.Parser.Position
import SAWCore.Term.Functor
import SAWCore.Term.Pretty (ppTermPureDefaults)
import SAWCore.SharedTerm
import SAWCore.Recognizer
import qualified SAWCore.Term.Certified as SC

import Debug.Trace

-- | Infer the type of an untyped term and complete it to a 'Term'.
inferCompleteTerm ::
  SharedContext -> Maybe ModuleName -> Un.UTerm -> IO (Either PPS.Doc Term)
inferCompleteTerm sc mnm t =
  do res <- runTCM (typeInferCompleteUTerm t) sc mnm
     case res of
       Right t' -> pure (Right t')
       Left err ->
         do ne <- scGetNamingEnv sc
            let opts = PPS.defaultOpts
            pure (Left (prettyTCError opts ne err))

-- | Pretty-print a type-checking error
ppTCError :: TCError -> String
ppTCError e =
  PPS.render PPS.defaultOpts $
  prettyTCError PPS.defaultOpts emptyDisplayNameEnv e

-- | Pretty-print a type-checking error
prettyTCError :: PPS.Opts -> DisplayNameEnv -> TCError -> PPS.Doc
prettyTCError opts ne e = helper Nothing e where

  ppWithPos :: Maybe Pos -> [PPS.Doc] -> PPS.Doc
  ppWithPos maybe_p strs =
    case maybe_p of
      Just p -> vcat (pretty (ppPos p) : strs)
      Nothing -> vcat strs

  helper :: Maybe Pos -> TCError -> PPS.Doc
  helper mp err =
    case err of
      AmbiguousName str [] ->
        ppWithPos mp [ "Unbound name:" <+> pretty str ]
      AmbiguousName str rnms ->
        ppWithPos mp $ [ "Ambiguous name:" <+> pretty str, "Possible matches:"] ++
          map (pretty . toAbsoluteName . resolvedNameInfo) rnms
      EmptyVectorLit ->
        ppWithPos mp [ "Empty vector literal"]
      NoSuchDataType d ->
        -- Note: for now d is always an `Ident`; when it needs to be
        -- more general (`Name`), switch to the commented-out version.
        --let d' = prettyNameWithEnv opts ne d in
        let d' = pretty $ identText d in
        ppWithPos mp [ "No such data type:" <+> d' ]
      DeclError nm reason ->
        ppWithPos mp [ "Malformed declaration for" <+> pretty (show nm), pretty reason ]
      ErrorPos p err' ->
        helper (Just p) err'
      ErrorUTerm t err' ->
        ppWithPos mp [ "While typechecking term:"
                     , indent 2 $ Un.prettyUTerm t
                     , helper mp err'
                     ]
      TermError err' ->
        ppWithPos mp [ prettyTermError opts ne err' ]

----------------------------------------------------------------------
-- Type Checking Monad

-- | The 'ReaderT' environment for a computation to typecheck a
-- SAWCore parser AST.
data TCEnv =
  TCEnv
  { tcSharedContext :: SharedContext -- ^ the SAW context
  , tcModName :: Maybe ModuleName -- ^ the current module name
  , tcLocals :: Map LocalName (VarName, Term, Bool)
      -- ^ the mapping of display names to variables, flag is true if the term
      -- is the definition of the variable, false if the term is the variable type
  }

-- | Errors that can occur during type-checking
data TCError
  = AmbiguousName Text [ResolvedName]
  | EmptyVectorLit
  | NoSuchDataType Ident
  | DeclError Text String
  | ErrorPos Pos TCError
  | ErrorUTerm Un.UTerm TCError
  | TermError SC.TermError

-- | The monad for computations to typecheck a SAWCore parser AST.
newtype TCM a = TCM (ReaderT TCEnv (ExceptT TCError IO) a)
  deriving (Functor, Applicative, Monad, MonadIO)

runTCM ::
  TCM a -> SharedContext -> Maybe ModuleName -> IO (Either TCError a)
runTCM (TCM m) sc mnm =
  runExceptT (runReaderT m (TCEnv sc mnm Map.empty))

-- | Read the current module name
askSharedContext :: TCM SharedContext
askSharedContext = TCM (asks tcSharedContext)

-- | Read the current module name
askModName :: TCM (Maybe ModuleName)
askModName = TCM (asks tcModName)

-- | Read the current context of named variables
askLocals :: TCM (Map LocalName (VarName, Term, Bool))
askLocals = TCM (asks tcLocals)

-- | Look up the current module name, raising an error if it is not set
getModuleName :: TCM ModuleName
getModuleName =
  do maybe_modname <- askModName
     case maybe_modname of
       Just mnm -> return mnm
       Nothing ->
         panic "getModuleName" ["Current module name not set during typechecking"]

-- | Throw a type-checking error.
throwTCError :: TCError -> TCM a
throwTCError e = TCM (throwError e)

-- | Augment and rethrow any 'TCError' thrown by the given computation.
rethrowTCError :: (TCError -> TCError) -> TCM a -> TCM a
rethrowTCError f (TCM m) = TCM (catchError m (throwError . f))

-- | Run a type-checking computation @m@ and tag any error it throws with the
-- 'ErrorUTerm' constructor.
withErrorUTerm :: Un.UTerm -> TCM a -> TCM a
withErrorUTerm t = rethrowTCError (ErrorUTerm t)

-- | Run a type-checking computation @m@ and tag any error it throws with the
-- given position, using the 'ErrorPos' constructor, unless that error is
-- already tagged with a position.
atPos :: Pos -> TCM a -> TCM a
atPos p = rethrowTCError (ErrorPos p)

-- | Lift a computation from the SAWCore term-building monad 'SC.SCM'
-- into 'TCM'.
liftSCM :: SC.SCM a -> TCM a
liftSCM m =
  do sc <- askSharedContext
     result <- liftIO $ SC.runSCM sc m
     case result of
       Left e -> throwTCError (TermError e)
       Right x -> pure x

----------------------------------------------------------------------

-- | Resolve a name.
inferResolveName :: Text -> TCM Term
inferResolveName n =
  inferResolveQualName $ QN.QualName [] [] n Nothing Nothing

-- | Resolve a name to a locally-bound variable
resolveLocalName :: Text -> TCM (Maybe Term)
resolveLocalName n = do
  nctx <- askLocals
  case Map.lookup n nctx of
    Just (vn, t, is_def) ->
      case is_def of
        True -> return $ Just t
        False -> Just <$> (liftSCM $ SC.scmVariable vn t)
    Nothing -> return Nothing

-- | Resolve a name to a list of possible globals
resolveGlobalName :: Text -> TCM [ResolvedName]
resolveGlobalName n = do
  sc <- askSharedContext
  env <- liftIO $ scGetNamingEnv sc
  mm <- liftIO $ scGetModuleMap sc
  let vis = resolveDisplayName env n
  return $ mapMaybe (\vi -> lookupVarIndexInMap vi mm) vis

-- | Resolve a partially qualified name
inferResolveQualName :: QN.QualName -> TCM Term
inferResolveQualName qn = do
  let n = QN.ppQualName qn
  resolveLocalName n >>= \case
    Just t -> return t
    Nothing -> resolveGlobalName n >>= \case
      [rn] -> rnToTerm rn
      rns -> resolveAliases qn >>= \case
        Just t -> return t
        Nothing | Nothing <- QN.namespace qn ->
          resolveAliases (qn { QN.namespace = Just QN.NamespaceCore }) >>= \case
            Just t -> return t
            Nothing -> throwTCError $ AmbiguousName n rns
        _ -> throwTCError $ AmbiguousName n rns
  where
    rnToTerm rn = do
      let c = resolvedNameName rn
      liftSCM $ SC.scmConst c

    resolveAliases q = uniqueGlobal (reverse (QN.aliases q))

    uniqueGlobal (n:ns) = resolveGlobalName n >>= \case
      [rn] -> Just <$> rnToTerm rn
      _ -> uniqueGlobal ns
    uniqueGlobal [] = return Nothing

-- | The debugging level
debugLevel :: Int
debugLevel = 0

-- | Print debugging output if 'debugLevel' is greater than 0
typeInferDebug :: String -> TCM ()
typeInferDebug str | debugLevel > 0 = liftIO $ traceIO str
typeInferDebug _ = return ()

-- | Completely typecheck an untyped SAWCore AST.
typeInferCompleteUTerm :: Un.UTerm -> TCM Term
typeInferCompleteUTerm t =
  do typeInferDebug ("typechecking term: " ++ show t)
     res <- atPos (pos t) $ withErrorUTerm t $ typeInferCompleteTerm t
     ty <- liftSCM $ SC.scmTypeOf res
     sc <- askSharedContext
     ty' <- liftIO $ ppTerm sc PPS.defaultOpts ty
     typeInferDebug ("completed typechecking term: " ++ show t ++ "\n"
                     ++ "type = " ++ ty')
     return res

-- | Main workhorse function for type inference on untyped terms
typeInferCompleteTerm :: Un.UTerm -> TCM Term
typeInferCompleteTerm uterm =
  case uterm of
    Un.Name (PosPair _ n) ->
      inferResolveName n
    Un.QName (PosPair _ n) ->
      inferResolveQualName n

    Un.Sort _ srt h ->
      liftSCM $ SC.scmSortWithFlags srt h

    Un.Recursor (PosPair _ str) s ->
      do mnm <- getModuleName
         sc <- askSharedContext
         mm <- liftIO $ scGetModuleMap sc
         let dt_ident = mkIdent mnm str
         dt <- case findDataTypeInMap dt_ident mm of
           Just d -> return d
           Nothing -> throwTCError $ NoSuchDataType dt_ident
         liftSCM $ SC.scmRecursor (dtName dt) s

    Un.App f arg ->
      -- Only call typeInferCompleteUTerm on the function arguments, to
      -- avoid adding too many 'atPos' and 'withErrorUTerm' annotations.
      do f' <- typeInferCompleteTerm f
         arg' <- typeInferCompleteUTerm arg
         liftSCM $ SC.scmApply f' arg'

    Un.Lambda _ [] t ->
      typeInferCompleteUTerm t
    Un.Lambda p ((Un.termVarLocalName -> x, tp) : ctx) t ->
      do tp_trm <- typeInferCompleteUTerm tp
         _ <- liftSCM $ SC.scmEnsureSortType tp_trm
         vn <- liftSCM $ SC.scmFreshVarName x
         -- Don't call typeInferCompleteUTerm with a suffix of the
         -- original variable context, to avoid adding too many
         -- 'withErrorUTerm' annotations.
         body <- withVar x vn tp_trm $
           typeInferCompleteTerm $ Un.Lambda p ctx t
         liftSCM $ SC.scmLambda vn tp_trm body

    Un.Let _ [] t ->
      typeInferCompleteUTerm t
    Un.Let p ( PosPair _ ((nm,midx), def) : bs) t ->
      do let qn = QN.QualName [] [] nm midx Nothing
         let x = QN.ppQualName qn
         vn <- liftSCM $ SC.scmFreshVarName x
         def' <- typeInferCompleteUTerm def
         withDefinedVar x vn def' $
           typeInferCompleteTerm $ Un.Let p bs t

    Un.Pi _ [] t ->
      typeInferCompleteUTerm t
    Un.Pi p ((Un.termVarLocalName -> x, tp) : ctx) t ->
      do tp' <- typeInferCompleteUTerm tp
         vn <- liftSCM $ SC.scmFreshVarName x
         -- Don't call typeInferCompleteUTerm with a suffix of the
         -- original variable context, to avoid adding too many
         -- 'withErrorUTerm' annotations.
         body <- withVar x vn tp' $
           typeInferCompleteTerm $ Un.Pi p ctx t
         liftSCM $ SC.scmPi vn tp' body

    Un.RecordValue _ elems ->
      do typed_elems <-
           mapM (\(PosPair _ fld, t) -> (fld,) <$> typeInferCompleteUTerm t) elems
         liftSCM $ SC.scmRecordValue typed_elems
    Un.RecordType _ elems ->
      do typed_elems <-
           mapM (\(PosPair _ fld, t) -> (fld,) <$> typeInferCompleteUTerm t) elems
         liftSCM $ SC.scmRecordType typed_elems
    Un.RecordProj t prj ->
      do t' <- typeInferCompleteUTerm t
         liftSCM $ SC.scmRecordSelect t' prj

    Un.UnitValue _ ->
      liftSCM $ SC.scmUnitValue
    Un.UnitType _ ->
      liftSCM $ SC.scmUnitType

    Un.PairValue _ t1 t2 ->
      do t1' <- typeInferCompleteUTerm t1
         t2' <- typeInferCompleteUTerm t2
         liftSCM $ SC.scmPairValue t1' t2'
    Un.PairType _ t1 t2 ->
      do t1' <- typeInferCompleteUTerm t1
         t2' <- typeInferCompleteUTerm t2
         liftSCM $ SC.scmPairType t1' t2'
    Un.PairLeft t ->
      do t' <- typeInferCompleteUTerm t
         liftSCM $ SC.scmPairLeft t'
    Un.PairRight t ->
      do t' <- typeInferCompleteUTerm t
         liftSCM $ SC.scmPairRight t'

    Un.TypeConstraint t _ tp ->
      do t' <- typeInferCompleteUTerm t
         tp' <- typeInferCompleteUTerm tp
         liftSCM $ SC.scmAscribe t' tp'

    Un.NatLit _ i ->
      liftSCM $ SC.scmNat i
    Un.StringLit _ str ->
      liftSCM $ SC.scmString str
    Un.VecLit _ ts ->
      do typed_ts <- mapM typeInferCompleteUTerm ts
         typed_tp <-
           case typed_ts of
             (t1:_) -> liftSCM $ SC.scmTypeOf t1
             [] -> throwTCError $ EmptyVectorLit
         liftSCM $ SC.scmVector typed_tp typed_ts
    Un.BVLit _ bits ->
      do tp <- liftSCM $ SC.scmGlobalDef "Prelude.Bool"
         let bit b = SC.scmGlobalDef (if b then "Prelude.True" else "Prelude.False")
         bit_tms <- liftSCM $ traverse bit bits
         liftSCM $ SC.scmVector tp bit_tms

    Un.BadTerm _ ->
      -- Should be unreachable, since BadTerms represent parse errors, that should
      -- already have been signaled before type inference
      panic "typeInferCompleteTerm" ["Type inference encountered a BadTerm"]


--
-- Type-checking modules
--

-- | Type-check a list of declarations and insert them into the current module
processDecls :: [Un.Decl] -> TCM ()
processDecls [] = return ()

processDecls (Un.InjectCodeDecl ns txt : rest) =
  do mnm <- getModuleName
     sc <- askSharedContext
     liftIO $ scInjectCode sc mnm ns txt
     processDecls rest

processDecls (Un.TypedDef nm params rty body : rest) =
  processDecls (Un.TypeDecl NoQualifier nm (Un.Pi (pos nm) params rty) :
                Un.TermDef nm (map fst params) body : rest)

processDecls (Un.TypeDecl NoQualifier (PosPair p nm) tp :
              Un.TermDef (PosPair _ ((== nm) -> True)) vars body : rest) =
  -- Type-checking for definitions
  (atPos p $
   do
     sc <- askSharedContext
     -- Step 1: type-check the type annotation, and make sure it is a type
     typed_tp <- typeInferCompleteUTerm tp
     void $ liftSCM $ SC.scmEnsureSortType typed_tp
     let def_tp = typed_tp
     def_tp_whnf <- liftIO $ scWhnf sc def_tp

     -- Step 2: assign types to the bound variables of the definition, by
     -- peeling off the pi-abstraction variables in the type annotation. Any
     -- remaining body of the pi-type is the required type for the def body.
     matchResult <-
       runMaybeT $ matchPiWithNames (map Un.termVarLocalName vars) def_tp_whnf
     (ctx, req_body_tp) <-
       case matchResult of
         Just x -> return x
         Nothing ->
             throwTCError $
             DeclError nm ("More variables " ++ show (map Un.termVarLocalName vars) ++
                           " than length of function type:\n" ++
                           ppTermPureDefaults typed_tp)

     -- Step 3: type-check the body of the definition in the context of its
     -- variables, and build a function that takes in those variables
     def_tm <-
       withCtx ctx $
       do body' <- typeInferCompleteUTerm body
          body_ty <- liftSCM $ SC.scmTypeOf body'
          ok <- liftIO $ scSubtype sc body_ty req_body_tp
          unless ok $ throwTCError (TermError (SC.AscriptionNotSubtype req_body_tp body'))
          let vts = map (\(_, v, t) -> (v, t)) ctx
          result <- liftIO $ scLambdaList sc vts body'
          liftSCM $ SC.scmAscribe result def_tp

     -- Step 4: add the definition to the current module
     mnm <- getModuleName
     let nmi = ModuleIdentifier (mkIdent mnm nm)
     void $ liftIO $ scDefineConstant sc nmi def_tm) >>
  processDecls rest

processDecls (Un.TypeDecl NoQualifier (PosPair p nm) _ : _) =
  atPos p $ throwTCError $ DeclError nm "Definition without defining equation"

processDecls (Un.TypeDecl _ (PosPair p nm) _ :
              Un.TermDef (PosPair _ ((== nm) -> True)) _ _ : _) =
  atPos p $ throwTCError $ DeclError nm "Primitive or axiom with definition"

processDecls (Un.TypeDecl q (PosPair p nm) tp : rest) =
  (atPos p $
   do typed_tp <- typeInferCompleteUTerm tp
      void $ liftSCM $ SC.scmEnsureSortType typed_tp
      mnm <- getModuleName
      let ident = mkIdent mnm nm
      let def_tp = typed_tp
      sc <- askSharedContext
      liftIO $ scDeclarePrim sc ident q def_tp) >>
  processDecls rest

processDecls (Un.TermDef (PosPair p nm) _ _ : _) =
  atPos p $ throwTCError $ DeclError nm "Dangling definition without a type"

processDecls (Un.DataDecl nm param_ctx dt_tp c_decls : rest) =
  do processDataDecl nm param_ctx dt_tp c_decls
     processDecls rest

-- | Type-check a data type declaration and insert it into the current module.
processDataDecl :: PosPair Text -> Un.UTermCtx -> Un.UTerm -> [Un.CtorDecl] -> TCM ()
processDataDecl (PosPair p nm) param_ctx dt_tp c_decls =
  let param_ctx' = map (\(x, t) -> (Un.termVarLocalName x, t)) param_ctx in
  atPos p $
  -- Step 1: type-check the parameters
  typeInferCompleteInCtx param_ctx' $ \params -> do
  let dtParams = map (\(_, v, t, _) -> (v, t)) params
  let err :: String -> TCM a
      err msg = throwTCError $ DeclError nm msg

  -- Step 2: type-check the type given for d, and make sure it is of the form
  -- (i1:ix1) -> ... -> (in:ixn) -> Type s for some sort s. Then form the full
  -- type of d as (p1:param1) -> ... -> (i1:ix1) -> ... -> Type s
  (dt_ixs, dtSort) <-
    case Un.asPiList dt_tp of
      (ixs, Un.Sort _ s h) | h == noFlags ->
        return (ixs, s) -- NB, don't allow `isort`, etc.
      _ -> err "Wrong form for type of datatype"
  let dt_ixs' = map (\(x, t) -> (Un.termVarLocalName x, t)) dt_ixs
  dt_ixs_typed <- typeInferCompleteCtx dt_ixs'
  let dtIndices = map (\(_, v, t, _) -> (v, t)) dt_ixs_typed

  -- Step 3: Declare d as a free variable, so we can typecheck the constructors
  dtType <- liftSCM $ SC.scmPiList (dtParams ++ dtIndices) =<< SC.scmSort dtSort
  dtVarName <- liftSCM $ SC.scmFreshVarName nm

  -- Step 4: typecheck the constructors, and build Ctors for them
  typed_ctors <-
    withVar nm dtVarName dtType $
    mapM (\(Un.Ctor (PosPair p' c) ctx body) ->
           (c,) <$> typeInferCompleteUTerm (Un.Pi p' ctx body)) c_decls
  mnm <- getModuleName
  ctors <-
    withVar nm dtVarName dtType $
    forM typed_ctors $ \(c, tp) ->
    do let nmi = ModuleIdentifier (mkIdent mnm c)
       let result = mkCtorSpec nmi dtVarName dtParams dtIndices tp
       case result of
         Just spec -> pure spec
         Nothing -> err ("Malformed type form constructor: " ++ show c)

  -- Step 5: Declare the datatype with the given ctors
  motiveName <- liftSCM $ SC.scmFreshVarName "p"
  argName <- liftSCM $ SC.scmFreshVarName "arg"
  let dts =
        SC.DataTypeSpec
        { SC.dtsNameInfo = ModuleIdentifier (mkIdent mnm nm)
        , SC.dtsParams = dtParams
        , SC.dtsIndices = dtIndices
        , SC.dtsSort = dtSort
        , SC.dtsCtors = ctors
        , SC.dtsMotiveName = motiveName
        , SC.dtsArgName = argName
        }
  void $ liftSCM $ SC.scmDefineDataType dts


-- | Typecheck a module and, on success, insert it into the current context
tcInsertModule :: SharedContext -> Un.Module -> IO ()
tcInsertModule sc (Un.Module (PosPair _ mnm) imports decls) = do
  -- First, insert an empty module for mnm
  scLoadModule sc $ emptyModule mnm
  -- Next, process all the imports
  forM_ imports $ \imp ->
    do let imn = val $ Un.importModName imp
       i_exists <- scModuleIsLoaded sc imn
       unless i_exists $ fail $ "Imported module not found: " ++ show imn
       scImportModule sc (Un.nameSatsConstraint (Un.importConstraints imp) . Text.unpack) imn mnm
  -- Finally, process all the decls
  decls_res <- runTCM (processDecls decls) sc (Just mnm)
  case decls_res of
    Left err -> fail $ ppTCError err
    Right _ -> return ()


--
-- Helper functions for type-checking modules
--

-- | Pattern match a nested pi-abstraction, like 'asPiList', but only match as
-- far as the supplied list of variables, and use them as the new names
matchPiWithNames ::
  [LocalName] -> Term -> MaybeT TCM ([(LocalName, VarName, Term)], Term)
matchPiWithNames [] tp = pure ([], tp)
matchPiWithNames (var : vars) tp =
  case asPi tp of
    Nothing -> mzero
    Just (x, arg_tp, body_tp) ->
      do vn <-
           if IntSet.member (vnIndex x) (freeVars body_tp)
           then -- dependent function type: use name from Pi type
             pure x
           else -- non-dependent function: use 'var' as base name
             lift $ liftSCM $ SC.scmFreshVarName var
         (ctx, body) <- matchPiWithNames vars body_tp
         pure ((var, vn, arg_tp) : ctx, body)

withVar' :: LocalName -> VarName -> Term -> Bool -> TCM a -> TCM a
withVar' x vn tp b (TCM m) =
  TCM $
  local (\env -> env { tcLocals = Map.insert x (vn, tp, b) (tcLocals env) }) m

-- | Run a type-checking computation in a typing context extended with a new
-- variable with the given name and type.
withVar :: LocalName -> VarName -> Term -> TCM a -> TCM a
withVar x vn tp f = withVar' x vn tp False f

-- | Run a type-checking computation in a typing context extended with a new
-- variable with the given name and definition.
withDefinedVar :: LocalName -> VarName -> Term -> TCM a -> TCM a
withDefinedVar x vn tp f = withVar' x vn tp True f

-- | Run a type-checking computation in a typing context extended by a list of
-- variables and their types. See 'withVar'.
withCtx :: [(LocalName, VarName, Term)] -> TCM a -> TCM a
withCtx = flip (foldr (\(x, vn, tp) -> withVar x vn tp))

-- | Perform type inference on a context, i.e., a list of variable names and
-- their associated types. This will give us 'Term's for each type, as
-- well as their 'Sort's, since the type of any type is a 'Sort'.
typeInferCompleteCtx ::
  [(LocalName, Un.UTerm)] -> TCM [(LocalName, VarName, Term, Sort)]
typeInferCompleteCtx [] = pure []
typeInferCompleteCtx ((x, tp) : ctx) =
  do tp' <- typeInferCompleteUTerm tp
     s <- liftSCM $ SC.scmEnsureSortType tp'
     vn <- liftSCM $ SC.scmFreshVarName x
     ctx' <- withVar x vn tp' (typeInferCompleteCtx ctx)
     pure ((x, vn, tp', s) : ctx')

-- | Perform type inference on a context via 'typeInferCompleteCtx', and then
-- run a computation in that context via 'withCtx', also passing in that context
-- to the computation
typeInferCompleteInCtx ::
  [(LocalName, Un.UTerm)] ->
  ([(LocalName, VarName, Term, Sort)] -> TCM a) -> TCM a
typeInferCompleteInCtx ctx f =
  do typed_ctx <- typeInferCompleteCtx ctx
     withCtx (map (\(x, v, t, _) -> (x, v, t)) typed_ctx) (f typed_ctx)

--------------------------------------------------------------------------------
-- Recognizers for constructor types


-- | Test if a 'Term' is an application of a specific datatype with the
-- supplied context of parameters and indices
ctxAsDataTypeApp ::
  VarName -> [param] -> [index] -> Term -> Maybe ([Term], [Term])
ctxAsDataTypeApp d params ixs t =
  do let (f, args) = asApplyAll t
     (d', _) <- asVariable f
     guard (d == d')
     guard (length args == length params + length ixs)
     let (params', ixs') = splitAt (length params) args
     pure (params', ixs')

-- | Test whether a specific datatype occurs in a term.
usesDataType :: VarName -> Term -> Bool
usesDataType d t = IntMap.member (vnIndex d) (varTypes t)

-- | Check that a type is a valid application of datatype @d@ for use in
-- specific ways in the type of a constructor for @d@. This requires that this
-- application of @d@ be of the form
--
-- > d p1 .. pn x1 .. xm
--
-- where the @pi@ are the distinct bound variables bound in the @params@
-- context, given as argument, and that the @xj@ have no occurrences of @d@. If
-- the given type is of this form, return the @xj@.
asCtorDTApp :: VarName -> [(VarName, Term)] -> [index] -> Term -> Maybe [Term]
asCtorDTApp d params dt_ixs (ctxAsDataTypeApp d params dt_ixs ->
                                       Just (param_vars, ixs))
  | isVarList (map fst params) param_vars && not (any (usesDataType d) ixs)
  = Just ixs
  where
    -- Check that the given list of terms is a list of named
    -- variables, one for each parameter
    isVarList :: [VarName] -> [Term] -> Bool
    isVarList _ [] = True
    isVarList (p : ps) ((asVariable -> Just (x, _)) : ts) =
      x == p && isVarList ps ts
    isVarList _ _ = False
asCtorDTApp _ _ _ _ = Nothing


-- | Check that an argument for a constructor has one of the allowed forms
asCtorArg ::
  VarName ->
  [(VarName, Term)] ->
  [index] ->
  Term ->
  Maybe CtorArg
asCtorArg d _ _ tp
  | not (usesDataType d tp)
  = Just (ConstArg tp)
asCtorArg d params dt_ixs tp =
  do let (zs, ret) = asPiList tp
     case asCtorDTApp d params dt_ixs ret of
       Just ixs
         | not (any (usesDataType d . snd) zs) ->
           Just (RecursiveArg zs ixs)
       _ ->
         Nothing

-- | Check that a constructor type is a pi-abstraction that takes as input an
-- argument of one of the allowed forms described by 'CtorArg'
asPiCtorArg ::
  VarName ->
  [(VarName, Term)] ->
  [index] ->
  Term ->
  Maybe (VarName, CtorArg, Term)
asPiCtorArg d params dt_ixs t =
  case asPi t of
    Nothing -> Nothing
    Just (nm, tp, rest) ->
      case asCtorArg d params dt_ixs tp of
        Nothing -> Nothing
        Just arg -> Just (nm, arg, rest)

-- | Helper function for 'mkCtorArgStruct'
mkCtorArgsIxs ::
  VarName ->
  [(VarName, Term)] ->
  [index] ->
  Term ->
  Maybe ([(VarName, CtorArg)], [Term])
mkCtorArgsIxs d params dt_ixs (asCtorDTApp d params dt_ixs -> Just ixs) =
  Just ([], ixs)
mkCtorArgsIxs d params dt_ixs ty =
  case asPiCtorArg d params dt_ixs ty of
    Nothing -> Nothing
    Just (x, arg, rest) ->
      case mkCtorArgsIxs d params dt_ixs rest of
        Nothing -> Nothing
        Just (args, ixs) -> Just ((x, arg) : args, ixs)

-- | Take in a datatype and bindings lists for its parameters and indices, and
-- also a prospective type of a constructor for that datatype, where the
-- constructor type is allowed to have the parameters but not the indices free.
-- Test that the constructor type is an allowed type for a constructor of this
-- datatype, and, if so, build a 'CtorSpec' for it.
mkCtorSpec ::
  NameInfo ->
  VarName ->
  [(VarName, Term)] ->
  [(VarName, Term)] ->
  Term ->
  Maybe CtorSpec
mkCtorSpec nmi d params dt_ixs ctor_tp =
  case mkCtorArgsIxs d params dt_ixs ctor_tp of
    Nothing -> Nothing
    Just (args, ctor_ixs) ->
      Just (CtorSpec nmi args ctor_ixs)
