{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

{- |
Module      : SAWCore.Typechecker
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : jhendrix@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module SAWCore.Typechecker
  ( inferCompleteTerm
  , tcInsertModule
  ) where

import Control.Monad (forM, forM_, mzero, void, unless)
import Control.Monad.Except
import Control.Monad.IO.Class (MonadIO(..))
import Control.Monad.Reader (ReaderT(..), asks, lift, local)
import Control.Monad.Trans.Maybe
import qualified Data.IntSet as IntSet
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Text (Text)
import qualified Data.Text as Text

import Prettyprinter hiding (Doc)

import qualified SAWSupport.Pretty as PPS (Doc, defaultOpts, render)

import SAWCore.Panic (panic)

import SAWCore.Module
  ( emptyModule
  , findDataTypeInMap
  , resolveNameInMap
  , resolvedNameName
  , DefQualifier(..)
  , DataType(dtName)
  )
import qualified SAWCore.Parser.AST as Un
import SAWCore.Name
import SAWCore.Parser.Position
import SAWCore.Term.Functor
import SAWCore.Term.CtxTerm
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
       -- TODO: avoid intermediate 'String's from 'prettyTCError'
       Left err -> return $ Left $ vsep $ map pretty $ prettyTCError err
       Right t' -> return $ Right t'

-- | Pretty-print a type-checking error
prettyTCError :: TCError -> [String]
prettyTCError e = helper Nothing e where

  ppWithPos :: Maybe Pos -> [String] -> [String]
  ppWithPos maybe_p strs =
    case maybe_p of
      Just p -> ppPos p : strs
      Nothing -> strs

  helper :: Maybe Pos -> TCError -> [String]
  helper mp err =
    case err of
      UnboundName str ->
        ppWithPos mp [ "Unbound name: " ++ show str ]
      EmptyVectorLit ->
        ppWithPos mp [ "Empty vector literal"]
      NoSuchDataType d ->
        ppWithPos mp [ "No such data type: " ++ show d ]
      DeclError nm reason ->
        ppWithPos mp [ "Malformed declaration for " ++ show nm, reason ]
      ErrorPos p err' ->
        helper (Just p) err'
      ErrorUTerm t err' ->
        ppWithPos mp [ "While typechecking term:"
                     , indent2 $ PPS.render PPS.defaultOpts (Un.prettyUTerm t)
                     ]
        ++ helper mp err'
      TermError err' ->
        ppWithPos mp [showTermError err']

  -- | Add prefix to every line, but remove final trailing newline
  indent2 :: String -> String
  indent2 s = init (unlines (map ("  " ++) (lines s)))

----------------------------------------------------------------------
-- Type Checking Monad

-- | The 'ReaderT' environment for a computation to typecheck a
-- SAWCore parser AST.
data TCEnv =
  TCEnv
  { tcSharedContext :: SharedContext -- ^ the SAW context
  , tcModName :: Maybe ModuleName -- ^ the current module name
  , tcLocals :: Map LocalName (VarName, Term) -- ^ the mapping of display names to variables
  }

-- | Errors that can occur during type-checking
data TCError
  = UnboundName Text
  | EmptyVectorLit
  | NoSuchDataType NameInfo
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
askLocals :: TCM (Map LocalName (VarName, Term))
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
  do nctx <- askLocals
     mnm <- getModuleName
     sc <- askSharedContext
     mm <- liftIO $ scGetModuleMap sc
     let ident = mkIdent mnm n
     case (Map.lookup n nctx, resolveNameInMap mm ident) of
       (Just (vn, tp), _) ->
         liftSCM $ SC.scmVariable vn tp
       (_, Just rn) ->
         do let c = resolvedNameName rn
            liftSCM $ SC.scmConst c
       (Nothing, Nothing) ->
         throwTCError $ UnboundName n

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
     typeInferDebug ("completed typechecking term: " ++ show t ++ "\n"
                     ++ "type = " ++ show ty)
     return res

-- | Main workhorse function for type inference on untyped terms
typeInferCompleteTerm :: Un.UTerm -> TCM Term
typeInferCompleteTerm uterm =
  case uterm of
    Un.Name (PosPair _ n) ->
      inferResolveName n

    Un.Sort _ srt h ->
      liftSCM $ SC.scmSortWithFlags srt h

    Un.Recursor (PosPair _ str) s ->
      do mnm <- getModuleName
         sc <- askSharedContext
         mm <- liftIO $ scGetModuleMap sc
         let dt_ident = mkIdent mnm str
         dt <- case findDataTypeInMap dt_ident mm of
           Just d -> return d
           Nothing -> throwTCError $ NoSuchDataType (ModuleIdentifier dt_ident)
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
         body <- withVar x vn tp_trm $
           typeInferCompleteUTerm $ Un.Lambda p ctx t
         liftSCM $ SC.scmLambda vn tp_trm body

    Un.Pi _ [] t ->
      typeInferCompleteUTerm t
    Un.Pi p ((Un.termVarLocalName -> x, tp) : ctx) t ->
      do tp' <- typeInferCompleteUTerm tp
         vn <- liftSCM $ SC.scmFreshVarName x
         body <- withVar x vn tp' $
           typeInferCompleteUTerm $ Un.Pi p ctx t
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
          unless ok $ throwTCError (TermError (SC.ApplyNotSubtype req_body_tp body')) -- FIXME: Wrong error
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
  let param_sort = maxSort (map (\(_, _, _, s) -> s) params)
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
      ixs_max_sort = maxSort (map (\(_, _, _, s) -> s) dt_ixs_typed)

  -- Step 3: do the necessary universe inclusion checking for any predicative
  -- (non-Prop) inductive type, which includes:
  --
  -- 1. All ix types must be of sort dtSort; AND
  -- 2. All param types must be of sort dtSort+1
  if dtSort /= propSort && param_sort > sortOf dtSort then
    err ("Universe level of parameters should be no greater" ++
         " than that of the datatype")
    else return ()
  if dtSort /= propSort && ixs_max_sort > dtSort then
    err ("Universe level of indices should be strictly contained" ++
         " in that of the datatype")
    else return ()

  -- Step 4: Add d as an empty datatype, so we can typecheck the constructors
  mnm <- getModuleName
  let dtIdent = mkIdent mnm nm
  pn <- liftSCM $ SC.scmBeginDataType dtIdent dtParams dtIndices dtSort

  -- Step 5: typecheck the constructors, and build Ctors for them
  typed_ctors <-
    mapM (\(Un.Ctor (PosPair p' c) ctx body) ->
           (c,) <$> typeInferCompleteUTerm (Un.Pi p' ctx body)) c_decls
  sc <- askSharedContext
  ctors <-
    forM typed_ctors $ \(c, typed_tp) ->
    -- Check that the universe level of the type of each constructor
    do case termSortOrType typed_tp of
           Left ctor_sort
             | dtSort /= propSort && ctor_sort > dtSort ->
               err ("Universe level of constructors should be strictly" ++
                    " contained in that of the datatype")
           Left _ ->
               return ()
           Right ty ->
               panic "processDecls" [
                   "Type of the type of constructor is not a sort!",
                   "Constructor type: " <> Text.pack (ppTermPureDefaults typed_tp),
                   "Type of that type: " <> Text.pack (ppTermPureDefaults ty)
               ]
       let tp = typed_tp
       let result = mkCtorArgStruct pn dtParams dtIndices tp
       case result of
         Just arg_struct ->
           liftIO $ scBuildCtor sc pn (mkIdent mnm c) arg_struct
         Nothing -> err ("Malformed type form constructor: " ++ show c)

  -- Step 6: complete the datatype with the given ctors
  liftSCM $ SC.scmCompleteDataType dtIdent ctors


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
    Left err -> fail $ unlines $ prettyTCError err
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

-- | Run a type-checking computation in a typing context extended with a new
-- variable with the given name and type.
withVar :: LocalName -> VarName -> Term -> TCM a -> TCM a
withVar x vn tp (TCM m) =
  TCM $
  local (\env -> env { tcLocals = Map.insert x (vn, tp) (tcLocals env) }) m

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
