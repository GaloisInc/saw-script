{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs  #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE RecordWildCards #-}

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
  , inferCompleteTermCtx
  , tcInsertModule
  ) where

import Control.Monad (forM, forM_, void, unless)
import Control.Monad.IO.Class (MonadIO(..))
import Control.Monad.Reader (ReaderT(..), asks, lift, local)
import Data.List (findIndex)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Vector as V

import Prettyprinter hiding (Doc)

import qualified SAWSupport.Pretty as PPS (Doc)

import SAWCore.Panic (panic)

import SAWCore.Module
  ( emptyModule
  , findDataTypeInMap
  , resolveNameInMap
  , resolvedNameName
  , DataType(..)
  , DefQualifier(..)
  )
import SAWCore.Name (Name(..))
import qualified SAWCore.Parser.AST as Un
import SAWCore.Parser.Position
import SAWCore.Term.Functor
import SAWCore.Term.CtxTerm
import SAWCore.Term.Pretty (showTerm)
import SAWCore.SharedTerm
import SAWCore.Recognizer
import SAWCore.SCTypeCheck (SCTypedTerm, typedVal, typedType, TCError(..), atPos, throwTCError)
import qualified SAWCore.SCTypeCheck as TC

import Debug.Trace

-- | Infer the type of an untyped term and complete it to a 'Term', all in the
-- empty typing context
inferCompleteTerm :: SharedContext -> Maybe ModuleName -> Un.UTerm ->
                     IO (Either PPS.Doc Term)
inferCompleteTerm sc mnm t = inferCompleteTermCtx sc mnm [] t

-- | Infer the type of an untyped term and complete it to a 'Term' in a given
-- typing context
inferCompleteTermCtx ::
  SharedContext -> Maybe ModuleName -> [(LocalName, Term)] ->
  Un.UTerm -> IO (Either PPS.Doc Term)
inferCompleteTermCtx sc mnm ctx t =
  do res <- runCheckM (typeInferCompleteUTerm t) sc mnm ctx
     case res of
       -- TODO: avoid intermediate 'String's from 'prettyTCError'
       Left err -> return $ Left $ vsep $ map pretty $ TC.prettyTCError err
       Right t' -> return $ Right $ typedVal t'


-- | The 'ReaderT' environment for a computation to typecheck a
-- SAWCore parser AST.
data CheckEnv =
  CheckEnv
  { tcModName :: Maybe ModuleName -- ^ the current module name
  , tcCtxEC :: Map LocalName (ExtCns Term) -- ^ the mapping of names to named variables
  }

-- | The monad for computations to typecheck a SAWCore parser AST.
type CheckM = ReaderT CheckEnv TC.TCM

runCheckM ::
  CheckM a -> SharedContext -> Maybe ModuleName -> [(LocalName, Term)] ->
  IO (Either TC.TCError a)
runCheckM m sc mnm ctx =
  TC.runTCM (runReaderT m (CheckEnv mnm Map.empty)) sc ctx

-- | Read the current module name
askModName :: CheckM (Maybe ModuleName)
askModName = asks tcModName

-- | Read the current context of named variables
askCtxEC :: CheckM (Map LocalName (ExtCns Term))
askCtxEC = asks tcCtxEC

-- | Look up the current module name, raising an error if it is not set
getModuleName :: CheckM ModuleName
getModuleName =
  do maybe_modname <- askModName
     case maybe_modname of
       Just mnm -> return mnm
       Nothing ->
         panic "getModuleName" ["Current module name not set during typechecking"]

----------------------------------------------------------------------

typeInferComplete :: TC.TypeInfer a => a -> CheckM SCTypedTerm
typeInferComplete x = lift $ TC.typeInferComplete x

-- | Build a multi-arity application of 'SCTypedTerm's
inferApplyAll :: SCTypedTerm -> [SCTypedTerm] -> CheckM SCTypedTerm
inferApplyAll t [] = return t
inferApplyAll t (arg:args) =
  do app1 <- typeInferComplete (App t arg)
     inferApplyAll app1 args

-- | Resolve a name in the current module and apply it to some arguments
inferResolveNameApp :: Text -> [SCTypedTerm] -> CheckM SCTypedTerm
inferResolveNameApp n args =
  do ctx <- lift $ TC.askCtx
     nctx <- askCtxEC
     mnm <- getModuleName
     mm <- lift $ TC.liftTCM scGetModuleMap
     let ident = mkIdent mnm n
     case (findIndex ((== n) . fst) ctx, Map.lookup n nctx, resolveNameInMap mm ident) of
       (Just i, _, _) ->
         do t <- typeInferComplete (LocalVar i :: TermF SCTypedTerm)
            inferApplyAll t args
       (_, Just ec, _) ->
         do t <- typeInferComplete (Variable ec)
            inferApplyAll t args
       (_, _, Just rn) ->
         do let c = resolvedNameName rn
            t <- typeInferComplete (Constant c :: TermF SCTypedTerm)
            inferApplyAll t args
       (Nothing, Nothing, Nothing) ->
         throwTCError $ UnboundName n

-- | Match an untyped term as a name applied to 0 or more arguments
matchAppliedName :: Un.UTerm -> Maybe (Text, [Un.UTerm])
matchAppliedName (Un.Name (PosPair _ n)) = Just (n, [])
matchAppliedName (Un.App f arg) =
  do (n, args) <- matchAppliedName f
     return (n, args++[arg])
matchAppliedName _ = Nothing

-- | Match an untyped term as a recursor applied to 0 or more arguments
matchAppliedRecursor :: Un.UTerm -> Maybe (Text, [Un.UTerm])
matchAppliedRecursor (Un.Recursor (PosPair _ n)) = Just (n, [])
matchAppliedRecursor (Un.App f arg) =
  do (n, args) <- matchAppliedRecursor f
     return (n, args++[arg])
matchAppliedRecursor _ = Nothing

-- | The debugging level
debugLevel :: Int
debugLevel = 0

-- | Print debugging output if 'debugLevel' is greater than 0
typeInferDebug :: String -> CheckM ()
typeInferDebug str | debugLevel > 0 = liftIO $ traceIO str
typeInferDebug _ = return ()

-- | Completely typecheck an untyped SAWCore AST.
typeInferCompleteUTerm :: Un.UTerm -> CheckM SCTypedTerm
typeInferCompleteUTerm t =
  do typeInferDebug ("typechecking term: " ++ show t)
     res <- atPos (pos t) $ typeInferCompleteTerm t
     typeInferDebug ("completed typechecking term: " ++ show t ++ "\n"
                     ++ "type = " ++ show (typedType res))
     return res

-- | Main workhorse function for type inference on untyped terms
typeInferCompleteTerm :: Un.UTerm -> CheckM SCTypedTerm

-- Names
typeInferCompleteTerm (matchAppliedName -> Just (n, args)) =
  mapM typeInferCompleteUTerm args >>= inferResolveNameApp n
typeInferCompleteTerm (Un.Name (PosPair _ n)) =
  -- NOTE: this is actually covered by the previous case, but we put it here
  -- so GHC doesn't complain about coverage
  inferResolveNameApp n []

-- Sorts
typeInferCompleteTerm (Un.Sort _ srt h) =
  typeInferComplete (Sort srt h :: FlatTermF SCTypedTerm)

-- Recursors (must come before applications)
typeInferCompleteTerm (matchAppliedRecursor -> Just (str, args)) =
  do mnm <- getModuleName
     mm <- lift $ TC.liftTCM scGetModuleMap
     let dt_ident = mkIdent mnm str
     dt <- case findDataTypeInMap dt_ident mm of
       Just d -> return d
       Nothing -> throwTCError $ NoSuchDataType (ModuleIdentifier dt_ident)
     typed_args <- mapM typeInferCompleteUTerm args
     case typed_args of
       (splitAt (length $ dtParams dt) -> (params, motive : rem_args)) ->
         do crec    <- lift $ TC.compileRecursor dt params motive
            r       <- typeInferComplete (Recursor crec)
            inferApplyAll r rem_args

       _ -> throwTCError $ NotFullyAppliedRec (nameInfo (dtName dt))

typeInferCompleteTerm (Un.Recursor _) =
  error "typeInferComplete: found a bare Recursor, which should never happen!"

-- Applications, lambdas, and pis
typeInferCompleteTerm (Un.App f arg) =
  (App <$> typeInferCompleteUTerm f <*> typeInferCompleteUTerm arg)
  >>= typeInferComplete
typeInferCompleteTerm (Un.Lambda _ [] t) = typeInferCompleteUTerm t
typeInferCompleteTerm (Un.Lambda p ((Un.termVarLocalName -> x, tp) : ctx) t) =
  do tp_trm <- typeInferCompleteUTerm tp
     -- NOTE: we need the type of x to be normalized when we add it to the
     -- context in withVar, but we do not want to normalize this type in the
     -- output, as the contract for typeInferComplete only normalizes the type,
     -- so we use the unnormalized tp_trm in the return
     tp_whnf <- lift $ TC.typeCheckWHNF $ typedVal tp_trm
     body <- withVar x tp_whnf $
       typeInferCompleteUTerm $ Un.Lambda p ctx t
     typeInferComplete (Lambda x tp_trm body)
typeInferCompleteTerm (Un.Pi _ [] t) = typeInferCompleteUTerm t
typeInferCompleteTerm (Un.Pi p ((Un.termVarLocalName -> x, tp) : ctx) t) =
  do tp_trm <- typeInferCompleteUTerm tp
     -- NOTE: we need the type of x to be normalized when we add it to the
     -- context in withVar, but we do not want to normalize this type in the
     -- output, as the contract for typeInferComplete only normalizes the type,
     -- so we use the unnormalized tp_trm in the return
     tp_whnf <- lift $ TC.typeCheckWHNF $ typedVal tp_trm
     body <- withVar x tp_whnf $
       typeInferCompleteUTerm $ Un.Pi p ctx t
     typeInferComplete (Pi x tp_trm body)

-- Non-dependent records
typeInferCompleteTerm (Un.RecordValue _ elems) =
  do typed_elems <-
       mapM (\(PosPair _ fld, t) -> (fld,) <$> typeInferCompleteUTerm t) elems
     typeInferComplete (RecordValue typed_elems)
typeInferCompleteTerm (Un.RecordType _ elems) =
  do typed_elems <-
       mapM (\(PosPair _ fld, t) -> (fld,) <$> typeInferCompleteUTerm t) elems
     typeInferComplete (RecordType typed_elems)
typeInferCompleteTerm (Un.RecordProj t prj) =
  (RecordProj <$> typeInferCompleteUTerm t <*> return prj) >>= typeInferComplete

-- Unit
typeInferCompleteTerm (Un.UnitValue _) =
  typeInferComplete (UnitValue :: FlatTermF SCTypedTerm)
typeInferCompleteTerm (Un.UnitType _) =
  typeInferComplete (UnitType :: FlatTermF SCTypedTerm)

-- Simple pairs
typeInferCompleteTerm (Un.PairValue _ t1 t2) =
  (PairValue <$> typeInferCompleteUTerm t1 <*> typeInferCompleteUTerm t2)
  >>= typeInferComplete
typeInferCompleteTerm (Un.PairType _ t1 t2) =
  (PairType <$> typeInferCompleteUTerm t1 <*> typeInferCompleteUTerm t2)
  >>= typeInferComplete
typeInferCompleteTerm (Un.PairLeft t) =
  (PairLeft <$> typeInferCompleteUTerm t) >>= typeInferComplete
typeInferCompleteTerm (Un.PairRight t) =
  (PairRight <$> typeInferCompleteUTerm t) >>= typeInferComplete

-- Type ascriptions
typeInferCompleteTerm (Un.TypeConstraint t _ tp) =
  do typed_t <- typeInferCompleteUTerm t
     typed_tp <- typeInferCompleteUTerm tp
     _ <- lift $ TC.ensureSort (typedType typed_tp)
     lift $ TC.checkSubtype typed_t (typedVal typed_tp)
     return typed_t

-- Literals
typeInferCompleteTerm (Un.NatLit _ i) =
  typeInferComplete (NatLit i :: FlatTermF SCTypedTerm)
typeInferCompleteTerm (Un.StringLit _ str) =
  typeInferComplete (StringLit str :: FlatTermF SCTypedTerm)
typeInferCompleteTerm (Un.VecLit _ []) = throwTCError EmptyVectorLit
typeInferCompleteTerm (Un.VecLit _ ts) =
  do typed_ts <- mapM typeInferCompleteUTerm ts
     tp <- case typed_ts of
       (t1:_) -> return $ typedType t1
       [] -> throwTCError $ EmptyVectorLit
     typed_tp <- typeInferComplete tp
     typeInferComplete (ArrayValue typed_tp $
                        V.fromList typed_ts)
typeInferCompleteTerm (Un.BVLit _ []) = throwTCError EmptyVectorLit
typeInferCompleteTerm (Un.BVLit _ bits) =
  do tp <- lift $ TC.liftTCM scBoolType
     bit_tms <- lift $ mapM (TC.liftTCM scBool) bits
     typeInferComplete $ ArrayValue tp $ V.fromList bit_tms

typeInferCompleteTerm (Un.BadTerm _) =
  -- Should be unreachable, since BadTerms represent parse errors, that should
  -- already have been signaled before type inference
  panic "typeInferCompleteTerm" ["Type inference encountered a BadTerm"]


--
-- Type-checking modules
--

-- | Type-check a list of declarations and insert them into the current module
processDecls :: [Un.Decl] -> CheckM ()
processDecls [] = return ()

processDecls (Un.InjectCodeDecl ns txt : rest) =
  do mnm <- getModuleName
     lift $ TC.liftTCM scInjectCode mnm ns txt
     processDecls rest

processDecls (Un.TypedDef nm params rty body : rest) =
  processDecls (Un.TypeDecl NoQualifier nm (Un.Pi (pos nm) params rty) :
                Un.TermDef nm (map fst params) body : rest)

processDecls (Un.TypeDecl NoQualifier (PosPair p nm) tp :
              Un.TermDef (PosPair _ ((== nm) -> True)) vars body : rest) =
  -- Type-checking for definitions
  (atPos p $
   do
     -- Step 1: type-check the type annotation, and make sure it is a type
     typed_tp <- typeInferCompleteUTerm tp
     void $ lift $ TC.ensureSort $ typedType typed_tp
     let def_tp = typedVal typed_tp
     def_tp_whnf <- lift $ TC.liftTCM TC.scTypeCheckWHNF def_tp

     -- Step 2: assign types to the bound variables of the definition, by
     -- peeling off the pi-abstraction variables in the type annotation. Any
     -- remaining body of the pi-type is the required type for the def body.
     (ctx, req_body_tp) <-
       case matchPiWithNames (map Un.termVarLocalName vars) def_tp_whnf of
         Just x -> return x
         Nothing ->
             throwTCError $
             DeclError nm ("More variables " ++ show (map Un.termVarLocalName vars) ++
                           " than length of function type:\n" ++
                           showTerm (typedVal typed_tp))

     -- Step 3: type-check the body of the definition in the context of its
     -- variables, and build a function that takes in those variables
     def_tm <-
       withCtx ctx $
       do typed_body <- typeInferCompleteUTerm body
          lift $ TC.checkSubtype typed_body req_body_tp
          lift $ TC.liftTCM scLambdaList ctx (typedVal typed_body)

     -- Step 4: add the definition to the current module
     mnm <- getModuleName
     let ident = mkIdent mnm nm
     lift $ TC.liftTCM scInsertDef ident def_tp def_tm) >>
  processDecls rest

processDecls (Un.TypeDecl NoQualifier (PosPair p nm) _ : _) =
  atPos p $ throwTCError $ DeclError nm "Definition without defining equation"

processDecls (Un.TypeDecl _ (PosPair p nm) _ :
              Un.TermDef (PosPair _ ((== nm) -> True)) _ _ : _) =
  atPos p $ throwTCError $ DeclError nm "Primitive or axiom with definition"

processDecls (Un.TypeDecl q (PosPair p nm) tp : rest) =
  (atPos p $
   do typed_tp <- typeInferCompleteUTerm tp
      void $ lift $ TC.ensureSort $ typedType typed_tp
      mnm <- getModuleName
      let ident = mkIdent mnm nm
      let def_tp = typedVal typed_tp
      lift $ TC.liftTCM scDeclarePrim ident q def_tp) >>
  processDecls rest

processDecls (Un.TermDef (PosPair p nm) _ _ : _) =
  atPos p $ throwTCError $ DeclError nm "Dangling definition without a type"

processDecls (Un.DataDecl (PosPair p nm) param_ctx dt_tp c_decls : rest) =
  let param_ctx' = map (\(x, t) -> (Un.termVarLocalName x, t)) param_ctx in
  -- This top line makes sure that we process the rest of the decls after the
  -- main body of the code below, which processes just the current data decl
  (>> processDecls rest) $ atPos p $
  -- Step 1: type-check the parameters
  typeInferCompleteInCtxEC param_ctx' $ \params -> do
  let dtParams = map (\(_,ec,_) -> ec) params
  let param_sort = maxSort (map (\(_,_,s) -> s) params)
  let err :: String -> CheckM a
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
  dt_ixs_typed <- typeInferCompleteCtxEC dt_ixs'
  let dtIndices = map (\(_,ec,_) -> ec) dt_ixs_typed
      ixs_max_sort = maxSort (map (\(_,_,s) -> s) dt_ixs_typed)

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
  pn <- lift $ TC.liftTCM scBeginDataType dtIdent dtParams dtIndices dtSort

  -- Step 5: typecheck the constructors, and build Ctors for them
  typed_ctors <-
    mapM (\(Un.Ctor (PosPair p' c) ctx body) ->
           (c,) <$> typeInferCompleteUTerm (Un.Pi p' ctx body)) c_decls
  ctors <-
    forM typed_ctors $ \(c, typed_tp) ->
    -- Check that the universe level of the type of each constructor
    do case asSort (typedType typed_tp) of
           Just ctor_sort
             | dtSort /= propSort && ctor_sort > dtSort ->
               err ("Universe level of constructors should be strictly" ++
                    " contained in that of the datatype")
           Just _ ->
               return ()
           Nothing ->
               panic "processDecls" [
                   "Type of the type of constructor is not a sort!",
                   "Constructor type: " <> Text.pack (showTerm $ typedVal typed_tp),
                   "Type of that type: " <> Text.pack (showTerm $ typedType typed_tp)
               ]
       let tp = typedVal typed_tp
       result <- lift $ TC.liftTCM mkCtorArgStruct pn dtParams dtIndices tp
       case result of
         Just arg_struct ->
           lift $ TC.liftTCM scBuildCtor pn (mkIdent mnm c) arg_struct
         Nothing -> err ("Malformed type form constructor: " ++ show c)

  -- Step 6: complete the datatype with the given ctors
  lift $ TC.liftTCM scCompleteDataType dtIdent ctors


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
  decls_res <- runCheckM (processDecls decls) sc (Just mnm) []
  case decls_res of
    Left err -> fail $ unlines $ TC.prettyTCError err
    Right _ -> return ()


--
-- Helper functions for type-checking modules
--

-- | Pattern match a nested pi-abstraction, like 'asPiList', but only match as
-- far as the supplied list of variables, and use them as the new names
matchPiWithNames :: [LocalName] -> Term -> Maybe ([(LocalName, Term)], Term)
matchPiWithNames [] tp = return ([], tp)
matchPiWithNames (var:vars) (asPi -> Just (_, arg_tp, body_tp)) =
  do (ctx,body) <- matchPiWithNames vars body_tp
     return ((var,arg_tp):ctx,body)
matchPiWithNames _ _ = Nothing

-- | Run a type-checking computation in a typing context extended with a new
-- variable with the given type. This throws away the memoization table while
-- running the sub-computation, as memoization tables are tied to specific sets
-- of bindings.
--
-- NOTE: the type given for the variable should be in WHNF, so that we do not
-- have to normalize the types of variables each time we see them.
withVar :: LocalName -> Term -> CheckM a -> CheckM a
withVar x tp m = ReaderT $ \env -> TC.withVar x tp (runReaderT m env)

withEC :: LocalName -> ExtCns Term -> CheckM a -> CheckM a
withEC x ec m =
  TC.rethrowTCError (ErrorCtx x (ecType ec)) $
  TC.withEmptyTCState $
  local (\env -> env { tcCtxEC = Map.insert x ec (tcCtxEC env) }) m

-- | Run a type-checking computation in a typing context extended by a list of
-- variables and their types. See 'withVar'.
withCtx :: [(LocalName, Term)] -> CheckM a -> CheckM a
withCtx = flip (foldr (\(x,tp) -> withVar x tp))

-- | Run a type-checking computation in a typing context extended by a list of
-- variables and their types. See 'withEC'.
withCtxEC :: [(LocalName, ExtCns Term)] -> CheckM a -> CheckM a
withCtxEC = flip (foldr (\(x,ec) -> withEC x ec))

-- | Perform type inference on a context, i.e., a list of variable names and
-- their associated types. This will give us 'Term's for each type, as
-- well as their 'Sort's, since the type of any type is a 'Sort'.
typeInferCompleteCtxEC ::
  [(LocalName, Un.UTerm)] -> CheckM [(LocalName, ExtCns Term, Sort)]
typeInferCompleteCtxEC [] = pure []
typeInferCompleteCtxEC ((x, tp) : ctx) =
  do typed_tp <- typeInferCompleteUTerm tp
     s <- lift $ TC.ensureSort (typedType typed_tp)
     ec <- lift $ TC.liftTCM scFreshEC x (typedVal typed_tp)
     ((x, ec, s) :) <$> withEC x ec (typeInferCompleteCtxEC ctx)

-- | Perform type inference on a context via 'typeInferCompleteCtxEC', and then
-- run a computation in that context via 'withCtxEC', also passing in that context
-- to the computation
typeInferCompleteInCtxEC ::
  [(LocalName, Un.UTerm)] ->
  ([(LocalName, ExtCns Term, Sort)] -> CheckM a) -> CheckM a
typeInferCompleteInCtxEC ctx f =
  do typed_ctx <- typeInferCompleteCtxEC ctx
     withCtxEC (map (\(x,ec,_) -> (x,ec)) typed_ctx) (f typed_ctx)
