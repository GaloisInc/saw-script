{-# OPTIONS_GHC -fno-warn-orphans #-}
-- The above is needed because we want our orphan TypeInfer instance below

{-# LANGUAGE CPP #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs  #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE RecordWildCards #-}

{- |
Module      : Verifier.SAW.Typechecker
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : jhendrix@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module Verifier.SAW.Typechecker
  ( inferCompleteTerm
  , tcInsertModule
  ) where

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative
#endif
import Control.Monad.State
import Data.List (findIndex)
import qualified Data.Vector as V
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import Verifier.SAW.Utils (internalError)

import Verifier.SAW.Module
import Verifier.SAW.Position
import Verifier.SAW.Term.Functor
import Verifier.SAW.Term.CtxTerm
import Verifier.SAW.SharedTerm
import Verifier.SAW.SCTypeCheck
import qualified Verifier.SAW.UntypedAST as Un

import Debug.Trace

-- | Infer the type of an untyped term and complete it to a 'Term', all in the
-- empty typing context
inferCompleteTerm :: SharedContext -> Maybe ModuleName -> Un.Term ->
                     IO (Either Doc Term)
inferCompleteTerm sc mnm t = inferCompleteTermCtx sc mnm [] t

-- | Infer the type of an untyped term and complete it to a 'Term' in a given
-- typing context
inferCompleteTermCtx :: SharedContext -> Maybe ModuleName -> [(String,Term)] ->
                        Un.Term -> IO (Either Doc Term)
inferCompleteTermCtx sc mnm ctx t =
  do res <- runTCM (typeInferComplete t) sc mnm ctx
     case res of
       Left err -> return $ Left $ vsep $ map string $ prettyTCError err
       Right t' -> return $ Right $ typedVal t'

-- | Look up the current module name, raising an error if it is not set
getModuleName :: TCM ModuleName
getModuleName =
  do maybe_modname <- askModName
     case maybe_modname of
       Just mnm -> return mnm
       Nothing ->
         internalError "Current module name not set during typechecking"

-- | Look up the current module
getModule :: TCM Module
getModule = getModuleName >>= liftTCM scFindModule

-- | Build a multi-arity application of 'TypedTerm's
inferApplyAll :: TypedTerm -> [TypedTerm] -> TCM TypedTerm
inferApplyAll t [] = return t
inferApplyAll t (arg:args) =
  do app1 <- typeInferComplete (App t arg)
     inferApplyAll app1 args

-- | Resolve a name in the current module and apply it to some arguments
inferResolveNameApp :: String -> [TypedTerm] -> TCM TypedTerm
inferResolveNameApp n args =
  do ctx <- askCtx
     m <- getModule
     case (findIndex ((== n) . fst) ctx, resolveName m n) of
       (Just i, _) ->
         do t <- typeInferComplete (LocalVar i :: TermF TypedTerm)
            inferApplyAll t args
       (_, Just (ResolvedCtor ctor)) ->
         let (params, ixs) = splitAt (ctorNumParams ctor) args in
         if length ixs == ctorNumArgs ctor then
           typeInferComplete (CtorApp (ctorName ctor) params ixs)
         else throwTCError (NotFullyApplied (ctorName ctor))
       (_, Just (ResolvedDataType dt)) ->
         let (params, ixs) = splitAt (length $ dtParams dt) args in
         if length ixs == length (dtIndices dt) then
           typeInferComplete (DataTypeApp (dtName dt) params ixs)
         else throwTCError (NotFullyApplied (dtName dt))
       (_, Just (ResolvedDef d)) ->
         do f <- typeInferComplete (GlobalDef (defIdent d)
                                    :: FlatTermF TypedTerm)
            inferApplyAll f args
       (Nothing, Nothing) ->
         throwTCError $ UnboundName n

-- | Match an untyped term as a name applied to 0 or more arguments
matchAppliedName :: Un.Term -> Maybe (String, [Un.Term])
matchAppliedName (Un.Name (PosPair _ n)) = Just (n, [])
matchAppliedName (Un.App f arg) =
  do (n, args) <- matchAppliedName f
     return (n, args++[arg])
matchAppliedName _ = Nothing

-- | Match an untyped term as a recursor applied to 0 or more arguments
matchAppliedRecursor :: Un.Term -> Maybe (Maybe ModuleName, String, [Un.Term])
matchAppliedRecursor (Un.Recursor mnm (PosPair _ n)) = Just (mnm, n, [])
matchAppliedRecursor (Un.App f arg) =
  do (mnm, n, args) <- matchAppliedRecursor f
     return (mnm, n, args++[arg])
matchAppliedRecursor _ = Nothing

-- | The debugging level
debugLevel :: Int
debugLevel = 0

-- | Print debugging output if 'debugLevel' is greater than 0
typeInferDebug :: String -> TCM ()
typeInferDebug str | debugLevel > 0 = liftIO $ traceIO str
typeInferDebug _ = return ()

-- The type inference engine for untyped terms, which mostly just dispatches to
-- the type inference engine for (FTermF TypedTerm) defined in SCTypeCheck.hs
instance TypeInfer Un.Term where
  typeInfer t = typedVal <$> typeInferComplete t

  typeInferComplete t =
    do typeInferDebug ("typechecking term: " ++ show t)
       res <- atPos (pos t) $ typeInferCompleteTerm t
       typeInferDebug ("completed typechecking term: " ++ show t ++ "\n"
                       ++ "type = " ++ show (typedType res))
       return res

-- | Main workhore function for type inference on untyped terms
typeInferCompleteTerm :: Un.Term -> TCM TypedTerm

-- Names
typeInferCompleteTerm (matchAppliedName -> Just (n, args)) =
  mapM typeInferComplete args >>= inferResolveNameApp n
typeInferCompleteTerm (Un.Name (PosPair _ n)) =
  -- NOTE: this is actually covered by the previous case, but we put it here
  -- so GHC doesn't complain about coverage
  inferResolveNameApp n []

-- Sorts
typeInferCompleteTerm (Un.Sort _ srt) =
  typeInferComplete (Sort srt :: FlatTermF TypedTerm)

-- Recursors (must come before applications)
typeInferCompleteTerm (matchAppliedRecursor -> Just (maybe_mnm, str, args)) =
  do mnm <-
       case maybe_mnm of
         Just mnm -> return mnm
         Nothing -> getModuleName
     m <- liftTCM scFindModule mnm
     let dt_ident = mkIdent mnm str
     dt <- case findDataType m str of
       Just d -> return d
       Nothing -> throwTCError $ NoSuchDataType dt_ident
     typed_args <- mapM typeInferComplete args
     case typed_args of
       (splitAt (length $ dtParams dt) ->
        (params,
         p_ret :
         (splitAt (length $ dtCtors dt) ->
          (elims,
           (splitAt (length $ dtIndices dt) ->
            (ixs, arg : rem_args)))))) ->
         do let cs_fs = zip (map ctorName $ dtCtors dt) elims
            typed_r <- typeInferComplete (RecursorApp dt_ident params
                                          p_ret cs_fs ixs arg)
            inferApplyAll typed_r rem_args
       _ -> throwTCError $ NotFullyAppliedRec dt_ident
typeInferCompleteTerm (Un.Recursor _ _) =
  error "typeInferComplete: found a bare Recursor, which should never happen!"

-- Applications, lambdas, and pis
typeInferCompleteTerm (Un.App f arg) =
  (App <$> typeInferComplete f <*> typeInferComplete arg)
  >>= typeInferComplete
typeInferCompleteTerm (Un.Lambda _ [] t) = typeInferComplete t
typeInferCompleteTerm (Un.Lambda p ((Un.termVarString -> x,tp):ctx) t) =
  do tp_trm <- typeInferComplete tp
     body <- withVar x (typedVal tp_trm) $
       typeInferComplete $ Un.Lambda p ctx t
     typeInferComplete (Lambda x tp_trm body)
typeInferCompleteTerm (Un.Pi _ [] t) = typeInferComplete t
typeInferCompleteTerm (Un.Pi p ((Un.termVarString -> x,tp):ctx) t) =
  do tp_trm <- typeInferComplete tp
     body <- withVar x (typedVal tp_trm) $
       typeInferComplete $ Un.Pi p ctx t
     typeInferComplete (Pi x tp_trm body)

-- Non-dependent records
typeInferCompleteTerm (Un.RecordValue _ elems) =
  do typed_elems <-
       mapM (\(PosPair _ fld, t) -> (fld,) <$> typeInferComplete t) elems
     typeInferComplete (RecordValue typed_elems)
typeInferCompleteTerm (Un.RecordType _ elems) =
  do typed_elems <-
       mapM (\(PosPair _ fld, t) -> (fld,) <$> typeInferComplete t) elems
     typeInferComplete (RecordType typed_elems)
typeInferCompleteTerm (Un.RecordProj t prj) =
  (RecordProj <$> typeInferComplete t <*> return prj) >>= typeInferComplete

-- Old-style pairs
typeInferCompleteTerm (Un.OldPairValue _ t1 t2) =
  (PairValue <$> typeInferComplete t1 <*> typeInferComplete t2)
  >>= typeInferComplete
typeInferCompleteTerm (Un.OldPairType _ t1 t2) =
  (PairType <$> typeInferComplete t1 <*> typeInferComplete t2)
  >>= typeInferComplete
typeInferCompleteTerm (Un.OldPairLeft t) =
  (PairLeft <$> typeInferComplete t) >>= typeInferComplete
typeInferCompleteTerm (Un.OldPairRight t) =
  (PairRight <$> typeInferComplete t) >>= typeInferComplete

-- Type ascriptions
typeInferCompleteTerm (Un.TypeConstraint t _ tp) =
  do typed_t <- typeInferComplete t
     typed_tp <- typeInferComplete tp
     _ <- ensureSort (typedType typed_tp)
     checkSubtype typed_t (typedVal typed_tp)
     return typed_t

-- Literals
typeInferCompleteTerm (Un.NatLit _ i) =
  typeInferComplete (NatLit i :: FlatTermF TypedTerm)
typeInferCompleteTerm (Un.StringLit _ str) =
  typeInferComplete (StringLit str :: FlatTermF TypedTerm)
typeInferCompleteTerm (Un.VecLit _ []) = throwTCError EmptyVectorLit
typeInferCompleteTerm (Un.VecLit _ ts) =
  do typed_ts <- mapM typeInferComplete ts
     tp <- case typed_ts of
       (t1:_) -> return $ typedType t1
       [] -> throwTCError $ EmptyVectorLit
     type_of_tp <- typeInfer tp
     typeInferComplete (ArrayValue (TypedTerm tp type_of_tp) $
                        V.fromList typed_ts)

typeInferCompleteTerm (Un.BadTerm _) =
  -- Should be unreachable, since BadTerms represent parse errors, that should
  -- already have been signaled before type inference
  internalError "Type inference encountered a BadTerm"


instance TypeInferCtx Un.TermVar Un.Term where
  typeInferCompleteCtx =
    typeInferCompleteCtx . map (\(x,tp) -> (Un.termVarString x, tp))


--
-- Type-checking modules
--

-- | Type-check a list of declarations and insert them into the current module
processDecls :: [Un.Decl] -> TCM ()
processDecls [] = return ()
processDecls (Un.TypeDecl NoQualifier (PosPair p nm) tp :
              Un.TermDef (PosPair _ ((== nm) -> True)) ctx body : rest) =
  atPos p $
  do typed_tp <- typeInferComplete tp
     void $ ensureSort $ typedType typed_tp
     real_ctx <- completeContext nm ctx $ fst $ Un.asPiList tp
     typed_body <- typeInferComplete (Un.Lambda (pos body) real_ctx body)
     checkSubtype typed_body (typedVal typed_tp)
     mnm <- getModuleName
     liftTCM scModifyModule mnm $ \m ->
       insDef m $ Def { defIdent = mkIdent mnm nm,
                        defQualifier = NoQualifier,
                        defType = typedVal typed_tp,
                        defBody = Just (typedVal typed_body) }
     processDecls rest

processDecls (Un.TypeDecl NoQualifier (PosPair p nm) _ : _) =
  atPos p $ throwTCError $ DeclError nm "Definition without defining equation"
processDecls (Un.TypeDecl _ (PosPair p nm) _ :
              Un.TermDef (PosPair _ ((== nm) -> True)) _ _ : _) =
  atPos p $ throwTCError $ DeclError nm "Primitive or axiom with definition"
processDecls (Un.TypeDecl q (PosPair p nm) tp : rest) =
  atPos p $
  do typed_tp <- typeInferComplete tp
     void $ ensureSort $ typedType typed_tp
     mnm <- getModuleName
     liftTCM scModifyModule mnm $ \m ->
       insDef m $ Def { defIdent = mkIdent mnm nm,
                        defQualifier = q,
                        defType = typedVal typed_tp,
                        defBody = Nothing }
     processDecls rest
processDecls (Un.TermDef (PosPair p nm) _ _ : _) =
  atPos p $ throwTCError $ DeclError nm "Dangling definition without a type"
processDecls (Un.DataDecl (PosPair p nm) param_ctx dt_tp c_decls : rest) =
  -- This top line makes sure that we process the rest of the decls after the
  -- main body of the code below, which processes just the current data decl
  (>> processDecls rest) $ atPos p $
  -- Step 1: type-check the parameters
  typeInferCompleteInCtx param_ctx $ \params -> do
  let dtParams = map (\(x,tp,_) -> (x,tp)) params
  let param_sort = maximum (propSort : map (\(_,_,s) -> s) params)
  let err :: String -> TCM a
      err msg = throwTCError $ DeclError nm msg

  -- Step 2: type-check the type given for d, and make sure it is of the form
  -- (i1:ix1) -> ... -> (in:ixn) -> Type s for some sort s. Then form the full
  -- type of d as (p1:param1) -> ... -> (i1:ix1) -> ... -> Type s
  (dt_ixs, dtSort) <-
    case Un.asPiList dt_tp of
      (ixs, Un.Sort _ s) -> return (ixs, s)
      _ -> err "Wrong form for type of datatype"
  dt_ixs_typed <- typeInferCompleteCtx dt_ixs
  let dtIndices = map (\(x,tp,_) -> (x,tp)) dt_ixs_typed
      ixs_max_sort = maximum (propSort : map (\(_,_,s) -> s) dt_ixs_typed)
  dtType <- (liftTCM scPiList (dtParams ++ dtIndices)
             =<< liftTCM scSort dtSort)

  -- Step 3: do the necessary universe inclusion checking for any predicative
  -- (non-Prop) inductive type, which includes:
  --
  -- 1. All ix types must be of sort dtSort; AND
  -- 2. All param types must be of sort dtSort+1
  --
  -- Note that the addition of propSort as an argument to maximum below is to
  -- ensure that it is passed a non-empty list
  if dtSort /= propSort && param_sort > sortOf dtSort then
    err ("Universe level of parameters should be no greater \
         than that of the datatype")
    else return ()
  if dtSort /= propSort && ixs_max_sort > dtSort then
    err ("Universe level of indices should be strictly contained \
         in that of the datatype")
    else return ()

  -- Step 4: Add d as an empty datatype, so we can typecheck the constructors
  mnm <- getModuleName
  let dtName = mkIdent mnm nm
  let dt = DataType { dtCtors = [], .. }
  liftTCM scModifyModule mnm (\m -> beginDataType m dt)

  -- Step 5: typecheck the constructors, and build Ctors for them
  typed_ctors <-
    mapM (\(Un.Ctor (PosPair p' c) ctx body) ->
           (c,) <$> typedVal <$> typeInferComplete (Un.Pi p' ctx body)) c_decls
  ctors <-
    case ctxBindingsOfTerms dtParams of
      ExistsTp p_ctx ->
        case ctxBindingsOfTerms dtIndices of
          ExistsTp ix_ctx ->
            forM typed_ctors $ \(c, tp) ->
            case mkCtorArgStruct dtName p_ctx ix_ctx tp of
              Just arg_struct ->
                liftTCM scBuildCtor dtName (mkIdent mnm c) arg_struct
              Nothing -> err ("Malformed type form constructor: " ++ c)

  -- Step 6: complete the datatype with the given ctors
  liftTCM scModifyModule mnm (\m -> completeDataType m dtName ctors)


-- | Typecheck a module and, on success, insert it into the current context
tcInsertModule :: SharedContext -> Un.Module -> IO ()
tcInsertModule sc (Un.Module (PosPair _ mnm) imports decls) = do
  let myfail :: String -> IO a
      myfail msg = scUnloadModule sc mnm >> fail msg
  -- First, insert an empty module for mnm
  scLoadModule sc $ emptyModule mnm
  -- Next, process all the imports
  forM_ imports $ \imp ->
    do i_exists <- scModuleIsLoaded sc (val $ Un.importModName imp)
       i <- if i_exists then scFindModule sc $ val $ Un.importModName imp else
              myfail $ "Imported module not found: " ++ show mnm
       scModifyModule sc mnm
         (insImport (Un.nameSatsConstraint (Un.importConstraints imp)
                     . identName . resolvedNameIdent) i)
  -- Finally, process all the decls
  decls_res <- runTCM (processDecls decls) sc (Just mnm) []
  case decls_res of
    Left err -> myfail $ unlines $ prettyTCError err
    Right _ -> return ()


--
-- Helper functions for type-checking modules
--

-- | Test whether two variable names "match", meaning that they are equal and/or
-- at least one is an unused variable
termVarsMatch :: Un.TermVar -> Un.TermVar -> Bool
termVarsMatch (Un.TermVar v1) (Un.TermVar v2) | val v1 == val v2 = True
termVarsMatch (Un.UnusedVar _) _ = True
termVarsMatch _ (Un.UnusedVar _) = True
termVarsMatch _ _ = False

-- | Take two term variables that match (as in 'termVarsMatch') and pick the
-- "most defined" one, i.e., the one that is not 'UnusedVar'
combineTermVars :: Un.TermVar -> Un.TermVar -> Un.TermVar
combineTermVars (Un.UnusedVar _) v2 = v2
combineTermVars v1 _ = v1

-- | Complete a variable context that might be missing some types against a
-- function type it is intended to match by filling in any types missing in
-- the former with the corresponding type in the latter
completeContext :: String -> [(Un.TermVar, Maybe Un.Term)] -> Un.TermCtx ->
                   TCM Un.TermCtx
completeContext _ [] _ = return []
completeContext nm ((var, Just tp):ctx) ((var', _):ctx')
  | termVarsMatch var var' =
    ((combineTermVars var var', tp) :) <$> completeContext nm ctx ctx'
completeContext nm ((var, Nothing):ctx) ((var', tp):ctx')
  | termVarsMatch var var' =
    ((combineTermVars var var', tp) :) <$> completeContext nm ctx ctx'
completeContext nm ((var1, _):_) ((var2,_):_) =
  throwTCError $ DeclError nm ("Definition variable " ++ Un.termVarString var1
                               ++ " does not match variable used in type: "
                               ++ Un.termVarString var2)
completeContext nm ctx ctx' =
  throwTCError $
  DeclError nm ("More variables than length of function type:\n" ++
                show ctx ++ "\n" ++ show ctx')
