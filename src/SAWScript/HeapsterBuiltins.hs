{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE KindSignatures #-}

module SAWScript.HeapsterBuiltins
       ( heapster_init_env
       , heapster_init_env_from_file
       , heapster_init_env_for_files
       , heapster_typecheck_fun
       , heapster_typecheck_mut_funs
       , heapster_define_opaque_perm
       , heapster_define_recursive_perm
       , heapster_define_perm
       , heapster_assume_fun
       , heapster_print_fun_trans
       , heapster_export_coq
       , heapster_parse_test
       ) where

import Data.Maybe
import qualified Data.Map as Map
import Data.String
import Data.List
import Data.IORef
import Control.Lens
import Control.Monad
import Control.Monad.IO.Class
import Unsafe.Coerce
import GHC.TypeNats
import System.Directory
import qualified Data.ByteString.Lazy as BL
import qualified Data.ByteString.Lazy.UTF8 as BL
import Data.ByteString.Internal (c2w)

import Data.Binding.Hobbits

import Verifier.SAW.Term.Functor
import Verifier.SAW.Module
import Verifier.SAW.Prelude
import Verifier.SAW.SharedTerm
import Verifier.SAW.OpenTerm
import Verifier.SAW.Typechecker
import Verifier.SAW.SCTypeCheck
import qualified Verifier.SAW.UntypedAST as Un
import qualified Verifier.SAW.Grammar as Un

import Lang.Crucible.Types
import Lang.Crucible.FunctionHandle
import Lang.Crucible.CFG.Core
import Lang.Crucible.CFG.Extension
import Lang.Crucible.LLVM.Extension
import Lang.Crucible.LLVM.MemModel
import Lang.Crucible.LLVM.Translation

import qualified Text.LLVM.AST as L

import SAWScript.Proof
import SAWScript.Prover.SolverStats
import SAWScript.TopLevel
import SAWScript.Value
import SAWScript.Utils as SS
import SAWScript.Options
import SAWScript.LLVMBuiltins
import SAWScript.Builtins
import SAWScript.Crucible.LLVM.Builtins
import SAWScript.Crucible.LLVM.MethodSpecIR

import Verifier.SAW.Heapster.CruUtil
import Verifier.SAW.Heapster.Permissions
import Verifier.SAW.Heapster.TypedCrucible
import Verifier.SAW.Heapster.SAWTranslation
import Verifier.SAW.Heapster.PermParser
import Verifier.SAW.Heapster.Implication (mbMap2)
import Text.Parsec (runParser)

import SAWScript.Prover.Exporter
import Verifier.SAW.Translation.Coq
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))


getLLVMCFG :: ArchRepr arch -> SAW_CFG -> AnyCFG (LLVM arch)
getLLVMCFG _ (LLVM_CFG cfg) =
  -- FIXME: there should be an ArchRepr argument for LLVM_CFG to compare here!
  unsafeCoerce cfg
getLLVMCFG _ (JVM_CFG _) =
  error "getLLVMCFG: expected LLVM CFG, found JVM CFG!"

archReprWidth :: ArchRepr arch -> NatRepr (ArchWidth arch)
archReprWidth (X86Repr w) = w

lookupModDefiningSym :: HeapsterEnv -> String -> Maybe (Some LLVMModule)
lookupModDefiningSym env nm =
  find (\some_lm -> case some_lm of
           Some lm -> Map.member (fromString nm) (cfgMap (lm ^. modTrans))) $
  heapsterEnvLLVMModules env

lookupModDeclaringSym :: HeapsterEnv -> String -> Maybe (Some LLVMModule)
lookupModDeclaringSym env nm =
  find (\some_lm -> case some_lm of
           Some lm ->
             Map.member (fromString nm) (lm ^. modTrans.transContext.symbolMap)) $
  heapsterEnvLLVMModules env

heapster_default_env :: Closed PermEnv
heapster_default_env = $(mkClosed [| PermEnv [] [] [] |])

-- | Based on the function of the same name in Verifier.SAW.ParserUtils.
-- Unlike that function, this calls 'fail' instead of 'error'.
readModuleFromFile :: FilePath -> TopLevel (Un.Module, ModuleName)
readModuleFromFile path = do
  base <- liftIO getCurrentDirectory
  b <- liftIO $ BL.readFile path
  case Un.parseSAW base path b of
    (m@(Un.Module (Un.PosPair _ mnm) _ _),[]) -> pure (m, mnm)
    (_,errs) -> fail $ "Module parsing failed:\n" ++ show errs

parseTermFromString :: String -> String -> TopLevel Un.Term
parseTermFromString nm term_string = do
  let base = ""
      path = "<" ++ nm ++ ">"
  case Un.parseSAWTerm base path (BL.fromString term_string) of
    (term,[]) -> pure term
    (_,errs) -> fail $ "Term parsing failed:\n" ++ show errs

-- based on 'inferCompleteTermCtx'
typecheckTerm :: ModuleName -> Un.Term -> TopLevel TypedTerm
typecheckTerm mnm t = do
  sc <- getSharedContext
  res <- liftIO $ runTCM (typeInferComplete t) sc (Just mnm) []
  case res of
    Right t' -> pure $ t'
    Left err -> fail $ "Term failed to typecheck:\n" ++ unlines (prettyTCError err)

-- | Translate a 'TypRepr' to the SAW core type it represents
translateTypePerm :: SharedContext -> PermEnv -> TypeRepr tp -> IO Term
translateTypePerm sc env typ_perm =
  completeOpenTerm sc $
  typeTransType1 $
  runTransM (translate $ emptyMb typ_perm) (emptyTypeTransInfo env)

translateOpenTermToTerm :: SharedContext -> PermEnv -> [(SomeNamedPermName, Ident)]
                        -> TransM TypeTransInfo RNil OpenTerm -> TopLevel Term 
translateOpenTermToTerm sc env npnts m =
  liftIO $ completeOpenTerm sc $ runTransM m (TypeTransInfo MNil npnts env)

-- | Parse the second given string as a term, check that it has the given type,
-- and, if the parsed term is not already an identifier, add it as a
-- definition in the current module using the first given string. Returns
-- either the identifer of the new definition or the identifier parsed.
parseAndInsDef :: HeapsterEnv -> String -> Term -> String -> TopLevel Ident
parseAndInsDef henv nm term_tp term_string =
  do sc <- getSharedContext
     un_term <- parseTermFromString nm term_string
     let mnm = heapsterEnvSAWModule henv
     typed_term <- typecheckTerm mnm un_term
     eith <- liftIO $ runTCM (checkSubtype typed_term term_tp) sc (Just mnm) []
     case (eith, typedVal typed_term) of
       (Left err, _) -> fail $ unlines $ prettyTCError err
       (Right _, STApp _ _ (FTermF (GlobalDef term_ident))) ->
         return term_ident
       (Right _, term) -> do
         let term_ident = mkSafeIdent mnm nm
         liftIO $ scModifyModule sc mnm $ \m ->
           insDef m $ Def { defIdent = term_ident,
                            defQualifier = NoQualifier,
                            defType = term_tp,
                            defBody = Just term }
         pure term_ident


heapster_init_env :: BuiltinContext -> Options -> String -> String ->
                     TopLevel HeapsterEnv
heapster_init_env bic opts mod_str llvm_filename =
  do llvm_mod <- llvm_load_module llvm_filename
     sc <- getSharedContext
     let saw_mod_name = mkModuleName [mod_str]
     mod_loaded <- liftIO $ scModuleIsLoaded sc saw_mod_name
     if mod_loaded then
       fail ("SAW module with name " ++ show mod_str ++ " already defined!")
       else return ()
     -- import Prelude by default
     preludeMod <- liftIO $ scFindModule sc preludeModuleName
     liftIO $ scLoadModule sc (insImport (const True) preludeMod $
                                 emptyModule saw_mod_name)
     let perm_env = unClosed heapster_default_env
     perm_env_ref <- liftIO $ newIORef perm_env
     return $ HeapsterEnv {
       heapsterEnvSAWModule = saw_mod_name,
       heapsterEnvPermEnvRef = perm_env_ref,
       heapsterEnvLLVMModules = [llvm_mod]
       }

heapster_init_env_from_file :: BuiltinContext -> Options -> String -> String ->
                               TopLevel HeapsterEnv
heapster_init_env_from_file bic opts mod_filename llvm_filename =
  do llvm_mod <- llvm_load_module llvm_filename
     sc <- getSharedContext
     (saw_mod, saw_mod_name) <- readModuleFromFile mod_filename
     liftIO $ tcInsertModule sc saw_mod
     let perm_env = unClosed heapster_default_env
     perm_env_ref <- liftIO $ newIORef perm_env
     return $ HeapsterEnv {
       heapsterEnvSAWModule = saw_mod_name,
       heapsterEnvPermEnvRef = perm_env_ref,
       heapsterEnvLLVMModules = [llvm_mod]
       }

heapster_init_env_for_files :: BuiltinContext -> Options -> String -> [String] ->
                               TopLevel HeapsterEnv
heapster_init_env_for_files bic opts mod_filename llvm_filenames =
  do llvm_mods <- mapM llvm_load_module llvm_filenames
     sc <- getSharedContext
     (saw_mod, saw_mod_name) <- readModuleFromFile mod_filename
     liftIO $ tcInsertModule sc saw_mod
     let perm_env = unClosed heapster_default_env
     perm_env_ref <- liftIO $ newIORef perm_env
     return $ HeapsterEnv {
       heapsterEnvSAWModule = saw_mod_name,
       heapsterEnvPermEnvRef = perm_env_ref,
       heapsterEnvLLVMModules = llvm_mods
       }

-- | Define a new opaque named permission with the given name, arguments, and
-- type, that translates to the given named SAW core definition
heapster_define_opaque_perm :: BuiltinContext -> Options -> HeapsterEnv ->
                               String -> String -> String -> String ->
                               TopLevel ()
heapster_define_opaque_perm _bic _opts henv nm args_str tp_str term_string =
  do env <- liftIO $ readIORef $ heapsterEnvPermEnvRef henv
     some_args <- case parseCtxString env args_str of
       Left err -> fail ("Error parsing argument types: " ++ show err)
       Right args -> return args
     some_tp <- case parseTypeString env tp_str of
       Left err -> fail ("Error parsing permission type: " ++ show err)
       Right tp -> return tp
     case (some_args, some_tp) of
       (Some args, Some tp_perm) -> do
         sc <- getSharedContext
         term_tp <- liftIO $ translateTypePerm sc env (ValuePermRepr tp_perm)
         term_ident <- parseAndInsDef henv nm term_tp term_string
         let env' = permEnvAddOpaquePerm env nm args tp_perm term_ident
         liftIO $ writeIORef (heapsterEnvPermEnvRef henv) env'

-- | Define a new recursive named permission with the given name, arguments,
-- type, that translates to the given named SAW core definition.
heapster_define_recursive_perm :: BuiltinContext -> Options -> HeapsterEnv ->
                                  String -> String -> String -> [String] ->
                                  String -> String -> String ->
                                  TopLevel ()
heapster_define_recursive_perm _bic _opts henv
  nm args_str val_str p_strs trans_str fold_fun_str unfold_fun_str =
    do env <- liftIO $ readIORef $ heapsterEnvPermEnvRef henv
       let penv = mkParserEnv env
       some_args <- case runParser parseCtx penv "" args_str  of
         Left err -> fail ("Error parsing argument types: " ++ show err)
         Right argsCtx -> return argsCtx
       some_val <- case parseTypeString env val_str of
         Left err -> fail ("Error parsing permission type: " ++ show err)
         Right tp -> return tp
       case (some_args, some_val) of
         (Some args_ctx@(ParsedCtx _ args), Some val_perm) -> do
           let rpn = NamedPermName nm val_perm args
           sc <- getSharedContext
           
           trans_tp <- translateOpenTermToTerm sc env [] $
             piExprCtx args (typeTransType1 <$>
               translateClosed (ValuePermRepr val_perm))
           trans_ident <- parseAndInsDef henv nm trans_tp trans_str
           
           let penv' = penv { parserEnvPermVars = [(nm, SomeNamedPermName rpn)] }
           p_perms <- forM p_strs $ \p_str ->
             case runParser (parseValPermInCtx args_ctx val_perm) penv' "" p_str of
               Left err -> fail ("Error parsing disjunctive perm: " ++ show err)
               Right p_perm -> pure p_perm
          
           let npnts = [(SomeNamedPermName rpn, trans_ident)]
               or_tp = mbCombine . emptyMb $
                         foldr1 (mbMap2 ValPerm_Or) p_perms
               nm_tp = mbCombine . emptyMb $
                         nus (cruCtxProxies args) (ValPerm_Named rpn . pExprVars)
           fold_fun_tp <- translateOpenTermToTerm sc env npnts $ 
             piExprCtx args (piPermCtx (fmap (ValPerms_Cons ValPerms_Nil) or_tp)
               (const $ typeTransType1 <$> translate nm_tp))
           fold_ident <- parseAndInsDef henv nm fold_fun_tp fold_fun_str
           unfold_fun_tp <- translateOpenTermToTerm sc env npnts $ 
             piExprCtx args (piPermCtx (fmap (ValPerms_Cons ValPerms_Nil) nm_tp)
               (const $ typeTransType1 <$> translate or_tp))
           unfold_ident <- parseAndInsDef henv nm unfold_fun_tp unfold_fun_str

           let env' = permEnvAddRecPerm env nm args val_perm p_perms
                                        trans_ident fold_ident unfold_ident
           liftIO $ writeIORef (heapsterEnvPermEnvRef henv) env'

-- | Define a new named permission with the given name, arguments, and type
-- that is equivalent to the given permission.
heapster_define_perm :: BuiltinContext -> Options -> HeapsterEnv ->
                        String -> String -> String -> String ->
                        TopLevel ()
heapster_define_perm _bic _opts henv nm args_str tp_str perm_string =
  do env <- liftIO $ readIORef $ heapsterEnvPermEnvRef henv
     let penv = mkParserEnv env
     some_args <- case runParser parseCtx penv "" args_str  of
       Left err -> fail ("Error parsing argument types: " ++ show err)
       Right args -> return args
     some_tp <- case parseTypeString env tp_str of
       Left err -> fail ("Error parsing permission type: " ++ show err)
       Right tp -> return tp
     case (some_args, some_tp) of
       (Some args_ctx@(ParsedCtx _ args), Some tp_perm) -> do
         perm <- case runParser (parseValPermInCtx args_ctx tp_perm) penv "" perm_string of
           Left err -> fail ("Error parsing disjunctive perm: " ++ show err)
           Right perm -> pure perm
         sc <- getSharedContext
         term_tp <- liftIO $ translateTypePerm sc env (ValuePermRepr tp_perm)
         let env' = permEnvAddDefinedPerm env nm args tp_perm perm
         liftIO $ writeIORef (heapsterEnvPermEnvRef henv) env'

-- | Assume that the given named function has the supplied type and translates
-- to a SAW core definition given by name
heapster_assume_fun :: BuiltinContext -> Options -> HeapsterEnv ->
                       String -> String -> String -> TopLevel ()
heapster_assume_fun bic opts henv nm perms_string term_string =
  case lookupModDeclaringSym henv nm of
    Nothing ->
      fail ("Could not find symbol: " ++ nm)
    Just (Some lm) -> do
      sc <- getSharedContext
      let arch = llvmArch $ _transContext (lm ^. modTrans)
      let w = archReprWidth arch
      leq_proof <- case decideLeq (knownNat @1) w of
        Left pf -> return pf
        Right _ -> fail "LLVM arch width is 0!"
      env <- liftIO $ readIORef $ heapsterEnvPermEnvRef henv
      case lm ^. modTrans.transContext.symbolMap.at (L.Symbol nm) of
        Nothing -> error ("Unreachable: could not find symbol: " ++ nm)
        Just (LLVMHandleInfo _ h) ->
          let args = mkCruCtx $ handleArgTypes h
              ret = handleReturnType h in
          withKnownNat w $ withLeqProof leq_proof $
          case parseFunPermString env args ret perms_string of
            Left err -> fail $ show err
            Right (SomeFunPerm fun_perm) -> do
              perm_env <- liftIO $ readIORef (heapsterEnvPermEnvRef henv)
              fun_typ <- liftIO $ translateCompleteFunPerm sc perm_env fun_perm
              term_ident <- parseAndInsDef henv nm fun_typ term_string
              let env' = permEnvAddGlobalSymFun env
                                                (GlobalSymbol $ fromString nm)
                                                w
                                                fun_perm
                                                (globalOpenTerm term_ident)
              liftIO $ writeIORef (heapsterEnvPermEnvRef henv) env'


heapster_typecheck_mut_funs :: BuiltinContext -> Options -> HeapsterEnv ->
                               [(String, String)] -> TopLevel ()
heapster_typecheck_mut_funs bic opts henv fn_names_and_perms =
  let fst_nm = fst $ head fn_names_and_perms in
  case lookupModDefiningSym henv fst_nm of
    Nothing -> fail ("Could not find symbol definition: " ++ fst_nm)
    Just (some_lm@(Some lm)) -> do
      let arch = llvmArch $ _transContext (lm ^. modTrans)
      let w = archReprWidth arch
      env <- liftIO $ readIORef $ heapsterEnvPermEnvRef henv
      some_cfgs_and_perms <- forM fn_names_and_perms $ \(nm,perms_string) ->
        (getLLVMCFG arch <$>
         crucible_llvm_cfg bic opts some_lm nm) >>= \any_cfg ->
        case any_cfg of
          AnyCFG cfg ->
            do let args = mkCruCtx $ handleArgTypes $ cfgHandle cfg
               let ret = handleReturnType $ cfgHandle cfg
               case parseFunPermString env args ret perms_string of
                 Left err -> fail $ show err
                 Right (SomeFunPerm fun_perm) ->
                   return $ SomeCFGAndPerm (GlobalSymbol $
                                            fromString nm) cfg fun_perm
      sc <- getSharedContext
      let saw_modname = heapsterEnvSAWModule henv
      leq_proof <- case decideLeq (knownNat @1) w of
        Left pf -> return pf
        Right _ -> fail "LLVM arch width is 0!"
      env' <- liftIO $ withKnownNat w $ withLeqProof leq_proof $
        tcTranslateAddCFGs sc saw_modname w env some_cfgs_and_perms
      liftIO $ writeIORef (heapsterEnvPermEnvRef henv) env'


heapster_typecheck_fun :: BuiltinContext -> Options -> HeapsterEnv ->
                          String -> String -> TopLevel ()
heapster_typecheck_fun bic opts henv fn_name perms_string =
  heapster_typecheck_mut_funs bic opts henv [(fn_name, perms_string)]

heapster_print_fun_trans :: BuiltinContext -> Options -> HeapsterEnv ->
                            String -> TopLevel ()
heapster_print_fun_trans bic opts henv fn_name =
  do pp_opts <- getTopLevelPPOpts
     sc <- getSharedContext
     let saw_modname = heapsterEnvSAWModule henv
     fun_term <-
       fmap (fromJust . defBody) $
       liftIO $ scRequireDef sc $ mkSafeIdent saw_modname fn_name
     liftIO $ putStrLn $ scPrettyTerm pp_opts fun_term

heapster_export_coq :: BuiltinContext -> Options -> HeapsterEnv ->
                       String -> TopLevel ()
heapster_export_coq bic opts henv filename =
  do let coq_trans_conf = coqTranslationConfiguration [] []
     sc <- getSharedContext
     saw_mod <- liftIO $ scFindModule sc $ heapsterEnvSAWModule henv
     let coq_doc =
           vcat [preamblePlus coq_trans_conf
                 (string "From CryptolToCoq Require Import SAWCorePrelude."),
                 translateSAWModule coq_trans_conf saw_mod]
     liftIO $ writeFile filename (show coq_doc)

heapster_parse_test :: BuiltinContext -> Options -> Some LLVMModule ->
                       String -> String ->  TopLevel ()
heapster_parse_test bic opts some_lm fn_name perms_string =
  case some_lm of
    Some lm -> do
      let env = unClosed heapster_default_env -- FIXME: cl_env should be an argument
      let arch = llvmArch $ _transContext (lm ^. modTrans)
      any_cfg <- getLLVMCFG arch <$> crucible_llvm_cfg bic opts some_lm fn_name
      case any_cfg of
        AnyCFG cfg -> do
          let args = mkCruCtx $ handleArgTypes $ cfgHandle cfg
          let ret = handleReturnType $ cfgHandle cfg
          case parseFunPermString env args ret perms_string of
            Left err -> fail $ show err
            Right (SomeFunPerm fun_perm) ->
              liftIO $ putStrLn $ permPrettyString emptyPPInfo fun_perm
