{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ViewPatterns #-}

module SAWScript.HeapsterBuiltins
       ( heapster_init_env
       , heapster_init_env_debug
       , heapster_init_env_from_file
       , heapster_init_env_from_file_debug
       , heapster_init_env_for_files
       , heapster_init_env_for_files_debug
       , load_sawcore_from_file
       , heapster_get_cfg
       , heapster_typecheck_fun
       , heapster_typecheck_mut_funs
       , heapster_typecheck_fun_rename
       , heapster_typecheck_mut_funs_rename
       -- , heapster_typecheck_fun_rs
       -- , heapster_typecheck_fun_rename_rs
       , heapster_define_opaque_perm
       , heapster_define_recursive_perm
       , heapster_define_reachability_perm
       , heapster_define_recursive_shape
       , heapster_define_perm
       , heapster_define_llvmshape
       , heapster_define_opaque_llvmshape
       , heapster_define_rust_type
       , heapster_define_rust_type_qual
       , heapster_block_entry_hint
       , heapster_gen_block_perms_hint
       , heapster_join_point_hint
       , heapster_find_symbol
       , heapster_find_symbols
       , heapster_find_symbol_with_type
       , heapster_find_symbols_with_type
       , heapster_find_symbol_commands
       , heapster_find_trait_method_symbol
       , heapster_assume_fun
       , heapster_assume_fun_rename
       , heapster_translate_rust_type
       , heapster_assume_fun_rename_prim
       , heapster_assume_fun_multi
       , heapster_set_event_type
       , heapster_print_fun_trans
       , heapster_export_coq
       , heapster_parse_test
       , heapster_dump_ide_info
       , heapster_set_debug_level
       , heapster_set_translation_checks
       ) where

import Data.Maybe
import Data.String
import Data.List (find, intercalate, intersperse, isInfixOf, stripPrefix)
import qualified Data.List.Extra as List
import Data.IORef
import Data.Functor.Product
import Data.Functor.Constant (getConstant)
import Control.Applicative ( (<|>) )
import Control.Lens
import Control.Monad
import Control.Monad.Reader
import qualified Control.Monad.Fail as Fail
import System.Directory
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Lazy as TL
import qualified Data.Text.Lazy.IO as TLIO

import Data.Binding.Hobbits hiding (sym)

import Data.Parameterized.BoolRepr
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.TraversableF
import Data.Parameterized.TraversableFC

import qualified SAWSupport.Pretty as PPS (defaultPPOpts)

import SAWCore.Term.Functor
import SAWCore.Name
import SAWCore.Module as Mod
import CryptolSAWCore.Monadify
import SAWCore.SharedTerm
import SAWCore.Recognizer
import SAWCore.OpenTerm
import SAWCore.Typechecker
import SAWCore.SCTypeCheck
import qualified SAWCore.Term.Pretty as Pretty (scPrettyTerm, scPrettyTermInCtx)
import qualified SAWCore.UntypedAST as Un
import qualified SAWCore.Grammar as Un

import Lang.Crucible.Types
import Lang.Crucible.FunctionHandle
import Lang.Crucible.CFG.Core
import Lang.Crucible.LLVM.Extension
import Lang.Crucible.LLVM.MemModel
import qualified Lang.Crucible.LLVM.PrettyPrint as Crucible.LLVM
import Lang.Crucible.LLVM.Translation
-- import Lang.Crucible.LLVM.Translation.Types
import Lang.Crucible.LLVM.TypeContext
import Lang.Crucible.LLVM.DataLayout

import qualified Text.LLVM.AST as L
import qualified Text.LLVM.Parser as L
import qualified Text.PrettyPrint.HughesPJ as L (render)

import SAWCentral.TopLevel
import SAWCentral.Value
import SAWCentral.Options
import SAWCentral.LLVMBuiltins
import SAWCentral.Builtins
import SAWCentral.Crucible.LLVM.Builtins
import SAWCentral.Crucible.LLVM.MethodSpecIR

import Heapster.CruUtil
import Heapster.HintExtract
import Heapster.Permissions
import Heapster.SAWTranslation
import Heapster.PermParser
import Heapster.RustTypes (parseSome3FunPermFromRust, Some3FunPerm(..))
import Heapster.ParsedCtx
import qualified Heapster.IDESupport as HIDE
import Heapster.LLVMGlobalConst

import SAWCentral.Prover.Exporter
import SAWCoreCoq.Coq
import Prettyprinter

import SAWScript.Panic


-- | Build the SAW core term for the type @TpDesc@
tpDescTypeM :: MonadIO m => SharedContext -> m Term
tpDescTypeM sc = liftIO $ completeOpenTerm sc tpDescTypeOpenTerm

-- | Pretty-print a SAW core term with a 'String' prefix to 'stderr' if the
-- current debug level in the supplied 'HeapsterEnv' is above the supplied one
debugPrettyTermWithPrefix :: HeapsterEnv -> DebugLevel -> String -> Term ->
                             TopLevel ()
debugPrettyTermWithPrefix henv req_dlevel prefix trm =
  do dlevel <- liftIO $ readIORef $ heapsterEnvDebugLevel henv
     pp_opts <- getTopLevelPPOpts
     debugTrace req_dlevel dlevel (prefix ++
                                   Pretty.scPrettyTerm pp_opts trm) (return ())

-- | Check that a type equals the type described by a type description in a ctx
checkTypeAgreesWithDesc :: SharedContext -> PermEnv -> String -> Ident ->
                           CruCtx args -> Ident -> IO ()
checkTypeAgreesWithDesc sc env nm tp_ident ctx d_ident =
  do d_tp <- translateDescTypeFun sc env ctx $ identOpenTerm d_ident
     tp <- scGlobalDef sc tp_ident
     ok <- scConvertibleEval sc scTypeCheckWHNF True tp d_tp
     if ok then return () else
       do tp_norm <- scTypeCheckWHNF sc tp
          d_tp_norm <- scTypeCheckWHNF sc d_tp
          fail ("Type description for " ++ nm ++
                " does not match user-supplied type\n" ++
                "Type for description:\n" ++
                Pretty.scPrettyTermInCtx PPS.defaultPPOpts [] d_tp_norm ++ "\n" ++
                "User-supplied type:\n" ++
                Pretty.scPrettyTermInCtx PPS.defaultPPOpts [] tp_norm)

-- | Extract out the contents of the 'Right' of an 'Either', calling 'fail' if
-- the 'Either' is a 'Left'. The supplied 'String' describes the action (in
-- "ing" form, as in, "parsing") that was performed to create this 'Either'.
-- failOnLeft :: (MonadFail m, Show err) => String -> Either err a -> m a
-- failOnLeft action (Left err) = Fail.fail ("Error" ++ action ++ ": " ++ show err)
-- failOnLeft _ (Right a) = return a

-- | Extract out the contents of the 'Just' of a 'Maybe' wrapped in a
-- `MonadFail`, calling 'fail' on the given string if the `Maybe` is a
-- `Nothing`.
failOnNothing :: Fail.MonadFail m => String -> Maybe a -> m a
failOnNothing err_str Nothing = Fail.fail err_str
failOnNothing _ (Just a) = return a

-- | Extract the bit width of an architecture
archReprWidth :: ArchRepr arch -> NatRepr (ArchWidth arch)
archReprWidth (X86Repr w) = w

-- | Get the architecture of an LLVM module
llvmModuleArchRepr :: LLVMModule arch -> ArchRepr arch
llvmModuleArchRepr lm = llvmArch $ view transContext $ modTrans lm

-- | Get the bit width of the architecture of an LLVM module
llvmModuleArchReprWidth :: LLVMModule arch -> NatRepr (ArchWidth arch)
llvmModuleArchReprWidth = archReprWidth . llvmModuleArchRepr

-- | Get the 'TypeContext' of an LLVM module
llvmModuleTypeContext :: LLVMModule arch -> TypeContext
llvmModuleTypeContext lm = modTrans lm ^. transContext . llvmTypeCtx

-- | Look up the 'L.Declare' for an external symbol in an 'LLVMModule'
lookupFunctionDecl :: LLVMModule arch -> String -> Maybe L.Declare
lookupFunctionDecl lm nm =
  find ((fromString nm ==) . L.decName) $ L.modDeclares $ modAST lm

-- | Look up the 'L.Define' for a symbol defined in an 'LLVMModule'
lookupFunctionDef :: LLVMModule arch -> String -> Maybe L.Define
lookupFunctionDef lm nm =
  find ((fromString nm ==) . L.defName) $ L.modDefines $ modAST lm

-- | Lookup a the singnature for a symbol in an 'LLVMModule'. This
--   will find a signaure for either an external symbol, or for
--   a defined symbol
lookupFunctionDeclOrDef :: LLVMModule arch -> String -> Maybe L.Declare
lookupFunctionDeclOrDef lm nm =
  lookupFunctionDecl lm nm <|> (declareFromDefine <$> lookupFunctionDef lm nm)

-- | Look up the Crucible CFG for a defined symbol in an 'LLVMModule'
lookupFunctionCFG :: LLVMModule arch -> String -> IO (Maybe (AnyCFG Lang.Crucible.LLVM.Extension.LLVM))
lookupFunctionCFG lm nm =
  getTranslatedCFG (modTrans lm) (fromString nm) >>= \case
    Nothing -> return Nothing
    Just (_,cfg,_warns) -> return (Just cfg)

-- | Look up the argument and return types of a named function
lookupFunctionType :: LLVMModule arch -> String ->
                      TopLevel (Some CtxRepr, Some TypeRepr)
lookupFunctionType (lm :: LLVMModule arch) nm =
  case lookupFunctionDeclOrDef lm nm of
    Just decl ->
      do let w = llvmModuleArchReprWidth lm
         leq1_proof <- case decideLeq (knownNat @1) w of
           Left pf -> return pf
           Right _ -> fail "LLVM arch width is 0!"
         leq16_proof <- case decideLeq (knownNat @16) w of
           Left pf -> return pf
           Right _ -> fail "LLVM arch width is too small!"
         let ?ptrWidth = w
         let ?lc = llvmModuleTypeContext lm
         withLeqProof leq1_proof $ withLeqProof leq16_proof $
           llvmDeclToFunHandleRepr' @(ArchWidth arch) decl $ \args ret ->
           return (Some args, Some ret)
    Nothing ->
      fail ("Could not find symbol: " ++ nm)

-- | Look for the LLVM module in a 'HeapsterEnv' where a symbol is defined
lookupModDefiningSym :: HeapsterEnv -> String -> Maybe (Some LLVMModule)
lookupModDefiningSym env nm =
  find (\(Some lm) -> isJust (lookupFunctionDef lm nm)) $
  heapsterEnvLLVMModules env

-- | Look for any LLVM module in a 'HeapsterEnv' containing a symbol
lookupModContainingSym :: HeapsterEnv -> String -> Maybe (Some LLVMModule)
lookupModContainingSym env nm =
  find (\(Some lm) -> isJust (lookupFunctionDeclOrDef lm nm)) $
  heapsterEnvLLVMModules env

-- | An LLVM module plus a CFG for a specific function in that module
data ModuleAndCFG arch =
  ModuleAndCFG (LLVMModule arch) (AnyCFG Lang.Crucible.LLVM.Extension.LLVM)

-- | Look up the LLVM module and associated CFG for a symobl
lookupLLVMSymbolModAndCFG :: HeapsterEnv -> String -> IO (Maybe (Some ModuleAndCFG))
lookupLLVMSymbolModAndCFG henv nm =
  case lookupModDefiningSym henv nm of
    Just (Some lm) ->
      do res <- lookupFunctionCFG lm nm
         return ((Some . ModuleAndCFG lm) <$> res)
    Nothing -> return Nothing

heapster_default_env :: PermEnv
heapster_default_env = emptyPermEnv

-- | Based on the function of the same name in SAWCore.ParserUtils.
-- Unlike that function, this calls 'fail' instead of 'error'.
--
-- XXX: we only need one; unify these once the error handling gets fixed.
readModuleFromFile :: FilePath -> TopLevel (Un.Module, ModuleName)
readModuleFromFile path = do
  base <- liftIO getCurrentDirectory
  txt <- liftIO $ TLIO.readFile path
  case Un.parseSAW base path txt of
    Right m@(Un.Module (Un.PosPair _ mnm) _ _) -> pure (m, mnm)
    Left err -> fail $ "Module parsing failed:\n" ++ show err

-- | Parse the second given string as a term, the first given string being
-- used as the path for error reporting
--
-- XXX: this should be moved to saw-core once we have unified error
-- handling that'll allow it to not need to explicitly live in
-- TopLevel.
parseTermFromString :: String -> String -> TopLevel Un.UTerm
parseTermFromString nm term_string = do
  let base = ""
      path = "<" ++ nm ++ ">"
  case Un.parseSAWTerm base path (TL.pack term_string) of
    Right term -> pure term
    Left err -> fail $ "Term parsing failed:\n" ++ show err

-- | Find an unused identifier in a 'Module' by starting with a particular
-- 'String' and appending a number if necessary
findUnusedIdent :: Module -> String -> Ident
findUnusedIdent m str =
  fromJust $ find (isNothing . Mod.resolveName m . identBaseName) $
  map (mkSafeIdent (moduleName m)) $
  (str : map ((str ++) . show) [(0::Int) ..])

-- | Insert a SAW core definition into the SAW core module associated with a
-- 'HeapsterEnv', printing out the definition if the debug level is at least 2
heapsterInsertDef :: HeapsterEnv -> Ident -> Term -> Term -> TopLevel ()
heapsterInsertDef henv trm_ident trm_tp trm =
  do debugPrettyTermWithPrefix henv verboseDebugLevel
       ("Inserting def " ++ show trm_ident ++ " =\n") trm
     sc <- getSharedContext
     let mnm = heapsterEnvSAWModule henv
     liftIO $ scInsertDef sc mnm trm_ident trm_tp trm

-- | Parse the second given string as a term, check that it has the given type,
-- and, if the parsed term is not already an identifier, add it as a definition
-- in the current module using the first given string. If that first string is
-- already used, find another name for the definition. Return either the
-- identifer of the new definition or the identifier that was parsed.
parseAndInsDef :: HeapsterEnv -> String -> Term -> String -> TopLevel Ident
parseAndInsDef henv nm term_tp term_string =
  do sc <- getSharedContext
     un_term <- parseTermFromString nm term_string
     let mnm = heapsterEnvSAWModule henv
     typed_term <- liftIO $ scTypeCheckCompleteError sc (Just mnm) un_term
     liftIO $ scCheckSubtype sc (Just mnm) typed_term term_tp
     case typedVal typed_term of
       STApp _ _ _ (Constant (EC _ (ModuleIdentifier term_ident) _) _) ->
         return term_ident
       term -> do
         m <- liftIO $ scFindModule sc mnm
         let term_ident = findUnusedIdent m nm
         heapsterInsertDef henv term_ident term_tp term
         return term_ident

-- | Build a 'HeapsterEnv' associated with the given SAW core module and the
-- given 'LLVMModule's. Add any globals in the 'LLVMModule's to the returned
-- 'HeapsterEnv'.
mkHeapsterEnv :: DebugLevel -> ModuleName -> [Some LLVMModule] ->
                 TopLevel HeapsterEnv
mkHeapsterEnv dlevel saw_mod_name llvm_mods@(Some first_mod:_) =
  do sc <- getSharedContext
     let w = llvmModuleArchReprWidth first_mod
     let endianness =
           llvmDataLayout (modTrans first_mod ^. transContext ^. llvmTypeCtx)
           ^. intLayout
     leq_proof <- case decideLeq (knownNat @1) w of
       Left pf -> return pf
       Right _ -> fail "LLVM arch width is 0!"
     let globals = concatMap (\(Some lm) -> L.modGlobals $ modAST lm) llvm_mods
     env <-
       liftIO $ withKnownNat w $ withLeqProof leq_proof $
       foldM (permEnvAddGlobalConst sc saw_mod_name dlevel endianness w)
       heapster_default_env globals
     env_ref <- liftIO $ newIORef env
     dlevel_ref <- liftIO $ newIORef dlevel
     checks_ref <- liftIO $ newIORef doChecks
     tcfg_ref <- liftIO $ newIORef []
     return $ HeapsterEnv {
       heapsterEnvSAWModule = saw_mod_name,
       heapsterEnvPermEnvRef = env_ref,
       heapsterEnvLLVMModules = llvm_mods,
       heapsterEnvDebugLevel = dlevel_ref,
       heapsterEnvChecksFlag = checks_ref,
       heapsterEnvTCFGs = tcfg_ref
       }
mkHeapsterEnv _ _ [] = fail "mkHeapsterEnv: empty list of LLVM modules!"


heapster_init_env :: BuiltinContext -> Options ->
                     Text -> String -> TopLevel HeapsterEnv
heapster_init_env bic opts mod_str llvm_filename =
  heapster_init_env_gen bic opts noDebugLevel mod_str llvm_filename

heapster_init_env_debug :: BuiltinContext -> Options ->
                           Text -> String -> TopLevel HeapsterEnv
heapster_init_env_debug bic opts mod_str llvm_filename =
  heapster_init_env_gen bic opts traceDebugLevel mod_str llvm_filename

heapster_init_env_gen :: BuiltinContext -> Options -> DebugLevel ->
                         Text -> String -> TopLevel HeapsterEnv
heapster_init_env_gen _bic _opts dlevel mod_str llvm_filename =
  do llvm_mod <- llvm_load_module llvm_filename
     sc <- getSharedContext
     liftIO $ ensureCryptolMLoaded sc
     let saw_mod_name = mkModuleName [mod_str]
     mod_loaded <- liftIO $ scModuleIsLoaded sc saw_mod_name
     if mod_loaded then
       fail ("SAW module with name " ++ show mod_str ++ " already defined!")
       else return ()
     -- import SpecM by default
     let specMModuleName = mkModuleName ["SpecM"]
     preludeMod <- liftIO $ scFindModule sc specMModuleName
     liftIO $ scLoadModule sc (insImport (const True) preludeMod $
                                 emptyModule saw_mod_name)
     mkHeapsterEnv dlevel saw_mod_name [llvm_mod]

load_sawcore_from_file :: BuiltinContext -> Options -> String -> TopLevel ()
load_sawcore_from_file _ _ mod_filename =
  do sc <- getSharedContext
     liftIO $ ensureCryptolMLoaded sc
     (saw_mod, _) <- readModuleFromFile mod_filename
     liftIO $ tcInsertModule sc saw_mod

heapster_init_env_from_file :: BuiltinContext -> Options -> String -> String ->
                               TopLevel HeapsterEnv
heapster_init_env_from_file bic opts mod_filename llvm_filename =
  heapster_init_env_for_files_gen
  bic opts noDebugLevel mod_filename [llvm_filename]

heapster_init_env_from_file_debug :: BuiltinContext -> Options ->
                                     String -> String -> TopLevel HeapsterEnv
heapster_init_env_from_file_debug bic opts mod_filename llvm_filename =
  heapster_init_env_for_files_gen
  bic opts traceDebugLevel mod_filename [llvm_filename]

heapster_init_env_for_files_gen :: BuiltinContext -> Options -> DebugLevel ->
                                   String -> [String] ->
                                   TopLevel HeapsterEnv
heapster_init_env_for_files_gen _bic _opts dlevel mod_filename llvm_filenames =
  do llvm_mods <- mapM llvm_load_module llvm_filenames
     sc <- getSharedContext
     liftIO $ ensureCryptolMLoaded sc
     (saw_mod, saw_mod_name) <- readModuleFromFile mod_filename
     liftIO $ tcInsertModule sc saw_mod
     mkHeapsterEnv dlevel saw_mod_name llvm_mods

heapster_init_env_for_files :: BuiltinContext -> Options -> String -> [String] ->
                               TopLevel HeapsterEnv
heapster_init_env_for_files _bic _opts mod_filename llvm_filenames =
  heapster_init_env_for_files_gen _bic _opts noDebugLevel
                                  mod_filename llvm_filenames

heapster_init_env_for_files_debug :: BuiltinContext -> Options ->
                                     String -> [String] ->
                                     TopLevel HeapsterEnv
heapster_init_env_for_files_debug _bic _opts mod_filename llvm_filenames =
  heapster_init_env_for_files_gen _bic _opts traceDebugLevel
                                  mod_filename llvm_filenames

-- | Look up the CFG associated with a symbol name in a Heapster environment
heapster_get_cfg :: BuiltinContext -> Options -> HeapsterEnv ->
                    String -> TopLevel SAW_CFG
heapster_get_cfg _ _ henv nm =
  case lookupModDefiningSym henv nm of
    Just (Some lm) -> llvm_cfg (Some lm) nm
    Nothing -> fail ("Could not find CFG for symbol: " ++ nm)


-- | Define a new opaque named permission with the given name, arguments, and
-- Crucible type that translates to the given SAW core type with the supplied
-- type description
heapster_define_opaque_perm :: BuiltinContext -> Options -> HeapsterEnv ->
                               String -> String -> String -> String ->
                               String -> TopLevel ()
heapster_define_opaque_perm _bic _opts henv nm args_str tp_str term_str d_str =
  do env <- liftIO $ readIORef $ heapsterEnvPermEnvRef henv
     Some args <- parseCtxString "argument types" env args_str
     Some tp_perm <- parseTypeString "permission type" env tp_str
     sc <- getSharedContext
     term_tp <- liftIO $ translateExprTypeFunType sc env args
     term_ident <- parseAndInsDef henv nm term_tp term_str
     d_tp <- tpDescTypeM sc
     d_ident <- parseAndInsDef henv (nm ++ "__desc") d_tp d_str
     liftIO $ checkTypeAgreesWithDesc sc env nm term_ident args d_ident
     let env' = permEnvAddOpaquePerm env nm args tp_perm term_ident d_ident
     liftIO $ writeIORef (heapsterEnvPermEnvRef henv) env'


-- | Define a new recursive named permission with the given name, arguments,
-- type, and permission that it unfolds to
heapster_define_recursive_perm :: BuiltinContext -> Options -> HeapsterEnv ->
                                  String -> String -> String -> String ->
                                  TopLevel ()
heapster_define_recursive_perm _bic _opts henv nm args_str tp_str p_str =
  do env <- liftIO $ readIORef $ heapsterEnvPermEnvRef henv
     let mnm = heapsterEnvSAWModule henv
     sc <- getSharedContext

     -- Parse the arguments, the type, and the body
     Some args_ctx <- parseParsedCtxString "argument types" env args_str
     Some tp <- parseTypeString "permission type" env tp_str
     let args = parsedCtxCtx args_ctx
         args_p = CruCtxCons args (ValuePermRepr tp)
     mb_p <- parsePermInCtxString "permission" env
       (consParsedCtx nm (ValuePermRepr tp) args_ctx) tp p_str

     -- Generate the type description for the body of the recursive perm
     d_tp <- tpDescTypeM sc
     let d_ident = mkSafeIdent mnm (nm ++ "__desc")
     d_trm <- liftIO $ translateCompleteDescInCtx sc env args_p mb_p
     heapsterInsertDef henv d_ident d_tp d_trm

     -- Generate the function \args -> tpElemEnv args (Ind d) from the
     -- arguments to the type of the translation of the permission as the term
     let transf_ident = mkSafeIdent mnm nm
     transf_tp <- liftIO $ translateExprTypeFunType sc env args
     transf_trm <-
       liftIO $ translateIndTypeFun sc env args (globalOpenTerm d_ident)
     heapsterInsertDef henv transf_ident transf_tp transf_trm

     -- Add the recursive perm to the environment and update henv
     env' <-
       permEnvAddRecPermM env nm args tp transf_ident d_ident mb_p
       NameNonReachConstr
       (\_ _ -> return NoReachMethods)
     liftIO $ writeIORef (heapsterEnvPermEnvRef henv) env'


-- | Define a new recursive named permission with the given name, arguments,
-- type, and permission that it unfolds to, that forms a reachability
-- permission, meaning it has the form
--
-- > P<args,x> := eq(x) or q
--
-- where the name @P@ occurs exactly once and @x@ occurs not at all in
-- permission @q@. The last input should define a transitivity method as
-- described in the documentation for the 'ReachMethods' type.
heapster_define_reachability_perm :: BuiltinContext -> Options -> HeapsterEnv ->
                                     String -> String -> String -> String ->
                                     String -> TopLevel ()
heapster_define_reachability_perm _bic _opts henv nm args_str tp_str p_str trans_fun_str =
  do env <- liftIO $ readIORef $ heapsterEnvPermEnvRef henv
     let mnm = heapsterEnvSAWModule henv
     sc <- getSharedContext

     -- Parse the arguments, the type, and the translation type
     Some (tp :: TypeRepr tp) <- parseTypeString "permission type" env tp_str
     (Some pre_args_ctx,
      last_args_ctx :: ParsedCtx (RNil :> tp)) <-
       do some_args_ctx <- parseParsedCtxString "argument types" env args_str
          case some_args_ctx of
            Some args_ctx
              | CruCtxCons _ tp' <- parsedCtxCtx args_ctx
              , Just Refl <- testEquality tp tp' ->
                return (Some (parsedCtxUncons args_ctx), parsedCtxLast args_ctx)
            _ -> Fail.fail "Incorrect type for last argument of reachability perm"
     let args_ctx = appendParsedCtx pre_args_ctx last_args_ctx
     let args = parsedCtxCtx args_ctx
         args_p = CruCtxCons args (ValuePermRepr tp)
     mb_p <- parsePermInCtxString "permission" env
       (consParsedCtx nm (ValuePermRepr tp) args_ctx) tp p_str

     -- Generate the type description for the body of the recursive perm
     d_tp <- tpDescTypeM sc
     let d_ident = mkSafeIdent mnm (nm ++ "__desc")
     d_trm <- liftIO $ translateCompleteDescInCtx sc env args_p mb_p
     heapsterInsertDef henv d_ident d_tp d_trm

     -- Generate the function \args -> tpElemEnv args (Ind d) from the
     -- arguments to the type of the translation of the permission as the term
     let transf_ident = mkSafeIdent mnm nm
     transf_tp <- liftIO $ translateExprTypeFunType sc env args
     transf_trm <-
       liftIO $ translateIndTypeFun sc env args (globalOpenTerm d_ident)
     heapsterInsertDef henv transf_ident transf_tp transf_trm

     -- Add the recursive perm to the environment and update henv
     env' <-
       permEnvAddRecPermM env nm args tp transf_ident d_ident mb_p
       NameReachConstr
       (\npn tmp_env ->
           -- Return the ReachMethods structure, which contains trans_ident.
           -- Typecheck trans_ident with x:P<args,y>, y:P<args,z> -o x:P<args,z>
           do trans_fun_tp <-
                liftIO $
                translateCompletePureFunType sc tmp_env (CruCtxCons args tp)
                (nus (cruCtxProxies args :>: Proxy) $ \(ns :>: y :>: z) ->
                  MNil :>:
                  ValPerm_Named npn (namesToExprs (ns :>: y)) NoPermOffset :>:
                  ValPerm_Named npn (namesToExprs (ns :>: z)) NoPermOffset)
                (nus (cruCtxProxies args :>: Proxy) $ \(ns :>: _ :>: z) ->
                  ValPerm_Named npn (namesToExprs (ns :>: z)) NoPermOffset)
              trans_ident <-
                parseAndInsDef henv ("trans_" ++ nm) trans_fun_tp trans_fun_str
              return (ReachMethods trans_ident))
     liftIO $ writeIORef (heapsterEnvPermEnvRef henv) env'


-- | Helper function to add a recursive named shape to a 'PermEnv', adding all
-- the required identifiers to the given SAW core module
addRecNamedShape :: 1 <= w => HeapsterEnv -> String ->
                    CruCtx args -> NatRepr w ->
                    Mb (args :> LLVMShapeType w) (PermExpr (LLVMShapeType w)) ->
                    TopLevel PermEnv
addRecNamedShape henv nm args w mb_sh =
  -- Generate the type description for the body of the recursive shape
  do sc <- getSharedContext
     env <- liftIO $ readIORef $ heapsterEnvPermEnvRef henv
     let mnm = heapsterEnvSAWModule henv
     d_tp <- tpDescTypeM sc
     let d_ident = mkSafeIdent mnm (nm ++ "__desc")
         args_p = CruCtxCons args (LLVMShapeRepr w)
     d_trm <- liftIO $ translateCompleteDescInCtx sc env args_p mb_sh
     heapsterInsertDef henv d_ident d_tp d_trm

     -- Generate the function \args -> tpElemEnv args (Ind d) from the
     -- arguments to the type of the translation of the permission as the term
     let transf_ident = mkSafeIdent mnm nm
     transf_tp <- liftIO $ translateExprTypeFunType sc env args
     transf_trm <-
       liftIO $ translateIndTypeFun sc env args (globalOpenTerm d_ident)
     heapsterInsertDef henv transf_ident transf_tp transf_trm

     -- Add the recursive shape to the environment and update henv
     let nmsh = NamedShape nm args $ RecShapeBody mb_sh transf_ident d_ident
     return $ withKnownNat w $ permEnvAddNamedShape env nmsh


-- | Define a new recursive named permission with the given name, arguments,
-- type, and memory shape that it unfolds to
heapster_define_recursive_shape :: BuiltinContext -> Options -> HeapsterEnv ->
                                   String -> Int -> String -> String ->
                                   TopLevel ()
heapster_define_recursive_shape _bic _opts henv nm w_int args_str body_str =
  do env <- liftIO $ readIORef $ heapsterEnvPermEnvRef henv

     -- Parse the bit width, arguments, and the body
     SomeKnownNatGeq1 w <-
       failOnNothing "Shape width must be positive" $ someKnownNatGeq1 w_int
     Some args_ctx <- parseParsedCtxString "argument types" env args_str
     let args = parsedCtxCtx args_ctx
     mb_sh <- parseExprInCtxString env (LLVMShapeRepr w)
       (consParsedCtx nm (LLVMShapeRepr w) args_ctx) body_str

     -- Add the shape to the current environment
     env' <- addRecNamedShape henv nm args w mb_sh
     liftIO $ writeIORef (heapsterEnvPermEnvRef henv) env'


-- | Define a new named permission with the given name, arguments, and type
-- that is equivalent to the given permission.
heapster_define_perm :: BuiltinContext -> Options -> HeapsterEnv ->
                        String -> String -> String -> String ->
                        TopLevel ()
heapster_define_perm _bic _opts henv nm args_str tp_str perm_string =
  do env <- liftIO $ readIORef $ heapsterEnvPermEnvRef henv
     Some args_ctx <- parseParsedCtxString "argument types" env args_str
     let args = parsedCtxCtx args_ctx
     Some tp_perm <- parseTypeString "permission type" env tp_str
     perm <- parsePermInCtxString "permission body" env
                                   args_ctx tp_perm perm_string
     let env' = permEnvAddDefinedPerm env nm args tp_perm perm
     liftIO $ writeIORef (heapsterEnvPermEnvRef henv) env'


-- | Define a new named llvm shape with the given name, pointer width,
-- arguments, and definition as a shape
heapster_define_llvmshape :: BuiltinContext -> Options -> HeapsterEnv ->
                             String -> Int -> String -> String ->
                             TopLevel ()
heapster_define_llvmshape _bic _opts henv nm w_int args_str sh_str =
  do env <- liftIO $ readIORef $ heapsterEnvPermEnvRef henv
     (Some (Pair w LeqProof)) <-
       failOnNothing "Shape width must be positive" $ someNatGeq1 w_int
     Some args_ctx <- parseParsedCtxString "argument types" env args_str
     let args = parsedCtxCtx args_ctx
     mb_sh <- parseExprInCtxString env (LLVMShapeRepr w) args_ctx sh_str
     let env' = withKnownNat w $ permEnvAddDefinedShape env nm args mb_sh
     liftIO $ writeIORef (heapsterEnvPermEnvRef henv) env'


-- | Define a new opaque llvm shape with the given name, pointer width,
-- arguments, expression for the length in bytes, SAW core expression for a
-- type-level function from the Heapster translations of the argument types to a
-- SAW core type, and SAW core expression for a type description of that type
heapster_define_opaque_llvmshape :: BuiltinContext -> Options -> HeapsterEnv ->
                                    String -> Int -> String -> String ->
                                    String -> String -> TopLevel ()
heapster_define_opaque_llvmshape _bic _opts henv nm w_int args_str len_str tp_str d_str =
  do env <- liftIO $ readIORef $ heapsterEnvPermEnvRef henv
     (Some (Pair w LeqProof)) <-
       failOnNothing "Shape width must be positive" $ someNatGeq1 w_int
     Some args_ctx <- parseParsedCtxString "argument types" env args_str
     let args = parsedCtxCtx args_ctx
     mb_len <- parseExprInCtxString env (BVRepr w) args_ctx len_str
     sc <- getSharedContext
     d_tp <- tpDescTypeM sc
     d_id <- parseAndInsDef henv (nm ++ "__desc") d_tp d_str
     tp_tp <- liftIO $ translateExprTypeFunType sc env args
     tp_id <- parseAndInsDef henv nm tp_tp tp_str
     liftIO $ checkTypeAgreesWithDesc sc env nm tp_id args d_id
     let env' =
           withKnownNat w $ permEnvAddOpaqueShape env nm args mb_len tp_id d_id
     liftIO $ writeIORef (heapsterEnvPermEnvRef henv) env'


-- | Define a new named LLVM shape from a Rust type declaration and an optional
-- crate name that qualifies the type name
heapster_define_rust_type_qual_opt :: BuiltinContext -> Options -> HeapsterEnv ->
                                      Maybe String -> String -> TopLevel ()
heapster_define_rust_type_qual_opt _bic _opts henv maybe_crate str =
  -- NOTE: Looking at first LLVM module to determine pointer width. Need to
  -- think more to determine if this is always a safe thing to do (e.g. are
  -- there ever circumstances where different modules have different pointer
  -- widths?)
  do Some lm <- failOnNothing ("No LLVM modules found")
                              (listToMaybe $ heapsterEnvLLVMModules henv)
     let w = llvmModuleArchReprWidth lm
     leq_proof <- case decideLeq (knownNat @1) w of
       Left pf -> return pf
       Right _ -> fail "LLVM arch width is 0!"
     env <- liftIO $ readIORef (heapsterEnvPermEnvRef henv)
     let crated_nm nm = maybe nm (\crate -> crate ++ "::" ++ nm) maybe_crate
     withKnownNat w $ withLeqProof leq_proof $
       do partialShape <- parseRustTypeString env w str
          case partialShape of
            NonRecShape nm ctx sh ->
              do let nsh = NamedShape { namedShapeName = crated_nm nm
                                      , namedShapeArgs = ctx
                                      , namedShapeBody = DefinedShapeBody sh
                                      }
                     env' = permEnvAddNamedShape env nsh
                 liftIO $ writeIORef (heapsterEnvPermEnvRef henv) env'
            RecShape nm ctx mb_sh ->
              do let nm' = crated_nm nm
                 env' <- addRecNamedShape henv nm' ctx w mb_sh
                 liftIO $ writeIORef (heapsterEnvPermEnvRef henv) env'


-- | Define a new named LLVM shape from a Rust type declaration
heapster_define_rust_type :: BuiltinContext -> Options -> HeapsterEnv ->
                             String -> TopLevel ()
heapster_define_rust_type bic opts henv str =
  heapster_define_rust_type_qual_opt bic opts henv Nothing str

-- | Define a new named LLVM shape from a Rust type declaration and a crate name
-- that qualifies the Rust type by being prefixed to the name of the LLVM shape
heapster_define_rust_type_qual :: BuiltinContext -> Options -> HeapsterEnv ->
                                  String -> String -> TopLevel ()
heapster_define_rust_type_qual bic opts henv crate str =
  heapster_define_rust_type_qual_opt bic opts henv (Just crate) str

-- | Add Heapster type-checking hint for some blocks in a function given by
-- name. The blocks to receive the hint are those specified in the list, or all
-- blocks if the list is empty.
heapster_add_block_hints :: HeapsterEnv -> String -> [Int] ->
                            (forall ext blocks init ret args.
                             CFG ext blocks init ret -> BlockID blocks args ->
                             TopLevel (BlockHintSort args)) ->
                            TopLevel ()
heapster_add_block_hints henv nm blks hintF =
  do env <- liftIO $ readIORef $ heapsterEnvPermEnvRef henv
     Some (ModuleAndCFG _ (AnyCFG cfg)) <-
       failOnNothing ("Could not find symbol definition: " ++ nm) =<<
         io (lookupLLVMSymbolModAndCFG henv nm)
     let h = cfgHandle cfg
         blocks = fmapFC blockInputs $ cfgBlockMap cfg
         block_idxs = fmapFC (blockIDIndex . blockID) $ cfgBlockMap cfg
     blkIDs <- case blks of
       -- If an empty list is given, add a hint to every block
       [] -> pure $ toListFC (Some . BlockID) block_idxs
       _ -> forM blks $ \blk ->
         failOnNothing ("Block ID " ++ show blk ++
                        " not found in function " ++ nm)
                       (fmapF BlockID <$> Ctx.intIndex blk (Ctx.size blocks))
     env' <- foldM (\env' (Some blkID) ->
                     permEnvAddHint env' <$> Hint_Block <$>
                     BlockHint h blocks blkID <$>
                     hintF cfg blkID)
       env blkIDs
     liftIO $ writeIORef (heapsterEnvPermEnvRef henv) env'

-- | Add a hint to the Heapster type-checker that Crucible block number @block@ in
-- function @fun@ should have permissions @perms@ on its inputs
heapster_block_entry_hint :: BuiltinContext -> Options -> HeapsterEnv ->
                             String -> Int -> String -> String -> String ->
                             TopLevel ()
heapster_block_entry_hint _bic _opts henv nm blk top_args_str ghosts_str perms_str =
  do env <- liftIO $ readIORef $ heapsterEnvPermEnvRef henv
     Some top_args_p <-
       parseParsedCtxString "top-level argument context" env top_args_str
     Some ghosts_p <-
       parseParsedCtxString "ghost argument context" env ghosts_str
     let top_args = parsedCtxCtx top_args_p
         ghosts = parsedCtxCtx ghosts_p
     heapster_add_block_hints henv nm [blk] $ \cfg blkID ->
       let block_args =
             mkCruCtx $ blockInputs $
             (cfgBlockMap cfg) Ctx.! (blockIDIndex blkID) in
       BlockEntryHintSort top_args ghosts <$>
       parsePermsString "block entry permissions" env
       (appendParsedCtx (appendParsedCtx
                         top_args_p (mkArgsParsedCtx block_args)) ghosts_p)
       perms_str


-- | Add a hint to the Heapster type-checker to *generalize* (recursively
-- replace all instances of @eq(const)@ with @exists x. eq(x)@) all permissions
-- on the inputs of the given Crucible blocks numbers. If the given list is
-- empty, do so for every block in the CFG.
heapster_gen_block_perms_hint :: BuiltinContext -> Options -> HeapsterEnv ->
                                 String -> [Int] -> TopLevel ()
heapster_gen_block_perms_hint _bic _opts henv nm blks =
  heapster_add_block_hints henv nm blks $ \_ _ -> return GenPermsHintSort

-- | Add a hint to the Heapster type-checker to make a join point at each of the
-- given block numbers, meaning that all entries to the given blocks are merged
-- into a single entrypoint, whose permissions are given by the first call to
-- the block
heapster_join_point_hint :: BuiltinContext -> Options -> HeapsterEnv ->
                            String -> [Int] -> TopLevel ()
heapster_join_point_hint _bic _opts henv nm blks =
  heapster_add_block_hints henv nm blks $ \_ _ -> return JoinPointHintSort

-- | Search for all symbol names in any LLVM module in a 'HeapsterEnv' that
-- contain the supplied string as a substring
heapster_find_symbols :: BuiltinContext -> Options -> HeapsterEnv -> String ->
                         TopLevel [String]
heapster_find_symbols _bic _opts henv str =
  return $
  concatMap (\(Some lm) ->
              mapMaybe (\(L.Symbol nm) ->
                         if isInfixOf str nm then Just nm else Nothing) $
              map L.decName (L.modDeclares $ modAST lm) ++
              map L.defName (L.modDefines $ modAST lm)) $
  heapsterEnvLLVMModules henv

-- | Search for a symbol name in any LLVM module in a 'HeapsterEnv' that
-- contains the supplied string as a substring, failing if there is not exactly
-- one such symbol
heapster_find_symbol :: BuiltinContext -> Options -> HeapsterEnv -> String ->
                        TopLevel String
heapster_find_symbol bic opts henv str =
  heapster_find_symbols bic opts henv str >>= \syms ->
  case syms of
    [sym] -> return sym
    [] -> fail ("No symbol found matching string: " ++ str)
    _ -> fail ("Found multiple symbols matching string " ++ str ++ ": " ++
               concat (intersperse ", " $ map show syms))

-- | Extract the 'String' name of an LLVM symbol
symString :: L.Symbol -> String
symString (L.Symbol str) = str

-- | Extract the function type of an LLVM definition
defFunType :: L.Define -> L.Type
defFunType defn =
  L.FunTy (L.defRetType defn) (map L.typedType
                               (L.defArgs defn)) (L.defVarArgs defn)

-- | Extract the function type of an LLVM declaration
decFunType :: L.Declare -> L.Type
decFunType decl =
  L.FunTy (L.decRetType decl) (L.decArgs decl) (L.decVarArgs decl)

-- | Search for all symbols with the supplied string as a substring that have
-- the supplied LLVM type
heapster_find_symbols_with_type :: BuiltinContext -> Options -> HeapsterEnv ->
                                   String -> String -> TopLevel [String]
heapster_find_symbols_with_type _bic _opts henv str tp_str =
  case L.parseType tp_str of
    Left err ->
      fail ("Error parsing LLVM type: " ++ tp_str ++ "\n" ++ show err)
    Right tp@(L.FunTy _ _ _) ->
      return $
      concatMap (\(Some lm) ->
                  mapMaybe (\decl ->
                             if isInfixOf str (symString $ L.decName decl) &&
                                decFunType decl == tp
                             then Just (symString $ L.decName decl) else Nothing)
                  (L.modDeclares $ modAST lm)
                  ++
                  mapMaybe (\defn ->
                             if isInfixOf str (symString $ L.defName defn) &&
                                defFunType defn == tp
                             then Just (symString $ L.defName defn) else Nothing)
                  (L.modDefines $ modAST lm)) $
      heapsterEnvLLVMModules henv
    Right tp ->
      fail ("Expected an LLVM function type, but found: " ++ show tp)

-- | Search for a symbol by name and Crucible type in any LLVM module in a
-- 'HeapsterEnv' that contains the supplied string as a substring
heapster_find_symbol_with_type :: BuiltinContext -> Options -> HeapsterEnv ->
                                  String -> String -> TopLevel String
heapster_find_symbol_with_type bic opts henv str tp_str =
  heapster_find_symbols_with_type bic opts henv str tp_str >>= \syms ->
  case syms of
    [sym] -> return sym
    [] -> fail ("No symbol found matching string: " ++ str ++
                " and type: " ++ tp_str)
    _ -> fail ("Found multiple symbols matching string " ++ str ++
               " and type: " ++ tp_str ++ ": " ++
               concat (intersperse ", " $ map show syms))

-- | Print a 'String' as a SAW-script string literal, escaping any double quotes
-- or newlines
print_as_saw_script_string :: String -> String
print_as_saw_script_string str =
  "\"" ++ concatMap (\c -> case c of
                        '\"' -> "\\\""
                        '\n' -> "\\\n\\"
                        _ -> [c]) str ++ "\"";

-- | Map a search string @str@ to a newline-separated sequence of SAW-script
-- commands @"heapster_find_symbol_with_type str tp"@, one for each LLVM type
-- @tp@ associated with a symbol whose name contains @str@
heapster_find_symbol_commands :: BuiltinContext -> Options -> HeapsterEnv ->
                                 String -> TopLevel String
heapster_find_symbol_commands _bic _opts henv str =
  return $
  concatMap (\tp ->
              "heapster_find_symbol_with_type env\n  \"" ++ str ++ "\"\n  " ++
              print_as_saw_script_string (L.render $ Crucible.LLVM.ppType tp) ++ ";\n") $
  concatMap (\(Some lm) ->
              mapMaybe (\decl ->
                         if isInfixOf str (symString $ L.decName decl)
                         then Just (decFunType decl)
                         else Nothing)
              (L.modDeclares $ modAST lm)
              ++
              mapMaybe (\defn ->
                         if isInfixOf str (symString $ L.defName defn)
                         then Just (defFunType defn) else Nothing)
              (L.modDefines $ modAST lm)) $
  heapsterEnvLLVMModules henv

-- | Search for a symbol name in any LLVM module in a 'HeapsterEnv' that
-- corresponds to the supplied string, which should be of the form:
-- @"trait::method<type>"@. Fails if there is not exactly one such symbol.
heapster_find_trait_method_symbol :: BuiltinContext -> Options ->
                                     HeapsterEnv -> String -> TopLevel String
heapster_find_trait_method_symbol bic opts henv str
  | _openingBracket:typeWithClosingBracket <- instType
  , Just (unbracketedType, _closingBracket) <- List.unsnoc typeWithClosingBracket
  = let queryStr = unbracketedType
                <> "$u20$as$u20$"
                <> trait
                <> "$GT$"
                <> (show . length) method
                <> method
    in heapster_find_symbol bic opts henv queryStr
  | otherwise
  = fail ("Ill-formed query string: " ++ str)
  where
    (traitMethod, instType) = span (/= '<') str

    (colonTrait, method) =
      let (revMethod, revTrait) = span (/= ':') (reverse traitMethod)
      in ((reverse . drop 2) revTrait, reverse revMethod)

    trait = intercalate ".." $ List.splitOn "::" colonTrait


-- | Assume that the given named function has the supplied type and translates
-- to a SAW core definition given by the second name
heapster_assume_fun_rename :: BuiltinContext -> Options -> HeapsterEnv ->
                              String -> String -> String -> String ->
                              TopLevel ()
heapster_assume_fun_rename _bic _opts henv nm nm_to perms_string term_string =
  do Some lm <- failOnNothing ("Could not find symbol: " ++ nm)
                              (lookupModContainingSym henv nm)
     sc <- getSharedContext
     let w = llvmModuleArchReprWidth lm
     leq_proof <- case decideLeq (knownNat @1) w of
       Left pf -> return pf
       Right _ -> fail "LLVM arch width is 0!"
     env <- liftIO $ readIORef $ heapsterEnvPermEnvRef henv
     (Some cargs, Some ret) <- lookupFunctionType lm nm
     let args = mkCruCtx cargs
     withKnownNat w $ withLeqProof leq_proof $ do
        SomeFunPerm fun_perm <-
          parseFunPermStringMaybeRust "permissions" w env args ret perms_string
        env' <- liftIO $ readIORef (heapsterEnvPermEnvRef henv)
        fun_typ <- liftIO $ translateCompleteFunPerm sc env fun_perm
        term_ident <- parseAndInsDef henv nm_to fun_typ term_string
        let env'' = permEnvAddGlobalSymFun env'
                                           (GlobalSymbol $ fromString nm)
                                           w
                                           fun_perm
                                           (globalOpenTerm term_ident)
        liftIO $ writeIORef (heapsterEnvPermEnvRef henv) env''

-- | Create a new SAW core primitive named @nm@ with type @tp@ in the module
-- associated with the supplied Heapster environment, and return its identifier
insPrimitive :: HeapsterEnv -> String -> Term -> TopLevel Ident
insPrimitive henv nm tp =
  do sc <- getSharedContext
     let mnm = heapsterEnvSAWModule henv
     let ident = mkSafeIdent mnm nm
     liftIO $ scDeclarePrim sc mnm ident PrimQualifier tp
     return ident

-- | Assume that the given named function has the supplied type and translates
-- to a SAW core definition given by the second name
heapster_assume_fun_rename_prim :: BuiltinContext -> Options -> HeapsterEnv ->
                                   String -> String -> String -> TopLevel ()
heapster_assume_fun_rename_prim _bic _opts henv nm nm_to perms_string =
  do Some lm <- failOnNothing ("Could not find symbol: " ++ nm)
                              (lookupModContainingSym henv nm)
     sc <- getSharedContext
     let w = llvmModuleArchReprWidth lm
     leq_proof <- case decideLeq (knownNat @1) w of
       Left pf -> return pf
       Right _ -> fail "LLVM arch width is 0!"
     env <- liftIO $ readIORef $ heapsterEnvPermEnvRef henv
     (Some cargs, Some ret) <- lookupFunctionType lm nm
     let args = mkCruCtx cargs
     withKnownNat w $ withLeqProof leq_proof $ do
        SomeFunPerm fun_perm <-
          parseFunPermStringMaybeRust "permissions" w env args ret perms_string
        env' <- liftIO $ readIORef (heapsterEnvPermEnvRef henv)
        fun_typ <- liftIO $ translateCompleteFunPerm sc env fun_perm
        term_ident <- insPrimitive henv nm_to fun_typ
        let env'' = permEnvAddGlobalSymFun env'
                                           (GlobalSymbol $ fromString nm)
                                           w
                                           fun_perm
                                           (globalOpenTerm term_ident)
        liftIO $ writeIORef (heapsterEnvPermEnvRef henv) env''

-- | Assume that the given named function has the supplied type and translates
-- to a SAW core definition given by name
heapster_assume_fun :: BuiltinContext -> Options -> HeapsterEnv ->
                       String -> String -> String -> TopLevel ()
heapster_assume_fun _bic _opts henv nm perms_string term_string =
  heapster_assume_fun_rename _bic _opts henv nm nm perms_string term_string

-- | Assume that the given named function has one or more permissions and
-- associated translations, each of which is as given in 'heapster_assume_fun'
heapster_assume_fun_multi :: BuiltinContext -> Options -> HeapsterEnv ->
                             String -> [(String, String)] -> TopLevel ()
heapster_assume_fun_multi _bic _opts henv nm perms_terms_strings =
  do Some lm <- failOnNothing ("Could not find symbol: " ++ nm)
                              (lookupModContainingSym henv nm)
     sc <- getSharedContext
     let w = llvmModuleArchReprWidth lm
     leq_proof <- case decideLeq (knownNat @1) w of
       Left pf -> return pf
       Right _ -> fail "LLVM arch width is 0!"
     (Some (cargs :: CtxRepr cargs),
      Some (ret :: TypeRepr ret)) <- lookupFunctionType lm nm
     let args = mkCruCtx cargs
     env <- liftIO $ readIORef (heapsterEnvPermEnvRef henv)
     perms_terms :: [(SomeFunPerm (CtxToRList cargs) ret, OpenTerm)] <-
       forM (zip perms_terms_strings [0::Int ..]) $ \((perms_string,
                                                       term_string), i) ->
       withKnownNat w $ withLeqProof leq_proof $
       do some_fun_perm <-
            parseFunPermStringMaybeRust "permissions" w env args ret perms_string
          fun_typ <-
            case some_fun_perm of
              SomeFunPerm fun_perm ->
                liftIO $ translateCompleteFunPerm sc env fun_perm
          term_ident <-
            parseAndInsDef henv (nm ++ "__" ++ show i) fun_typ term_string
          return (some_fun_perm, globalOpenTerm term_ident)
     let env' =
           withKnownNat w $ withLeqProof leq_proof $
           permEnvAddGlobalSymFunMulti env (GlobalSymbol $
                                            fromString nm) w perms_terms
     liftIO $ writeIORef (heapsterEnvPermEnvRef henv) env'


-- | Type-check a list of potentially mutually recursive functions, each against
-- its own function permission, specified as a list of pairs of a function
-- name and a 'String' representation of its permission
heapster_typecheck_mut_funs :: BuiltinContext -> Options -> HeapsterEnv ->
                               [(String, String)] -> TopLevel ()
heapster_typecheck_mut_funs bic opts henv =
  heapster_typecheck_mut_funs_rename bic opts henv .
  map (\(nm, perms_string) -> (nm, nm, perms_string))

-- | Type-check a list of potentially mutually recursive functions, each against
-- its own function permission, potentially renaming the functions in the
-- generated SAW core specifications. The functions are specified as a list of
-- triples @(nm,nm_to,perms)@ of the function symbol @nm@ in the binary, the
-- desired name @mn_to@ for the SAW core specification, and the permissions
-- @perms@ given as a 'String'
heapster_typecheck_mut_funs_rename ::
  BuiltinContext -> Options -> HeapsterEnv ->
  [(String, String, String)] -> TopLevel ()
heapster_typecheck_mut_funs_rename _bic opts henv fn_names_and_perms =
  do let fst_nm =
           case fn_names_and_perms of
             (nm, _, _):_ -> nm
             -- TODO: Give a proper error message here instead of panicking,
             -- and document the non-empty list requirement. See #2096.
             [] -> panic "heapster_typecheck_mut_funs_rename"
                         [ "Unexpected empty list of mutually recursive functions"
                         , "See https://github.com/GaloisInc/saw-script/issues/2096"
                         ]
     Some lm <- failOnNothing ("Could not find symbol definition: " ++ fst_nm)
                              (lookupModDefiningSym henv fst_nm)
     let w = llvmModuleArchReprWidth lm
     let endianness =
           llvmDataLayout (modTrans lm ^. transContext ^. llvmTypeCtx)
           ^. intLayout
     dlevel <- liftIO $ readIORef $ heapsterEnvDebugLevel henv
     checks <- liftIO $ readIORef $ heapsterEnvChecksFlag henv
     LeqProof <- case decideLeq (knownNat @16) w of
       Left pf -> return pf
       Right _ -> fail "LLVM arch width is < 16!"
     LeqProof <- case decideLeq (knownNat @1) w of
       Left pf -> return pf
       Right _ -> panic "heapster_typecheck_mut_funs_rename" ["1 > 16!"]
     some_cfgs_and_perms <- forM fn_names_and_perms $ \(nm, nm_to, perms_string) ->
       do AnyCFG cfg <-
            failOnNothing ("Could not find symbol definition: " ++ nm) =<<
              io (lookupFunctionCFG lm nm)
          env <- liftIO $ readIORef $ heapsterEnvPermEnvRef henv
          let args = mkCruCtx $ handleArgTypes $ cfgHandle cfg
          let ret = handleReturnType $ cfgHandle cfg
          SomeFunPerm fun_perm <-
            withKnownNat w $
            parseFunPermStringMaybeRust "permissions" w env args ret perms_string
          let mods = [ modAST m | Some m <- heapsterEnvLLVMModules henv ]
          hints <- case extractHints env mods fun_perm cfg of
            Left err -> fail ("Error parsing LLVM-level hints: " ++ err)
            Right hints -> return hints
          let env' = foldlFC (\e h -> maybe e (permEnvAddHint e) (getConstant h))
                             env
                             hints
          liftIO $ writeIORef (heapsterEnvPermEnvRef henv) env'
          return (SomeCFGAndPerm (GlobalSymbol $
                                  fromString nm) nm_to cfg fun_perm)
     env <- liftIO $ readIORef $ heapsterEnvPermEnvRef henv
     sc <- getSharedContext
     let saw_modname = heapsterEnvSAWModule henv
     (env', tcfgs) <- liftIO $
       let ?ptrWidth = w in
       tcTranslateAddCFGs sc saw_modname env checks endianness dlevel
       some_cfgs_and_perms
     liftIO $ writeIORef (heapsterEnvPermEnvRef henv) env'
     liftIO $ modifyIORef (heapsterEnvTCFGs henv) (\old -> map Some tcfgs ++ old)
     forM_ fn_names_and_perms $ \(_, nm_to, _) ->
       warnErrs nm_to =<< heapsterFunTrans henv nm_to
  where warnErrs :: String -> Term -> TopLevel ()
        warnErrs nm (asApplyAll -> (asGlobalDef -> Just "SpecM.errorS",
                                    [_ev, _a, asStringLit -> Just msg]))
          | Just msg_body <- stripPrefix implicationFailurePrefix (T.unpack msg)
          = let pref = "WARNING: Heapster implication failure while typechecking "
             in io $ printOutLn opts Warn (pref ++ nm ++ ":\n" ++ msg_body ++ "\n")
        warnErrs nm (asLambda -> Just (_, _, t)) = warnErrs nm t
        warnErrs nm (asApp -> Just (f, arg)) = warnErrs nm arg >> warnErrs nm f
        warnErrs nm (asCtor -> Just (_, args)) = mapM_ (warnErrs nm) args
        warnErrs nm (asRecursorApp -> Just (_, _, ixs, arg)) = mapM_ (warnErrs nm) (arg:ixs)
        warnErrs nm (asTupleValue -> Just ts) = mapM_ (warnErrs nm) ts
        warnErrs nm (asTupleSelector -> Just (t, _)) = warnErrs nm t
        warnErrs nm (asRecordValue -> Just ts) = mapM_ (warnErrs nm) ts
        warnErrs nm (asRecordSelector -> Just (t, _)) = warnErrs nm t
        warnErrs nm (asArrayValue -> Just (_, ts)) = mapM_ (warnErrs nm) ts
        warnErrs _ _ = return ()


-- | Type-check a single function against a function permission
heapster_typecheck_fun :: BuiltinContext -> Options -> HeapsterEnv ->
                          String -> String -> TopLevel ()
heapster_typecheck_fun bic opts henv fn_name perms_string =
  heapster_typecheck_mut_funs bic opts henv [(fn_name, perms_string)]

-- | Type-check a single function against a function permission and generate a
-- SAW core specification with a potentially different name
heapster_typecheck_fun_rename :: BuiltinContext -> Options -> HeapsterEnv ->
                                 String -> String -> String -> TopLevel ()
heapster_typecheck_fun_rename bic opts henv fn_name fn_name_to perms_string =
  heapster_typecheck_mut_funs_rename bic opts henv [(fn_name, fn_name_to,
                                                     perms_string)]

{-
heapster_typecheck_fun_rs :: BuiltinContext -> Options -> HeapsterEnv ->
                             String -> String -> TopLevel ()
heapster_typecheck_fun_rs bic opts henv fn_name perms_string =
  heapster_typecheck_fun bic opts henv

heapster_typecheck_fun_rename_rs :: BuiltinContext -> Options -> HeapsterEnv ->
                                    String -> String -> String -> TopLevel ()
heapster_typecheck_fun_rename_rs bic opts henv fn_name fn_name_to perms_string =
  heapster_typecheck_mut_funs_rename bic opts henv [(fn_name, fn_name_to,
                                                     perms_string)]
-}

-- | Set the event type for the remaining Heapster translations
heapster_set_event_type :: BuiltinContext -> Options -> HeapsterEnv ->
                           String -> TopLevel ()
heapster_set_event_type _bic _opts henv term_string =
  do sc <- getSharedContext
     ev_tp <-
       liftIO $ completeOpenTerm sc $ dataTypeOpenTerm "SpecM.EvType" []
     ev_id <- parseAndInsDef henv "HeapsterEv" ev_tp term_string
     liftIO $ modifyIORef' (heapsterEnvPermEnvRef henv) $ \env ->
       env { permEnvEventType = EventType (globalOpenTerm ev_id) }

-- | Fetch the SAW core definition associated with a name
heapsterFunTrans :: HeapsterEnv -> String -> TopLevel Term
heapsterFunTrans henv fn_name =
  do sc <- getSharedContext
     let saw_modname = heapsterEnvSAWModule henv
     fun_term <-
       fmap (fromJust . defBody) $
       liftIO $ scRequireDef sc $ mkSafeIdent saw_modname fn_name
     bodies <-
       fmap (fmap fst) $
       liftIO $ scResolveName sc $ T.pack $ fn_name ++ "__bodies"
     liftIO $ scUnfoldConstants sc bodies fun_term >>=
              sawLetMinimize sc >>= betaNormalize sc

-- | Fetch the SAW core definition associated with a name and print it
heapster_print_fun_trans :: BuiltinContext -> Options -> HeapsterEnv ->
                            String -> TopLevel ()
heapster_print_fun_trans _bic _opts henv fn_name =
  do pp_opts <- getTopLevelPPOpts
     fun_term <- heapsterFunTrans henv fn_name
     liftIO $ putStrLn $ Pretty.scPrettyTerm pp_opts fun_term

-- | Export all definitions in the SAW core module associated with a Heapster
-- environment to a Coq file with the given name
heapster_export_coq :: BuiltinContext -> Options -> HeapsterEnv ->
                       String -> TopLevel ()
heapster_export_coq _bic _opts henv filename =
  do let coq_trans_conf = coqTranslationConfiguration [] []
     sc <- getSharedContext
     saw_mod <- liftIO $ scFindModule sc $ heapsterEnvSAWModule henv
     let coq_doc =
           vcat [preamble coq_trans_conf {
                   postPreamble =
                       "From CryptolToCoq Require Import " ++
                       "SAWCorePrelude SpecMPrimitivesForSAWCore SAWCoreBitvectors.\n" },
                 translateSAWModule coq_trans_conf saw_mod]
     liftIO $ writeFile filename (show coq_doc)

-- | Set the Hepaster debug level
heapster_set_debug_level :: BuiltinContext -> Options -> HeapsterEnv ->
                            Int -> TopLevel ()
heapster_set_debug_level _ _ env l =
  liftIO $ writeIORef (heapsterEnvDebugLevel env) (DebugLevel l)

-- | Turn on or off the translation checks in the Heapster-to-SAW translation
heapster_set_translation_checks :: BuiltinContext -> Options -> HeapsterEnv ->
                                   Bool -> TopLevel ()
heapster_set_translation_checks _ _ env f =
  liftIO $ writeIORef (heapsterEnvChecksFlag env) (ChecksFlag f)

-- | Parse a Rust type from an input string, translate it to a Heapster function
-- permission, and print out that Heapster permission on stdout
heapster_translate_rust_type :: BuiltinContext -> Options -> HeapsterEnv ->
                                String -> TopLevel ()
heapster_translate_rust_type _bic _opts henv perms_string =
  do env <- liftIO $ readIORef $ heapsterEnvPermEnvRef henv
     let w64 = (knownNat @64::NatRepr 64)
     leq_proof <- case decideLeq (knownNat @1) w64 of
       Left pf -> return pf
       Right _ -> fail "LLVM arch width is 0!"
     withKnownNat w64 $ withLeqProof leq_proof $ do
        Some3FunPerm fun_perm <-
          parseSome3FunPermFromRust env w64 perms_string
        liftIO $ putStrLn $ permPrettyString emptyPPInfo fun_perm

-- | Parse a Heapster function permission from a 'String' and print it to
-- stdout, using a particular symbol in an LLVM module as the type of the
-- function that the permission applies to
heapster_parse_test :: BuiltinContext -> Options -> Some LLVMModule ->
                       String -> String -> TopLevel ()
heapster_parse_test _bic _opts _some_lm@(Some lm) fn_name perms_string =
  do let env = heapster_default_env -- FIXME: env should be an argument
     let _arch = llvmModuleArchRepr lm
     AnyCFG cfg <-
       failOnNothing ("Could not find symbol: " ++ fn_name) =<<
         io (lookupFunctionCFG lm fn_name)
     let args = mkCruCtx $ handleArgTypes $ cfgHandle cfg
     let ret = handleReturnType $ cfgHandle cfg
     SomeFunPerm fun_perm <- parseFunPermString "permissions" env args
                                                ret perms_string
     liftIO $ putStrLn $ permPrettyString emptyPPInfo fun_perm

-- | Dump the IDE information contained in a Heapster environment to a JSON file
heapster_dump_ide_info :: BuiltinContext -> Options -> HeapsterEnv -> String ->
                          TopLevel ()
heapster_dump_ide_info _bic _opts henv filename = do
  -- heapster_typecheck_mut_funs bic opts henv [(fnName, perms)]
  penv <- io $ readIORef (heapsterEnvPermEnvRef henv)
  tcfgs <- io $ readIORef (heapsterEnvTCFGs henv)
  io $ HIDE.printIDEInfo penv tcfgs filename emptyPPInfo
