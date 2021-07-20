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
{-# LANGUAGE ImplicitParams #-}

module SAWScript.HeapsterBuiltins
       ( heapster_init_env
       , heapster_init_env_from_file
       , heapster_init_env_for_files
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
       , heapster_define_irt_recursive_perm
       , heapster_define_irt_recursive_shape
       , heapster_define_reachability_perm
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
       , heapster_find_trait_method_symbol
       , heapster_assume_fun
       , heapster_assume_fun_rename
       , heapster_assume_fun_rename_prim
       , heapster_assume_fun_multi
       , heapster_print_fun_trans
       , heapster_export_coq
       , heapster_parse_test
       ) where

import Data.Maybe
import qualified Data.Map as Map
import Data.String
import Data.List
import Data.List.Extra (splitOn)
import Data.IORef
import Data.Functor.Product
import Control.Lens
import Control.Monad
import Control.Monad.IO.Class
import qualified Control.Monad.Fail as Fail
import System.Directory
import qualified Data.ByteString.Lazy as BL
import qualified Data.ByteString.Lazy.UTF8 as BL
import GHC.TypeLits
import Data.Text (Text)

import Data.Binding.Hobbits hiding (sym)
import qualified Data.Type.RList as RL

import Data.Parameterized.BoolRepr
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.TraversableF
import Data.Parameterized.TraversableFC

import Verifier.SAW.Term.Functor
import Verifier.SAW.Module as Mod
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
import Lang.Crucible.LLVM.Extension
import Lang.Crucible.LLVM.MemModel
import Lang.Crucible.LLVM.Translation
-- import Lang.Crucible.LLVM.Translation.Types
import Lang.Crucible.LLVM.TypeContext
import Lang.Crucible.LLVM.DataLayout

import qualified Text.LLVM.AST as L

import SAWScript.TopLevel
import SAWScript.Value
import SAWScript.Options
import SAWScript.LLVMBuiltins
import SAWScript.Builtins
import SAWScript.Crucible.LLVM.Builtins
import SAWScript.Crucible.LLVM.MethodSpecIR

import Verifier.SAW.Heapster.CruUtil
import Verifier.SAW.Heapster.Permissions
import Verifier.SAW.Heapster.SAWTranslation
import Verifier.SAW.Heapster.IRTTranslation
import Verifier.SAW.Heapster.PermParser
import Verifier.SAW.Heapster.ParsedCtx

import SAWScript.Prover.Exporter
import Verifier.SAW.Translation.Coq
import Prettyprinter


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
llvmModuleArchRepr lm = llvmArch $ _transContext $ modTrans lm

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

-- | Look up the Crucible CFG for a defined symbol in an 'LLVMModule'
lookupFunctionCFG :: LLVMModule arch -> String -> Maybe (AnyCFG Lang.Crucible.LLVM.Extension.LLVM)
lookupFunctionCFG lm nm =
  snd <$> Map.lookup (fromString nm) (cfgMap $ modTrans lm)

-- | Look up the argument and return types of a named function
lookupFunctionType :: LLVMModule arch -> String ->
                      TopLevel (Some CtxRepr, Some TypeRepr)
lookupFunctionType (lm :: LLVMModule arch) nm =
  case (lookupFunctionDecl lm nm, lookupFunctionCFG lm nm) of
    (Just decl, _) ->
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
    (_, Just (AnyCFG cfg)) ->
      return (Some (cfgArgTypes cfg), Some (cfgReturnType cfg))
    (Nothing, Nothing) ->
      fail ("Could not find symbol: " ++ nm)

-- | Look for the LLVM module in a 'HeapsterEnv' where a symbol is defined
lookupModDefiningSym :: HeapsterEnv -> String -> Maybe (Some LLVMModule)
lookupModDefiningSym env nm =
  find (\(Some lm) -> Map.member (fromString nm) (cfgMap $ modTrans lm)) $
  heapsterEnvLLVMModules env

-- | Look for any LLVM module in a 'HeapsterEnv' containing a symbol
lookupModContainingSym :: HeapsterEnv -> String -> Maybe (Some LLVMModule)
lookupModContainingSym env nm =
  find (\(Some lm) ->
         isJust (lookupFunctionDecl lm nm) || isJust (lookupFunctionCFG lm nm)) $
  heapsterEnvLLVMModules env

-- | An LLVM module plus a CFG for a specific function in that module
data ModuleAndCFG arch =
  ModuleAndCFG (LLVMModule arch) (AnyCFG Lang.Crucible.LLVM.Extension.LLVM)

-- | Look up the LLVM module and associated CFG for a symobl
lookupLLVMSymbolModAndCFG :: HeapsterEnv -> String -> Maybe (Some ModuleAndCFG)
lookupLLVMSymbolModAndCFG henv nm =
  case lookupModDefiningSym henv nm of
    Just (Some lm) ->
      (Some . ModuleAndCFG lm) <$> lookupFunctionCFG lm nm
    Nothing -> Nothing

heapster_default_env :: PermEnv
heapster_default_env = emptyPermEnv

-- | Based on the function of the same name in Verifier.SAW.ParserUtils.
-- Unlike that function, this calls 'fail' instead of 'error'.
readModuleFromFile :: FilePath -> TopLevel (Un.Module, ModuleName)
readModuleFromFile path = do
  base <- liftIO getCurrentDirectory
  b <- liftIO $ BL.readFile path
  case Un.parseSAW base path b of
    Right m@(Un.Module (Un.PosPair _ mnm) _ _) -> pure (m, mnm)
    Left err -> fail $ "Module parsing failed:\n" ++ show err

-- | Parse the second given string as a term, the first given string being
-- used as the path for error reporting
parseTermFromString :: String -> String -> TopLevel Un.Term
parseTermFromString nm term_string = do
  let base = ""
      path = "<" ++ nm ++ ">"
  case Un.parseSAWTerm base path (BL.fromString term_string) of
    Right term -> pure term
    Left err -> fail $ "Term parsing failed:\n" ++ show err

-- | Find an unused identifier in a 'Module' by starting with a particular
-- 'String' and appending a number if necessary
findUnusedIdent :: Module -> String -> Ident
findUnusedIdent m str =
  fromJust $ find (isNothing . Mod.resolveName m . identBaseName) $
  map (mkSafeIdent (moduleName m)) $
  (str : map ((str ++) . show) [(0::Int) ..])

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
       STApp _ _ (Constant (EC _ (ModuleIdentifier term_ident) _) _) ->
         return term_ident
       term -> do
         m <- liftIO $ scFindModule sc mnm
         let term_ident = findUnusedIdent m nm
         liftIO $ scInsertDef sc mnm term_ident term_tp term
         return term_ident


heapster_init_env :: BuiltinContext -> Options -> Text -> String ->
                     TopLevel HeapsterEnv
heapster_init_env _bic _opts mod_str llvm_filename =
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
     perm_env_ref <- liftIO $ newIORef heapster_default_env
     return $ HeapsterEnv {
       heapsterEnvSAWModule = saw_mod_name,
       heapsterEnvPermEnvRef = perm_env_ref,
       heapsterEnvLLVMModules = [llvm_mod]
       }

load_sawcore_from_file :: BuiltinContext -> Options -> String -> TopLevel ()
load_sawcore_from_file _ _ mod_filename =
  do sc <- getSharedContext
     (saw_mod, _) <- readModuleFromFile mod_filename
     liftIO $ tcInsertModule sc saw_mod

heapster_init_env_from_file :: BuiltinContext -> Options -> String -> String ->
                               TopLevel HeapsterEnv
heapster_init_env_from_file _bic _opts mod_filename llvm_filename =
  do llvm_mod <- llvm_load_module llvm_filename
     sc <- getSharedContext
     (saw_mod, saw_mod_name) <- readModuleFromFile mod_filename
     liftIO $ tcInsertModule sc saw_mod
     perm_env_ref <- liftIO $ newIORef heapster_default_env
     return $ HeapsterEnv {
       heapsterEnvSAWModule = saw_mod_name,
       heapsterEnvPermEnvRef = perm_env_ref,
       heapsterEnvLLVMModules = [llvm_mod]
       }

heapster_init_env_for_files :: BuiltinContext -> Options -> String -> [String] ->
                               TopLevel HeapsterEnv
heapster_init_env_for_files _bic _opts mod_filename llvm_filenames =
  do llvm_mods <- mapM llvm_load_module llvm_filenames
     sc <- getSharedContext
     (saw_mod, saw_mod_name) <- readModuleFromFile mod_filename
     liftIO $ tcInsertModule sc saw_mod
     perm_env_ref <- liftIO $ newIORef heapster_default_env
     return $ HeapsterEnv {
       heapsterEnvSAWModule = saw_mod_name,
       heapsterEnvPermEnvRef = perm_env_ref,
       heapsterEnvLLVMModules = llvm_mods
       }

-- | Look up the CFG associated with a symbol name in a Heapster environment
heapster_get_cfg :: BuiltinContext -> Options -> HeapsterEnv ->
                    String -> TopLevel SAW_CFG
heapster_get_cfg _ _ henv nm =
  case lookupModDefiningSym henv nm of
    Just (Some lm) -> llvm_cfg (Some lm) nm
    Nothing -> fail ("Could not find CFG for symbol: " ++ nm)

-- | Define a new opaque named permission with the given name, arguments, and
-- type, that translates to the given named SAW core definition
heapster_define_opaque_perm :: BuiltinContext -> Options -> HeapsterEnv ->
                               String -> String -> String -> String ->
                               TopLevel ()
heapster_define_opaque_perm _bic _opts henv nm args_str tp_str term_string =
  do env <- liftIO $ readIORef $ heapsterEnvPermEnvRef henv
     Some args <- parseCtxString "argument types" env args_str
     Some tp_perm <- parseTypeString "permission type" env tp_str
     sc <- getSharedContext
     term_tp <- liftIO $
       translateCompleteTypeInCtx sc env args (nus (cruCtxProxies args) $
                                               const $ ValuePermRepr tp_perm)
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
  nm args_str tp_str p_strs trans_str fold_fun_str unfold_fun_str =
    do env <- liftIO $ readIORef $ heapsterEnvPermEnvRef henv
       sc <- getSharedContext

       -- Parse the arguments, the type, and the translation type
       Some args_ctx <- parseParsedCtxString "argument types" env args_str
       let args = parsedCtxCtx args_ctx
       Some tp <- parseTypeString "permission type" env tp_str
       trans_tp <- liftIO $ 
         translateCompleteTypeInCtx sc env args (nus (cruCtxProxies args) $
                                                 const $ ValuePermRepr tp)
       trans_ident <- parseAndInsDef henv nm trans_tp trans_str

       -- Use permEnvAddRecPermM to tie the knot of adding a recursive
       -- permission whose cases and fold/unfold identifiers depend on that
       -- recursive permission being defined
       env' <-
         permEnvAddRecPermM env nm args tp trans_ident NameNonReachConstr
         (\_ tmp_env ->
           forM p_strs $
           parsePermInCtxString "disjunctive perm" tmp_env args_ctx tp)
         (\npn cases tmp_env ->
           do let or_tp = foldr1 (mbMap2 ValPerm_Or) cases
                  nm_tp = nus (cruCtxProxies args)
                    (\ns -> ValPerm_Named npn (namesToExprs ns) NoPermOffset)
              fold_fun_tp <- liftIO $
                translateCompletePureFun sc tmp_env args (singletonValuePerms
                                                          <$> or_tp) nm_tp
              unfold_fun_tp <- liftIO $
                translateCompletePureFun sc tmp_env args (singletonValuePerms
                                                          <$> nm_tp) or_tp
              fold_ident   <- parseAndInsDef henv ("fold" ++ nm) fold_fun_tp fold_fun_str
              unfold_ident <- parseAndInsDef henv ("unfold" ++ nm) unfold_fun_tp unfold_fun_str
              return (fold_ident, unfold_ident))
         (\_ _ -> return NoReachMethods)
       liftIO $ writeIORef (heapsterEnvPermEnvRef henv) env'

-- | Define a new recursive named permission with the given name, arguments,
-- and type, auto-generating SAWCore definitions using `IRT`
heapster_define_irt_recursive_perm :: BuiltinContext -> Options -> HeapsterEnv ->
                                      String -> String -> String -> [String] ->
                                      TopLevel ()
heapster_define_irt_recursive_perm _bic _opts henv nm args_str tp_str p_strs =
  do env <- liftIO $ readIORef $ heapsterEnvPermEnvRef henv
     sc <- getSharedContext

     -- Parse the arguments and type
     Some args_ctx <- parseParsedCtxString "argument types" env args_str
     let args = parsedCtxCtx args_ctx
     Some tp <- parseTypeString "permission type" env tp_str
     let mnm = heapsterEnvSAWModule henv
         trans_ident = mkSafeIdent mnm (nm ++ "_IRT")

     -- Use permEnvAddRecPermM to tie the knot of adding a recursive
     -- permission whose cases and fold/unfold identifiers depend on that
     -- recursive permission being defined
     env' <-
       permEnvAddRecPermM env nm args tp trans_ident NameNonReachConstr
       (\_ tmp_env ->
         forM p_strs $
         parsePermInCtxString "disjunctive perm" tmp_env args_ctx tp)
       (\npn cases tmp_env -> liftIO $
         do let or_tp = foldr1 (mbMap2 ValPerm_Or) cases
                nm_tp = nus (cruCtxProxies args)
                  (\ns -> ValPerm_Named npn (namesToExprs ns) NoPermOffset)
            -- translate the list of type variables
            (TypedTerm ls_tm ls_tp, ixs) <-
              translateCompletePermIRTTyVars sc tmp_env npn args or_tp
            let ls_ident = mkSafeIdent mnm (nm ++ "_IRTTyVars")
            scInsertDef sc mnm ls_ident ls_tp ls_tm
            -- translate the type description
            (TypedTerm d_tm d_tp) <-
              translateCompleteIRTDesc sc tmp_env ls_ident args or_tp ixs
            let d_ident = mkSafeIdent mnm (nm ++ "_IRTDesc")
            scInsertDef sc mnm d_ident d_tp d_tm
            -- translate the final definition
            (TypedTerm tp_tm tp_tp) <-
              translateCompleteIRTDef sc tmp_env ls_ident d_ident args
            scInsertDef sc mnm trans_ident tp_tp tp_tm
            -- translate the fold and unfold functions
            fold_fun_tp <-
              translateCompletePureFun sc tmp_env args (singletonValuePerms
                                                        <$> or_tp) nm_tp
            unfold_fun_tp <-
              translateCompletePureFun sc tmp_env args (singletonValuePerms
                                                        <$> nm_tp) or_tp
            fold_fun_tm <-
              translateCompleteIRTFoldFun sc tmp_env ls_ident d_ident
                                          trans_ident args
            unfold_fun_tm <-
              translateCompleteIRTUnfoldFun sc tmp_env ls_ident d_ident
                                            trans_ident args
            let fold_ident   = mkSafeIdent mnm ("fold"   ++ nm ++ "_IRT")
            let unfold_ident = mkSafeIdent mnm ("unfold" ++ nm ++ "_IRT")
            scInsertDef sc mnm fold_ident   fold_fun_tp   fold_fun_tm
            scInsertDef sc mnm unfold_ident unfold_fun_tp unfold_fun_tm
            return (fold_ident, unfold_ident))
       (\_ _ -> return NoReachMethods)
     liftIO $ writeIORef (heapsterEnvPermEnvRef henv) env'

-- | Define a new recursive named shape with the given name, arguments, and
-- body, auto-generating SAWCore definitions using `IRT`
heapster_define_irt_recursive_shape :: BuiltinContext -> Options -> HeapsterEnv ->
                                      String -> Int -> String -> String ->
                                      TopLevel ()
heapster_define_irt_recursive_shape _bic _opts henv nm w_int args_str body_str =
  do env <- liftIO $ readIORef $ heapsterEnvPermEnvRef henv
     SomeKnownNatGeq1 w <-
       failOnNothing "Shape width must be positive" $ someKnownNatGeq1 w_int
     sc <- getSharedContext

     -- Parse the arguments
     Some args_ctx <- parseParsedCtxString "argument types" env args_str
     let args = parsedCtxCtx args_ctx
         mnm = heapsterEnvSAWModule henv
         trans_ident = mkSafeIdent mnm (nm ++ "_IRT")

     -- Parse the body
     let tmp_nsh = partialRecShape w nm args Nothing trans_ident
         tmp_env = permEnvAddNamedShape env tmp_nsh
         mb_args = nus (cruCtxProxies args) namesToExprs
     body <- parseExprInCtxString tmp_env (LLVMShapeRepr w) args_ctx body_str
     abs_body <-
       failOnNothing "recursive shape applied to different arguments in its body" $
         fmap (mbCombine RL.typeCtxProxies) . mbMaybe $
           mbMap2 (abstractNS nm args) mb_args body

     -- Add the named shape to scope using the functions from IRTTranslation.hs
     env' <- liftIO $ addIRTRecShape sc mnm env nm args abs_body trans_ident
     liftIO $ writeIORef (heapsterEnvPermEnvRef henv) env'

-- | A temporary named recursive shape with `error`s for `fold_ident`,
-- `unfold_ident`, and optionally `body`.
partialRecShape :: NatRepr w -> String -> CruCtx args ->
                   Maybe (Mb (args :> LLVMShapeType w) (PermExpr (LLVMShapeType w))) ->
                   Ident -> NamedShape 'True args w
partialRecShape _ nm args mb_body trans_ident =
  let body_err =
        error "Analyzing recursive shape cases before it is defined!" in
  NamedShape nm args $
  RecShapeBody (fromMaybe body_err mb_body) trans_ident Nothing

-- | Given a named recursive shape name, arguments, body, and `trans_ident`,
-- insert its definition and definitions for its fold and unfold functions
-- using the functions in `IRTTranslation.hs`. Returns a modified
-- `PermEnv` with the new named shape added.
addIRTRecShape :: (1 <= w, KnownNat w) => SharedContext -> ModuleName ->
                  PermEnv -> String -> CruCtx args ->
                  Mb (args :> LLVMShapeType w) (PermExpr (LLVMShapeType w)) ->
                  Ident -> IO PermEnv
addIRTRecShape sc mnm env nm args body trans_ident =
  do let tmp_nsh = partialRecShape knownNat nm args (Just body) trans_ident
         tmp_env = permEnvAddNamedShape env tmp_nsh
         nsh_unf = unfoldNamedShape tmp_nsh <$>
                     nus (cruCtxProxies args) namesToExprs
         nsh_fld = nus (cruCtxProxies args) $ \ns ->
                     PExpr_NamedShape Nothing Nothing tmp_nsh (namesToExprs ns)
     -- translate the list of type variables
     (TypedTerm ls_tm ls_tp, ixs) <-
       translateCompleteShapeIRTTyVars sc tmp_env tmp_nsh
     let ls_ident = mkSafeIdent mnm (nm ++ "_IRTTyVars")
     scInsertDef sc mnm ls_ident ls_tp ls_tm
     -- translate the type description
     (TypedTerm d_tm d_tp) <-
       translateCompleteIRTDesc sc tmp_env ls_ident args nsh_unf ixs
     let d_ident = mkSafeIdent mnm (nm ++ "_IRTDesc")
     scInsertDef sc mnm d_ident d_tp d_tm
     -- translate the final definition
     (TypedTerm tp_tm tp_tp) <-
       translateCompleteIRTDef sc tmp_env ls_ident d_ident args
     scInsertDef sc mnm trans_ident tp_tp tp_tm
     -- translate the fold and unfold functions
     fold_fun_tp <-
       translateCompletePureFun sc tmp_env args
         (singletonValuePerms . ValPerm_LLVMBlockShape <$> nsh_unf)
         (ValPerm_LLVMBlockShape <$> nsh_fld)
     unfold_fun_tp <-
       translateCompletePureFun sc tmp_env args
         (singletonValuePerms . ValPerm_LLVMBlockShape <$> nsh_fld)
         (ValPerm_LLVMBlockShape <$> nsh_unf)
     fold_fun_tm <-
       translateCompleteIRTFoldFun sc tmp_env ls_ident d_ident
                                   trans_ident args
     unfold_fun_tm <-
       translateCompleteIRTUnfoldFun sc tmp_env ls_ident d_ident
                                     trans_ident args
     let fold_ident   = mkSafeIdent mnm ("fold"   ++ nm ++ "_IRT")
     let unfold_ident = mkSafeIdent mnm ("unfold" ++ nm ++ "_IRT")
     scInsertDef sc mnm fold_ident   fold_fun_tp   fold_fun_tm
     scInsertDef sc mnm unfold_ident unfold_fun_tp unfold_fun_tm
     let nsh = NamedShape nm args $
                 RecShapeBody body trans_ident (Just (fold_ident, unfold_ident))
     return $ permEnvAddNamedShape env nsh

-- | Define a new reachability permission
heapster_define_reachability_perm :: BuiltinContext -> Options -> HeapsterEnv ->
                                     String -> String -> String -> String ->
                                     String -> String -> String -> String ->
                                     TopLevel ()
heapster_define_reachability_perm _bic _opts henv
  nm args_str tp_str p_str trans_tp_str fold_fun_str unfold_fun_str trans_fun_str =
    do env <- liftIO $ readIORef $ heapsterEnvPermEnvRef henv
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
       trans_tp <- liftIO $ 
         translateCompleteTypeInCtx sc env args (nus (cruCtxProxies args) $
                                                 const $ ValuePermRepr tp)
       trans_tp_ident <- parseAndInsDef henv nm trans_tp trans_tp_str

       -- Use permEnvAddRecPermM to tie the knot of adding a recursive
       -- permission whose cases and fold/unfold identifiers depend on that
       -- recursive permission being defined
       env' <-
         permEnvAddRecPermM env nm args tp trans_tp_ident NameReachConstr
         (\_ tmp_env ->
           -- Return the disjunctive cases, which for P<args,e> are eq(e) and p
           do p <- parsePermInCtxString "disjunctive perm" tmp_env args_ctx tp p_str
              return [nus (cruCtxProxies args) (\(_ :>: n) ->
                                                 ValPerm_Eq $ PExpr_Var n),
                      p])
         (\npn cases tmp_env ->
           -- Return the Idents for the fold and unfold functions, which
           -- includes type-checking them, using or_tp = \args. rec perm body,
           -- where the body = the or of all the cases, and nm_tp =
           -- \args.P<args>
           do let or_tp = foldr1 (mbMap2 ValPerm_Or) cases
                  nm_tp = nus (cruCtxProxies args)
                    (\ns -> ValPerm_Named npn (namesToExprs ns) NoPermOffset)
              -- Typecheck fold against body -o P<args>
              fold_fun_tp <- liftIO $
                translateCompletePureFun sc tmp_env args (singletonValuePerms
                                                          <$> or_tp) nm_tp
              -- Typecheck fold against P<args> -o body
              unfold_fun_tp <- liftIO $
                translateCompletePureFun sc tmp_env args (singletonValuePerms
                                                          <$> nm_tp) or_tp
              -- Build identifiers foldXXX and unfoldXXX
              fold_ident <-
                parseAndInsDef henv ("fold" ++ nm) fold_fun_tp fold_fun_str
              unfold_ident <-
                parseAndInsDef henv ("unfold" ++ nm) unfold_fun_tp unfold_fun_str
              return (fold_ident, unfold_ident))
         (\npn tmp_env ->
           -- Return the ReachMethods structure, which contains trans_ident.
           -- Typecheck trans_ident with x:P<args,y>, y:P<args,z> -o x:P<args,z>
           do trans_fun_tp <-
                liftIO $
                translateCompletePureFun sc tmp_env (CruCtxCons args tp)
                (nus (cruCtxProxies args :>: Proxy) $ \(ns :>: y :>: z) ->
                  MNil :>:
                  ValPerm_Named npn (namesToExprs (ns :>: y)) NoPermOffset :>:
                  ValPerm_Named npn (namesToExprs (ns :>: z)) NoPermOffset)
                (nus (cruCtxProxies args :>: Proxy) $ \(ns :>: _ :>: z) ->
                  ValPerm_Named npn (namesToExprs (ns :>: z)) NoPermOffset)
              trans_ident <-
                parseAndInsDef henv ("trans" ++ nm) trans_fun_tp trans_fun_str
              return (ReachMethods trans_ident))
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
     perm <- parsePermInCtxString "disjunctive perm" env
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
-- arguments, expression for the length in bytes, and SAW core expression for a
-- type-level function from the Heapster translations of the argument types to a
-- SAW core type
heapster_define_opaque_llvmshape :: BuiltinContext -> Options -> HeapsterEnv ->
                                    String -> Int -> String -> String -> String ->
                                    TopLevel ()
heapster_define_opaque_llvmshape _bic _opts henv nm w_int args_str len_str tp_str =
  do env <- liftIO $ readIORef $ heapsterEnvPermEnvRef henv
     (Some (Pair w LeqProof)) <-
       failOnNothing "Shape width must be positive" $ someNatGeq1 w_int
     Some args_ctx <- parseParsedCtxString "argument types" env args_str
     let args = parsedCtxCtx args_ctx
     mb_len <- parseExprInCtxString env (BVRepr w) args_ctx len_str
     sc <- getSharedContext
     tp_tp <- liftIO $
       translateCompleteTypeInCtx sc env args (nus (cruCtxProxies args) $
                                               const $ ValuePermRepr $
                                               LLVMShapeRepr w)
     tp_id <- parseAndInsDef henv nm tp_tp tp_str
     let env' = withKnownNat w $ permEnvAddOpaqueShape env nm args mb_len tp_id
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
            RecShape nm ctx sh ->
              do sc <- getSharedContext
                 let mnm = heapsterEnvSAWModule henv
                     nm' = crated_nm nm
                     trans_ident = mkSafeIdent mnm (nm' ++ "_IRT")
                 env' <-
                   liftIO $ addIRTRecShape sc mnm env nm' ctx sh trans_ident
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
       failOnNothing ("Could not find symbol definition: " ++ nm) $
       lookupLLVMSymbolModAndCFG henv nm
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

-- | Search for a symbol name in any LLVM module in a 'HeapsterEnv' that
-- corresponds to the supplied string, which should be of the form:
-- "trait::method<type>". Fails if there is not exactly one such symbol.
heapster_find_trait_method_symbol :: BuiltinContext -> Options ->
                                     HeapsterEnv -> String -> TopLevel String
heapster_find_trait_method_symbol bic opts henv str =
  if length instType >= 2 then
    let unbracketedType = (init . tail) instType
        queryStr = unbracketedType
                <> "$u20$as$u20$"
                <> trait
                <> "$GT$"
                <> (show . length) method
                <> method
    in heapster_find_symbol bic opts henv queryStr
  else
    fail ("Ill-formed query string: " ++ str)
  where
    (traitMethod, instType) = span (/= '<') str

    (colonTrait, method) =
      let (revMethod, revTrait) = span (/= ':') (reverse traitMethod)
      in ((reverse . drop 2) revTrait, reverse revMethod)

    trait = intercalate ".." $ splitOn "::" colonTrait

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
     i <- liftIO $ scFreshGlobalVar sc
     liftIO $ scRegisterName sc i (ModuleIdentifier ident)
     let pn = PrimName i ident tp
     t <- liftIO $ scFlatTermF sc (Primitive pn)
     liftIO $ scRegisterGlobal sc ident t
     liftIO $ scModifyModule sc mnm $ \m ->
        insDef m $ Def { defIdent = ident,
                         defQualifier = PrimQualifier,
                         defType = tp,
                         defBody = Nothing }
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


heapster_typecheck_mut_funs :: BuiltinContext -> Options -> HeapsterEnv ->
                               [(String, String)] -> TopLevel ()
heapster_typecheck_mut_funs bic opts henv =
  heapster_typecheck_mut_funs_rename bic opts henv .
  map (\(nm, perms_string) -> (nm, nm, perms_string)) 

heapster_typecheck_mut_funs_rename ::
  BuiltinContext -> Options -> HeapsterEnv ->
  [(String, String, String)] -> TopLevel ()
heapster_typecheck_mut_funs_rename _bic _opts henv fn_names_and_perms =
  do let (fst_nm, _, _) = head fn_names_and_perms
     Some lm <- failOnNothing ("Could not find symbol definition: " ++ fst_nm)
                              (lookupModDefiningSym henv fst_nm)
     let w = llvmModuleArchReprWidth lm
     let endianness =
           llvmDataLayout (modTrans lm ^. transContext ^. llvmTypeCtx)
           ^. intLayout
     LeqProof <- case decideLeq (knownNat @16) w of
       Left pf -> return pf
       Right _ -> fail "LLVM arch width is < 16!"
     LeqProof <- case decideLeq (knownNat @1) w of
       Left pf -> return pf
       Right _ -> fail "PANIC: 1 > 16!"
     env <- liftIO $ readIORef $ heapsterEnvPermEnvRef henv
     some_cfgs_and_perms <- forM fn_names_and_perms $ \(nm, nm_to, perms_string) ->
       do AnyCFG cfg <-
            failOnNothing ("Could not find symbol definition: " ++ nm) $
            lookupFunctionCFG lm nm
          let args = mkCruCtx $ handleArgTypes $ cfgHandle cfg
          let ret = handleReturnType $ cfgHandle cfg
          SomeFunPerm fun_perm <-
            tracePretty (pretty ("Fun args:" :: String) <+>
                         permPretty emptyPPInfo args) $
            withKnownNat w $
            parseFunPermStringMaybeRust "permissions" w env args ret perms_string
          return (SomeCFGAndPerm (GlobalSymbol $
                                  fromString nm) nm_to cfg fun_perm)
     sc <- getSharedContext
     let saw_modname = heapsterEnvSAWModule henv
     env' <- liftIO $
       let ?ptrWidth = w in
       tcTranslateAddCFGs sc saw_modname env endianness some_cfgs_and_perms
     liftIO $ writeIORef (heapsterEnvPermEnvRef henv) env'


heapster_typecheck_fun :: BuiltinContext -> Options -> HeapsterEnv ->
                          String -> String -> TopLevel ()
heapster_typecheck_fun bic opts henv fn_name perms_string =
  heapster_typecheck_mut_funs bic opts henv [(fn_name, perms_string)]

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

heapster_print_fun_trans :: BuiltinContext -> Options -> HeapsterEnv ->
                            String -> TopLevel ()
heapster_print_fun_trans _bic _opts henv fn_name =
  do pp_opts <- getTopLevelPPOpts
     sc <- getSharedContext
     let saw_modname = heapsterEnvSAWModule henv
     fun_term <-
       fmap (fromJust . defBody) $
       liftIO $ scRequireDef sc $ mkSafeIdent saw_modname fn_name
     liftIO $ putStrLn $ scPrettyTerm pp_opts fun_term

heapster_export_coq :: BuiltinContext -> Options -> HeapsterEnv ->
                       String -> TopLevel ()
heapster_export_coq _bic _opts henv filename =
  do let coq_trans_conf = coqTranslationConfiguration [] []
     sc <- getSharedContext
     saw_mod <- liftIO $ scFindModule sc $ heapsterEnvSAWModule henv
     let coq_doc =
           vcat [preamble coq_trans_conf {
                   postPreamble = "From CryptolToCoq Require Import SAWCorePrelude."},
                 translateSAWModule coq_trans_conf saw_mod]
     liftIO $ writeFile filename (show coq_doc)

heapster_parse_test :: BuiltinContext -> Options -> Some LLVMModule ->
                       String -> String ->  TopLevel ()
heapster_parse_test _bic _opts _some_lm@(Some lm) fn_name perms_string =
  do let env = heapster_default_env -- FIXME: env should be an argument
     let _arch = llvmModuleArchRepr lm
     AnyCFG cfg <-
       failOnNothing ("Could not find symbol: " ++ fn_name) $
       lookupFunctionCFG lm fn_name
     let args = mkCruCtx $ handleArgTypes $ cfgHandle cfg
     let ret = handleReturnType $ cfgHandle cfg
     SomeFunPerm fun_perm <- parseFunPermString "permissions" env args
                                                ret perms_string
     liftIO $ putStrLn $ permPrettyString emptyPPInfo fun_perm
