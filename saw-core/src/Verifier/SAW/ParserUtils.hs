{-# LANGUAGE CPP #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}

{- |
Module      : Verifier.SAW.ParserUtils
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : jhendrix@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module Verifier.SAW.ParserUtils
 ( module Verifier.SAW.TypedAST
   -- * Parser utilities.
 , readModuleFromFile
   -- * Template haskell utilities.
 , DecWriter
 , runDecWriter
 , defineModuleFromFile
 , declareSharedModuleFns
 , defineModuleFromFileWithFns
 , tcInsertModule -- re-exported for code using defineModuleFromFileWithFns
 ) where

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative
#endif
import Control.Monad.State
import qualified Data.ByteString.Lazy as BL
#if !MIN_VERSION_template_haskell(2,8,0)
import qualified Data.ByteString.Lazy.UTF8 as UTF8
#endif
import Language.Haskell.TH
#if MIN_VERSION_template_haskell(2,7,0)
import Language.Haskell.TH.Syntax (qAddDependentFile)
#endif
import System.Directory
import qualified Language.Haskell.TH.Syntax as TH (lift)

import qualified Verifier.SAW.UntypedAST as Un
import qualified Verifier.SAW.Grammar as Un
import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedAST
import Verifier.SAW.Typechecker (tcInsertModule)

-- | Parse an untyped module declaration from a byte-string
readModule :: FilePath -> FilePath -> BL.ByteString -> Un.Module
readModule base path b =
  case Un.parseSAW base path b of
    Right m -> m
    Left err -> error $ "Module parsing failed:\n" ++ show err

-- | Parse an untyped module from file
readModuleFromFile :: FilePath -> IO Un.Module
readModuleFromFile path = do
  base <- getCurrentDirectory
  b <- BL.readFile path
  return $ readModule base path b


-- | Monad for defining TH declarations
type DecWriter = StateT [Dec] Q

-- | Run declaration writer returning list of TH declarations
runDecWriter :: DecWriter () -> Q [Dec]
runDecWriter m = execStateT m []

-- | Emit a list of TH declarations, adding them to the current list
addDecs :: [Dec] -> DecWriter ()
addDecs decs = modify (++ decs)

-- | Record @path@ as a dependency for this compilation
addDep :: FilePath -> DecWriter ()
#if MIN_VERSION_template_haskell(2,7,0)
addDep path = lift $ qAddDependentFile path
#else
addDep path = return ()
#endif

-- | @defineModuleFromFile str file@ reads an untyped module from @file@, adds a
-- TH declaration of the name @str@ that is bound to that module at runtime, and
-- also returns the module at TH time
defineModuleFromFile :: String -> FilePath -> DecWriter Un.Module
defineModuleFromFile decNameStr path = do
  addDep path
  m <- lift $ runIO $ readModuleFromFile path
  let decName = mkName decNameStr
  moduleTp <- lift $ [t| Un.Module |]
  body <- lift $ TH.lift m
  addDecs [ SigD decName moduleTp
          , FunD decName [ Clause [] (NormalB body) [] ]]
  return m


-- | Return the type
--
-- > 'SharedContext' -> 'Term' -> .. -> 'Term' -> 'IO' 'Term'
--
-- that takes in @n@ 'Term's
termFunctionType :: Int -> Q Type
termFunctionType n = [t| SharedContext -> $(go n) |]
  where
    go 0 = [t| IO Term |]
    go i = [t| Term -> $(go (i-1)) |]

-- | @declareTermApplyFun nm t n@ declares a Haskell function
--
-- > nm :: SharedContext -> Term -> ... -> Term -> IO Term
--
-- that takes in @n@ 'Term's and applies (the 'Term' generated at runtime by the
-- expression) @t@ to them
declareTermApplyFun :: String -> Int -> (Name -> Q Exp -> Q Exp) -> DecWriter ()
declareTermApplyFun nm n tf =
  do let decName = mkName nm
     sc <- lift $ newName "sc"
     tp <- lift $ termFunctionType n
     vars <- lift $ mapM newName (map (("t"++) . show) [1 .. n])
     body <- lift $ tf sc (listE $ map varE vars)
     addDecs [ SigD decName tp
             , FunD decName [ Clause (VarP sc : map VarP vars) (NormalB body) [] ]
             ]

-- | @declareTypedNameFun sc_fun mnm nm apply_p tp@ declares a Haskell function
--
-- > scXXXmnm_nm :: SharedContext -> Term -> ... -> Term -> IO Term
--
-- where @XXX@ is @"Apply"@ if @apply_p@ is 'True', and empty otherwise. This
-- function will fully apply the constructor, datatype, or declared name
-- specified by @nm@ in module @mnm@, using the shared term constructor function
-- @sc_fun@, which should have type
--
-- > SharedContext -> Ident -> [Term] -> IO Term
--
-- The number of 'Term's to take as arguments is given by the arity of @tp@,
-- i.e., the number of nested pi-abstractions it contains at top level.
declareTypedNameFun :: Q Exp -> ModuleName -> String -> Bool -> Un.Term ->
                       DecWriter ()
declareTypedNameFun sc_fun mnm nm apply_p tp =
  let th_nm = (if apply_p then "scApply" else "sc") ++ show mnm ++ "_" ++ nm in
  declareTermApplyFun th_nm (length $ fst $ Un.asPiList tp) $ \sc ts ->
  [| $(sc_fun) $(varE sc)
   (mkIdent mnm $(stringE nm))
   $(ts) |]

-- | Declare a Haskell function
--
-- > scApplyMMM_d :: SharedContext -> Term -> ... -> Term -> IO Term
--
-- for declared name (primitive, axiom, or definition) @d@ with type @tp@ in
-- module @MMM@
declareDefFun :: ModuleName -> String -> Un.Term -> DecWriter ()
declareDefFun mnm d tp =
  declareTypedNameFun [| scGlobalApply |] mnm d True tp

-- | Declare a Haskell function
--
-- > scMMM_d :: SharedContext -> Term -> ... -> Term -> IO Term
--
-- for datatype @d@ with parameters @p_ctx@ and type @tp@ in module @MMM@
declareDataTypeFun :: ModuleName -> String -> Un.Term -> DecWriter ()
declareDataTypeFun mnm d tp =
  declareTypedNameFun [| scDataTypeApp |] mnm d False tp

-- | Declare a Haskell function
--
-- > scApplyMMM_c :: SharedContext -> Term -> ... -> Term -> IO Term
--
-- for constructor @c@ with type (including parameters) @tp@ in module @MMM@
declareCtorFun :: ModuleName -> String -> Un.Term -> DecWriter ()
declareCtorFun mnm c tp =
  declareTypedNameFun [| scCtorApp |] mnm c True tp


-- | Declare Haskell functions, via 'declareTermApplyFun', that build shared
-- terms for each of the definitions, datatypes, and constructors in a
-- module. Each datatype @d@ gets a function
--
-- > scMMM_d :: SharedContext -> Term -> ... -> Term -> IO Term
--
-- where @MMM@ is the name of the module. Similarly, each constructor or
-- definition @d@ gets
--
-- > scApplyMMM_d :: SharedContext -> Term -> ... -> Term -> IO Term
declareSharedModuleFns :: Un.Module -> DecWriter ()
declareSharedModuleFns m =
  do forM_ (Un.moduleTypedDecls m) $ \(d,tp) ->
       declareDefFun (Un.moduleName m) d tp
     forM_ (Un.moduleTypedDataDecls m) $ \(d,tp) ->
       declareDataTypeFun (Un.moduleName m) d tp
     forM_ (Un.moduleTypedCtorDecls m) $ \(c,tp) ->
       declareCtorFun (Un.moduleName m) c tp


-- | @defineModuleFromFileWithFns str str2 file@ reads an untyped module from
-- @file@, adds a TH declaration of the name @str@ that is bound to that module
-- at runtime, and then calls 'declareSharedModuleFns' to add declarations of
-- Haskell term-building functions for each definition, constructor, and
-- datatype declared in the module that is loaded. It also defines the function
--
-- > str2 :: SharedContext -> IO ()
--
-- that will load the module @str@ into the current 'SharedContext'.
defineModuleFromFileWithFns :: String -> String -> FilePath -> Q [Dec]
defineModuleFromFileWithFns mod_name mod_loader path =
  runDecWriter $
  do m <- defineModuleFromFile mod_name path
     declareSharedModuleFns m
     let sc = mkName "sc"
     load_tp <- lift $ [t| SharedContext -> IO () |]
     load_body <-
       lift $ [e| tcInsertModule $(varE sc) $(varE $ mkName mod_name) |]
     addDecs [ SigD (mkName mod_loader) load_tp
             , FunD (mkName mod_loader) [ Clause [VarP sc] (NormalB load_body) [] ]
             ]
