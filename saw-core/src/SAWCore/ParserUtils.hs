{-# LANGUAGE CPP #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}

{- |
Module      : SAWCore.ParserUtils
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : jhendrix@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module SAWCore.ParserUtils
 ( -- * Parser utilities.
   readModuleFromFile
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
import Control.Monad (forM_)
import Control.Monad.State (StateT, execStateT, modify)
import Control.Monad.Trans.Class (MonadTrans(..))
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.Lazy as TL
import qualified Data.Text.Lazy.IO as TLIO
import Language.Haskell.TH
#if MIN_VERSION_template_haskell(2,7,0)
import Language.Haskell.TH.Syntax (qAddDependentFile)
#endif
import System.Directory
import qualified Language.Haskell.TH.Syntax as TH (lift)

import SAWCore.Name (ModuleName)
import qualified SAWCore.UntypedAST as Un
import qualified SAWCore.Grammar as Un
import SAWCore.SharedTerm
import SAWCore.Typechecker (tcInsertModule)

-- | Parse an untyped module declaration from a (lazy) Text
readModule :: FilePath -> FilePath -> TL.Text -> Un.Module
readModule base path b =
  case Un.parseSAW base path b of
    Right m -> m
    Left err -> error $ "Module parsing failed:\n" ++ show err

-- | Parse an untyped module from file
readModuleFromFile :: FilePath -> IO Un.Module
readModuleFromFile path = do
  base <- getCurrentDirectory
  txt <- TLIO.readFile path
  return $ readModule base path txt


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
declareTypedNameFun :: Q Exp -> ModuleName -> Text -> Bool -> Un.UTerm ->
                       DecWriter ()
declareTypedNameFun sc_fun mnm nm apply_p tp =
  let th_nm = (if apply_p then "scApply" else "sc") ++ show mnm ++ "_" ++ Text.unpack nm in
  declareTermApplyFun th_nm (length $ fst $ Un.asPiList tp) $ \sc ts ->
  [| $(sc_fun) $(varE sc)
   (mkIdent mnm (Text.pack $(stringE (Text.unpack nm))))
   $(ts) |]

-- | Declare a Haskell function
--
-- > scApplyMMM_d :: SharedContext -> Term -> ... -> Term -> IO Term
--
-- for declared name (primitive, axiom, or definition) @d@ with type @tp@ in
-- module @MMM@
declareDefFun :: ModuleName -> Text -> Un.UTerm -> DecWriter ()
declareDefFun mnm d tp =
  declareTypedNameFun [| scGlobalApply |] mnm d True tp

-- | Declare a Haskell function
--
-- > scMMM_d :: SharedContext -> Term -> ... -> Term -> IO Term
--
-- for datatype @d@ with parameters @p_ctx@ and type @tp@ in module @MMM@
declareDataTypeFun :: ModuleName -> Text -> Un.UTerm -> DecWriter ()
declareDataTypeFun mnm d tp =
  declareTypedNameFun [| scDataTypeApp |] mnm d False tp

-- | Declare a Haskell function
--
-- > scApplyMMM_c :: SharedContext -> Term -> ... -> Term -> IO Term
--
-- for constructor @c@ with type (including parameters) @tp@ in module @MMM@
declareCtorFun :: ModuleName -> Text -> Un.UTerm -> DecWriter ()
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
