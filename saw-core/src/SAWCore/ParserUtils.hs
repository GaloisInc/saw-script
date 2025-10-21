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
 ( -- * Template haskell utilities.
   DecWriter
 , runDecWriter
 , declareSharedModuleFns
 , defineModuleFns
 , tcInsertModule -- re-exported for code using defineModuleFromFileWithFns
 ) where

import Control.Monad (forM_)
import Control.Monad.State (StateT, execStateT, modify)
import Control.Monad.Trans.Class (MonadTrans(..))
import Data.List (intercalate)
import Data.Text (Text)
import qualified Data.Text as Text
import Language.Haskell.TH

import SAWCore.Name (ModuleName, moduleNamePieces)
import qualified SAWCore.Parser.AST as Un
import SAWCore.SharedTerm
import SAWCore.Typechecker (tcInsertModule)

-- | Monad for defining TH declarations
type DecWriter = StateT [Dec] Q

-- | Run declaration writer returning list of TH declarations
runDecWriter :: DecWriter () -> Q [Dec]
runDecWriter m = execStateT m []

-- | Emit a list of TH declarations, adding them to the current list
addDecs :: [Dec] -> DecWriter ()
addDecs decs = modify (++ decs)


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
  let mnm_s = intercalate "_" $ map Text.unpack $ moduleNamePieces mnm in
  let th_nm = (if apply_p then "scApply" else "sc") ++ mnm_s ++ "_" ++ Text.unpack nm in
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
  declareTypedNameFun [| scGlobalApply |] mnm d False tp

-- | Declare a Haskell function
--
-- > scApplyMMM_c :: SharedContext -> Term -> ... -> Term -> IO Term
--
-- for constructor @c@ with type (including parameters) @tp@ in module @MMM@
declareCtorFun :: ModuleName -> Text -> Un.UTerm -> DecWriter ()
declareCtorFun mnm c tp =
  declareTypedNameFun [| scGlobalApply |] mnm c True tp


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


-- | @defineModuleFns m str@ calls 'declareSharedModuleFns' to add
-- declarations of Haskell term-building functions for each
-- definition, constructor, and datatype declared in module @m@.
-- It also defines the function
--
-- > str :: SharedContext -> IO ()
--
-- that will load the module @m@ into the current 'SharedContext'.
defineModuleFns :: Un.Module -> String -> Q [Dec]
defineModuleFns m mod_loader =
  runDecWriter $
  do declareSharedModuleFns m
     let sc = mkName "sc"
     load_tp <- lift $ [t| SharedContext -> IO () |]
     load_body <-
       lift $ [e| tcInsertModule $(varE sc) m |]
     addDecs [ SigD (mkName mod_loader) load_tp
             , FunD (mkName mod_loader) [ Clause [VarP sc] (NormalB load_body) [] ]
             ]
