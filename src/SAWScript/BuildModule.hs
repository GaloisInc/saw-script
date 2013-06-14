{-# LANGUAGE TupleSections #-}

module SAWScript.BuildModule
  ( buildModule
  ) where

import SAWScript.AST
import SAWScript.Compiler

import Control.Applicative
import Control.Arrow
import Control.Monad
import Control.Monad.State
import Data.Monoid
import Data.Foldable (foldrM)
import qualified Data.Map as M
import qualified Data.Traversable as T

-- Types -----------------------------------------------------------------------

type Incoming = (ModuleName,[TopStmtSimple RawT])
type Outgoing = ModuleSimple RawT RawT

type ModuleBuilder = (Env ExprAssoc,Env RawT)
type ExprAssoc = (Maybe (ExprSimple RawT),Maybe RawSigT)

-- BuildEnv --------------------------------------------------------------------

buildModule :: Compiler Incoming Outgoing
buildModule = compiler "BuildEnv" $ \(mn,ts) -> build >=> check >=> assemble mn $ ts
  where
  -- stage1: build tentative environment. expression vars may or may not have bound expressions,
  --   but may not have multiple bindings.
  build = foldrM mkModBuilder (M.empty,M.empty)
  -- stage2: force every expression var to have exactly one bound expression.
  check (ee,te) = (,) <$> M.traverseWithKey ensureExprPresent ee <*> pure te
  -- stage3: make a module out of the resulting envs
  assemble mn (ee,te) = return $ Module mn ee te M.empty

  -- Every expression name must be bound to something
  ensureExprPresent :: Name -> ExprAssoc -> Err (ExprSimple RawT)
  ensureExprPresent n met = case met of
    (Just e,Just t) -> return $ updateAnnotation (Just t) e
    (Just e,_     ) -> return e
    _               -> noBindingErr n

mkModBuilder :: TopStmtSimple RawT -> ModuleBuilder -> Err ModuleBuilder
mkModBuilder t env@(ee,te) = case t of
  -- TypeDecls may not fail
  TopTypeDecl n pt -> case M.lookup n ee of
                      Just (_,Just _) -> multiDeclErr n
                      _               -> return $ intoExprEnv (newTypeDecl pt) n env
  -- Multiple binds to the same name will fail
  TopBind n e      -> case M.lookup n ee of
                      Just (Just _,_) -> multiDeclErr n
                      _               -> return $ intoExprEnv (newBind e) n env
  -- Multiple declarations of the same type synonym will fail
  TypeDef n pt     -> if M.member n te
                      then multiDeclErr n
                      else return $ intoTypeEnv n (newTypeSyn pt) env
  -- Multiple declarations of an abstract type will fail
  AbsTypeDecl n    -> if M.member n te
                      then multiDeclErr n
                      else return $ intoTypeEnv n newAbsType env
  -- Imports will not change the environment
  _ -> return env

-- BuildEnv --------------------------------------------------------------------

intoExprEnv :: (Maybe ExprAssoc -> ExprAssoc) -> Name -> ModuleBuilder -> ModuleBuilder
intoExprEnv f n (ee,te) = (M.alter (Just . f) n ee,te)

intoTypeEnv :: Name -> RawT -> ModuleBuilder -> ModuleBuilder
intoTypeEnv n a (ee,te) = (ee,M.insert n a te)

-- If the name is bound already, add the RawSigT to the others,
--  otherwise start a new list.
newTypeDecl :: RawSigT -> Maybe ExprAssoc -> ExprAssoc
newTypeDecl pt = maybe (Nothing,Just pt) (second (Just pt `mplus`))

-- The fst of the resulting tuple will always be (Just e).
--  If the name wasn't bound already, bind it.
newBind :: ExprSimple RawT -> Maybe ExprAssoc -> ExprAssoc
newBind e = maybe (Just e,Nothing) (first $ const $ Just e)

newTypeSyn :: RawSigT -> RawT
newTypeSyn = Just

newAbsType :: RawT
newAbsType = Nothing

-- Error Messages --------------------------------------------------------------

multiDeclErr :: Name -> Err a 
multiDeclErr n = fail ("Multiple declarations of '" ++ n ++ "'")

noBindingErr :: Name -> Err a
noBindingErr n = fail ("The type signature for '" ++ n ++ "' lacks an accompanying binding.")

