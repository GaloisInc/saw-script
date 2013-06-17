{-# LANGUAGE FlexibleInstances #-}

module SAWScript.RenameRefs
  ( renameRefs
  , IncomingModule
  , OutgoingModule
  ) where

import SAWScript.AST
import SAWScript.Compiler
import SAWScript.Prelude

import Control.Applicative
import Control.Monad.State
import Control.Monad.Reader
import Data.List (elemIndices, intercalate, nub)
import Data.Maybe (mapMaybe, maybeToList)
import qualified Data.Map as M
import qualified Data.Traversable as T

-- Traverse over all variable reference @UnresolvedName@s, resolving them to exactly one @ResolvedName@.
renameRefs :: Compiler IncomingModule OutgoingModule
renameRefs = compiler "RenameRefs" $ \m@(Module nm ee te ds) -> evalRR m $
  Module nm <$> T.traverse resolveInExpr ee <*> pure te <*> pure ds

-- Types {{{

type IncomingModule = Module    UnresolvedName ResolvedT ResolvedT
type IncomingExpr   = Expr      UnresolvedName ResolvedT
type IncomingBStmt  = BlockStmt UnresolvedName ResolvedT

type OutgoingModule = Module    ResolvedName   ResolvedT ResolvedT
type OutgoingExpr   = Expr      ResolvedName   ResolvedT
type OutgoingBStmt  = BlockStmt ResolvedName   ResolvedT

type RR = StateT Int (ReaderT RREnv Err)

-- One map for the local module, which has not yet been typechecked,
--  and a list of maps for the dependency modules, which have.
-- In the moduleEnv, we have a local name for the module, the full
--  name for the module, and the expr env for the module.
-- Since these are fully typechecked modules, we can assume that
--  their Expr type is FullT.
type ExprMaps = (ModuleName, Env IncomingExpr, ModuleEnv (Env (Expr ResolvedName Type)))

-- }}}

-- RREnv {{{

data RREnv = RREnv
  { thisModule   :: IncomingModule
  , localNameEnv :: Env Name
  }

onLocalNameEnv :: (Env Name -> Env Name) -> RREnv -> RREnv
onLocalNameEnv f e = e { localNameEnv = f $ localNameEnv e }

-- }}}

-- Monadic Operations {{{

evalRR :: IncomingModule -> RR a -> Err a
evalRR mod m = runReaderT (evalStateT m 0) env
  where
  env = RREnv mod emptyEnv

incrGen :: RR Int
incrGen = do
  i <- get
  modify (+1)
  return i

getModule :: RR IncomingModule
getModule = asks thisModule

getLocalNameEnv :: RR (Env Name)
getLocalNameEnv = asks localNameEnv

addName  :: Name -> (Name -> RR a) -> RR a
addName n f = do
  i <- incrGen
  let uniqueN = n ++ "." ++ show i
  -- shadow any existing reference in the env with the new one
  local (onLocalNameEnv $ M.alter (const $ Just uniqueN) n)
    -- pass in the new unique name
    (f uniqueN)

addNamesFromBinds :: [Bind e] -> ([Bind e] -> RR a) -> RR a
addNamesFromBinds ns f = foldr step f ns []
  where
  step (n,e) f' ns' = addName n $ \n' -> f' ((n',e) : ns')

-- }}}

-- traversal operations for Exprs, BlockStmts, and Binds
resolveInExpr :: IncomingExpr -> RR OutgoingExpr
resolveInExpr exp = case exp of
  -- Focus of the whole compiler pass
  Var nm t          -> Var <$> resolveName nm <*> pure t
  -- Recursive structures
  Array  es t       -> Array  <$> mapM resolveInExpr es   <*> pure t
  Block  bs t       -> Block  <$> resolveInBStmts bs      <*> pure t
  Tuple  es t       -> Tuple  <$> mapM resolveInExpr es   <*> pure t
  Record bs t       -> Record <$> mapM resolveInBind bs   <*> pure t
  Index  e1 e2 t    -> Index  <$> resolveInExpr e1        <*> resolveInExpr e2 <*> pure t
  Lookup e n t      -> Lookup <$> resolveInExpr e         <*> pure n           <*> pure t
  Application f v t -> Application   <$> resolveInExpr f  <*> resolveInExpr v  <*> pure t
  -- Binders, which add to the local name environment.
  Function a at e t -> addName a $ \a' ->
                         Function a' at <$> resolveInExpr e  <*> pure t
  LetBlock bs e     -> let ds = duplicates bs in if null ds
                         then addNamesFromBinds bs $ \bs' ->
                           LetBlock <$> mapM resolveInBind bs' <*> resolveInExpr e
                         else duplicateBindingsFail ds
  -- No-ops
  Unit t            -> pure $ Unit t
  Bit b t           -> pure $ Bit b t
  Quote s t         -> pure $ Quote s t
  Z i t             -> pure $ Z i t

duplicateBindingsFail :: [Name] -> RR a
duplicateBindingsFail ns = fail $
  "Conflicting definitions for " ++ str
  where
  str = intercalate ", " $ map show ns

duplicates :: [Bind a] -> [Name]
duplicates bs = nub $ mapMaybe f ns
  where
  ns = map fst bs
  occurenceCount = length . (`elemIndices` ns)
  f n = if occurenceCount n > 1 then Just n else Nothing

resolveInBind :: Bind IncomingExpr -> RR (Bind OutgoingExpr)
resolveInBind (n,e) = (,) <$> pure n <*> resolveInExpr e

resolveInBStmts :: [IncomingBStmt] -> RR [OutgoingBStmt]
resolveInBStmts bsts = case bsts of
  []                        -> return []

  Bind Nothing c e  : bsts' ->   (:) <$> (Bind Nothing c   <$> resolveInExpr e)       <*> resolveInBStmts bsts'
  Bind (Just n) c e : bsts' -> addName n $ \n' ->
                                 (:) <$> (Bind (Just n') c <$> resolveInExpr e)       <*> resolveInBStmts bsts'

  BlockTypeDecl n t : bsts' ->   (:) <$> (pure $ BlockTypeDecl n t)            <*> resolveInBStmts bsts'
  BlockLet bs       : bsts' -> addNamesFromBinds bs $ \bs' ->
                                 (:) <$> (BlockLet <$> mapM resolveInBind bs') <*> resolveInBStmts bsts'

-- Given a module as context, find *the* ResolvedName that an unqualified UnresolvedName refers to,
--  failing if the UnresolvedName is unbound or ambiguous.
resolveName :: UnresolvedName -> RR ResolvedName
resolveName un = do
  lEnv <- getLocalNameEnv
  mod <- getModule
  let ems = allExprMaps mod
  enforceResolution un $
    resolveUnresolvedName lEnv ems un



-- Take a module to its collection of Expr Environments.
allExprMaps :: IncomingModule -> ExprMaps
allExprMaps (Module modNm exprEnv _ deps) = (modNm,exprEnv,foldr f M.empty (M.elems deps))
  where
  f (Module modNm exprEnv _ _) = M.insert modNm exprEnv

-- TODO: this will need to change once we can refer to prelude functions
-- with qualified names.
resolveUnresolvedName :: Env Name -> ExprMaps -> UnresolvedName -> [ResolvedName]
resolveUnresolvedName
  localAnonEnv
  (localModNm,localTopEnv,rms)
  un@(UnresolvedName ns n) =
  -- gather all the possible bindings. Later, we'll check that there is exactly one.
  case inLocalAnon of
    Just n -> [n]
    Nothing -> maybeToList inLocalTop ++ inPrelude ++ mapMaybe inDepMod (M.assocs rms)
  where
  -- TODO: fix when we have proper modules
  inPrelude = [ s | s@(TopLevelName _ x) <- map fst preludeEnv, n == x ]
  -- ignores name shadowing, defering to the local binding over the top level binding.
  inLocal = maybeToList $ inLocalAnon `mplus` inLocalTop
  -- If it's in the localAnonEnv, use the unique name.
  inLocalAnon
    -- only check the local anon env if the name is unqualified
    | isUnqualified un         = LocalName                        <$> M.lookup n localAnonEnv
    | otherwise                = Nothing
  -- check the local module top level names if either...
  inLocalTop
    -- unqualified
    | isUnqualified un         = TopLevelName localModNm n        <$  M.lookup n localTopEnv
    -- qualified as local module
    | un `inModule` localModNm = TopLevelName localModNm n        <$  M.lookup n localTopEnv
    | otherwise                = Nothing
  inDepMod (mn, exprEnv)
    -- unqualified
    | isUnqualified un = TopLevelName mn n <$ M.lookup n exprEnv
    -- qualified as this module
    | un `inModule` mn = TopLevelName mn n <$ M.lookup n exprEnv
    | otherwise        = Nothing

isUnqualified :: UnresolvedName -> Bool
isUnqualified (UnresolvedName ns _) = null ns

inModule :: UnresolvedName -> ModuleName -> Bool
inModule (UnresolvedName ns _) (ModuleName mns mn) = ns == (mns ++ [mn])


-- Enforce that there is exactly one valid ResolvedName for a variable.
enforceResolution :: UnresolvedName -> [ResolvedName] -> RR ResolvedName
enforceResolution un qs = case qs of
  [qn] -> return qn
  []   -> fail $ "Unbound reference for " ++ renderUnresolvedName un
  _    -> fail $ "Ambiguous reference for " ++ renderUnresolvedName un

