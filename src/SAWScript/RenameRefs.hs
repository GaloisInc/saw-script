{-# LANGUAGE FlexibleInstances #-}

module SAWScript.RenameRefs
  ( renameRefs
  , IncomingModule
  , OutgoingModule
  ) where

import SAWScript.AST
import SAWScript.Compiler

import Control.Applicative
import Control.Monad.State
import Control.Monad.Reader
import Data.List (elemIndices, intercalate, nub)
import Data.Maybe (mapMaybe, maybeToList)
import qualified Data.Map as M
import Data.Traversable (traverse)
import Prelude hiding (mod, exp)

-- Traverse over all variable reference @UnresolvedName@s, resolving them to exactly one @ResolvedName@.
renameRefs :: Compiler IncomingModule OutgoingModule
renameRefs = compiler "RenameRefs" $ \m@(Module nm ee pe ds cs) -> evalRR m $
  Module nm <$> traverse resolveInDecl ee <*> pure pe <*> pure ds <*> pure cs

-- Types {{{

type IncomingModule = Module
type IncomingExpr   = Expr
type IncomingBStmt  = BlockStmt

type OutgoingModule = Module
type OutgoingExpr   = Expr
type OutgoingBStmt  = BlockStmt

type RR = StateT Int (ReaderT RREnv Err)

-- One map for the local module, which has not yet been typechecked,
--  and a list of maps for the dependency modules, which have.
-- In the moduleEnv, we have a local name for the module, the full
--  name for the module, and the expr env for the module.
-- Since these are fully typechecked modules, we can assume that
--  their Expr type is FullT.
type ExprMaps =
    ( ModuleName
    , Env IncomingExpr
    , Env Schema
    , ModuleEnv (Env Expr, Env Schema)
    )

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

addName  :: LName -> (LName -> RR a) -> RR a
addName n f = do
  i <- incrGen
  let uniqueN = fmap (++ "." ++ show i) n
  -- shadow any existing reference in the env with the new one
  local (onLocalNameEnv $ M.insert (getVal n) (getVal uniqueN))
    -- pass in the new unique name
    (f uniqueN)

addNameFromDecl :: Decl -> (Decl -> RR a) -> RR a
addNameFromDecl (Decl n mt e) f = addName n $ \n' -> f (Decl n' mt e)

addNamesFromDecls :: [Decl] -> ([Decl] -> RR a) -> RR a
addNamesFromDecls ds f = foldr step f ds []
  where step d f' ds' = addNameFromDecl d $ \d' -> f' (d' : ds')

-- }}}

{-
resolveInExprs :: IncomingExprs -> RR OutgoingExprs
resolveInExprs pexp = case pexp of
  PrimExpr t -> return $ PrimExpr t
  Defined e -> Defined <$> resolveInExpr e
-}

-- traversal operations for Exprs, BlockStmts, and Binds
resolveInExpr :: IncomingExpr -> RR OutgoingExpr
resolveInExpr exp = case exp of
  -- Focus of the whole pass
  Var nm ts         -> Var <$> resolveName nm <*> pure ts
  -- Binders, which add to the local name environment.
  Function a at e   -> addName a $ \a' ->
                         Function a' at <$> resolveInExpr e
  Let ds e          -> let dups = duplicates ds in if null dups
                         then addNamesFromDecls ds $ \ds' ->
                           Let <$> mapM resolveInDecl ds' <*> resolveInExpr e
                         else duplicateBindingsFail dups
  -- Recursive structures
  Array  es         -> Array  <$> mapM resolveInExpr es
  Block  bs         -> Block  <$> resolveInBStmts bs
  Tuple  es         -> Tuple  <$> mapM resolveInExpr es
  Record bs         -> Record <$> traverse resolveInExpr bs
  Index  e1 e2      -> Index  <$> resolveInExpr e1        <*> resolveInExpr e2
  Lookup e n        -> Lookup <$> resolveInExpr e         <*> pure n
  TLookup e i       -> TLookup <$> resolveInExpr e        <*> pure i
  Application f v   -> Application   <$> resolveInExpr f  <*> resolveInExpr v
  -- No-ops
  Bit b             -> pure $ Bit b
  String s          -> pure $ String s
  Z i               -> pure $ Z i
  Undefined         -> pure $ Undefined
  Code s            -> pure $ Code s
  TSig e t          -> TSig <$> resolveInExpr e <*> pure t

duplicateBindingsFail :: [Name] -> RR a
duplicateBindingsFail ns = fail $
  "Conflicting definitions for " ++ str
  where
  str = intercalate ", " $ map show ns

duplicates :: [Decl] -> [Name]
duplicates ds = nub $ mapMaybe f ns
  where
  ns = map (getVal . dName) ds
  occurenceCount = length . (`elemIndices` ns)
  f n = if occurenceCount n > 1 then Just n else Nothing

resolveInDecl :: Decl -> RR Decl
resolveInDecl (Decl n mt e) = Decl n mt <$> resolveInExpr e

resolveInBStmts :: [IncomingBStmt] -> RR [OutgoingBStmt]
resolveInBStmts bsts = case bsts of
  []                        -> return []

  Bind Nothing t c e  : bsts' -> (:) <$> (Bind Nothing t c   <$> resolveInExpr e)       <*> resolveInBStmts bsts'
  Bind (Just n) t c e : bsts' -> addName n $ \n' ->
                                 (:) <$> (Bind (Just n') t c <$> resolveInExpr e)       <*> resolveInBStmts bsts'

  BlockLet ds       : bsts' -> addNamesFromDecls ds $ \ds' ->
                                 (:) <$> (BlockLet <$> mapM resolveInDecl ds') <*> resolveInBStmts bsts'
  BlockCode s       : bsts' ->   (:) (BlockCode s) <$> resolveInBStmts bsts'

-- Given a module as context, find *the* ResolvedName that an unqualified UnresolvedName refers to,
--  failing if the UnresolvedName is unbound or ambiguous.
resolveName :: Located Name -> RR (Located Name)
resolveName un = do
  lEnv <- getLocalNameEnv
  mod <- getModule
  let ems = allExprMaps mod
  enforceResolution un $
    resolveUnresolvedName lEnv ems (getVal un)



-- Take a module to its collection of Expr Environments.
allExprMaps :: IncomingModule -> ExprMaps
allExprMaps (Module modNm exprEnv primEnv deps _)
  = (modNm, unloc' exprEnv, unloc primEnv, foldr f M.empty (M.elems deps))
  where
    f (Module modNm' exprEnv' primEnv' _ _) = M.insert modNm' (unloc' exprEnv', unloc primEnv')
    unloc = M.mapKeys getVal
    unloc' = M.fromList . map (\(Decl n _ e) -> (getVal n, e))

resolveUnresolvedName :: Env Name -> ExprMaps -> Name -> [Name]
resolveUnresolvedName
  localAnonEnv
  (_localModNm,localTopEnv,localPrimEnv,rms)
  n =
  -- gather all the possible bindings. Later, we'll check that there is exactly one.
  case inLocalAnon of
    Just nm -> [nm]
    Nothing -> maybeToList inLocalTop ++ maybeToList inLocalPrim ++ mapMaybe inDepMod (M.assocs rms)
  where
  -- If it's in the localAnonEnv, use the unique name.
  inLocalAnon                  = M.lookup n localAnonEnv
  inLocalTop                   = n <$ M.lookup n localTopEnv
  inLocalPrim                  = n <$ M.lookup n localPrimEnv
  inDepMod (_mn, (exprEnv,primEnv))
    = (n <$ M.lookup n exprEnv) `mplus` (n <$ M.lookup n primEnv)

-- Enforce that there is exactly one valid ResolvedName for a variable.
enforceResolution :: Located Name -> [Name] -> RR (Located Name)
enforceResolution un qs = case qs of
  [qn] -> return (qn <$ un)
  []   -> fail $ "Unbound reference for " ++ getVal un ++ " at " ++ show (getPos un)
  qns  -> fail $ "Ambiguous reference for " ++ getVal un ++ " at " ++ show (getPos un)
          ++ "\n" ++ unlines qns
