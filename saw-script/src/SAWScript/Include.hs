{-# LANGUAGE OverloadedStrings #-}
{- |
Module      : SAWScript.Include
Description : Processing SAWScript include directives
License     : BSD3
Maintainer  : saw@galois.com
Stability   : provisional
-}

module SAWScript.Include (Processor, processExpr, processStmts) where

import qualified Data.Text as Text
import Data.Text (Text)
import qualified Data.IORef as IORef
import Data.IORef (IORef)

import SAWCentral.AST

-- Type shorthand for the file-reader function we want.
--
-- (The file-reader function is passed down to avoid a dependency
-- cycle.)
--
type Reader = FilePath -> IO (Either [Text] [Stmt])

-- Type shorthand for the type of process*.
type Processor a = Reader -> a -> IO (Either [Text] a)

-- | Context for the pass: the reader for include files
--   plus the error messages accumulated so far.
--
--   The error list is a list of lists of Text, the idea being that we
--   cons each batch of errors we get back from the reader on the
--   front of the outer list, and read it off at the end with @concat
--   $ reverse errs@.
--
--   Note that we do not _generate_ errors, only pass on errors
--   returned by the reader. For the moment, that does not include
--   warnings, so there's no need to handle warnings in here either.
--
data Ctx = Ctx {
    ctxReader :: Reader,
    ctxErrs :: IORef [[Text]]
}

ctxAddErrs :: Ctx -> [Text] -> IO ()
ctxAddErrs ctx errs = do
    let errsRef = ctxErrs ctx
    errlists <- IORef.readIORef errsRef
    IORef.writeIORef errsRef (errs : errlists)


------------------------------------------------------------
-- Main recursive pass

-- | Resolve includes, for expressions.
incs'expr :: Ctx -> Expr -> IO Expr
incs'expr ctx e0 =
  case e0 of
    Bool{} -> pure e0
    String{} -> pure e0
    Int{} -> pure e0
    Code{} -> pure e0
    CType{} -> pure e0
    Array pos es -> do
        es' <- mapM (incs'expr ctx) es
        pure $ Array pos es'
    Block pos (stmts, lastexpr) -> do
        stmts' <- incs'stmts ctx stmts
        lastexpr' <- incs'expr ctx lastexpr
        pure $ Block pos (stmts', lastexpr')
    Tuple pos es -> do
        es' <- mapM (incs'expr ctx) es
        pure $ Tuple pos es'
    Record pos members -> do
        members' <- traverse (incs'expr ctx) members
        pure $ Record pos members'
    Index pos e1 e2 -> do
        e1' <- incs'expr ctx e1
        e2' <- incs'expr ctx e2
        pure $ Index pos e1' e2'
    Lookup pos e1 field -> do
        e1' <- incs'expr ctx e1
        pure $ Lookup pos e1' field
    TLookup pos e1 ix -> do
        e1' <- incs'expr ctx e1
        pure $ TLookup pos e1' ix
    Var{} -> pure e0
    Lambda pos mname pat e1 -> do
        e1' <- incs'expr ctx e1
        pure $ Lambda pos mname pat e1'
    Application pos e1 e2 -> do
        e1' <- incs'expr ctx e1
        e2' <- incs'expr ctx e2
        pure $ Application pos e1' e2'
    Let pos ds e1 -> do
        ds' <- incs'declgroup ctx ds
        e1' <- incs'expr ctx e1
        pure $ Let pos ds' e1'
    TSig pos e1 ty -> do
        e1' <- incs'expr ctx e1
        pure $ TSig pos e1' ty
    IfThenElse pos e1 e2 e3 -> do
        e1' <- incs'expr ctx e1
        e2' <- incs'expr ctx e2
        e3' <- incs'expr ctx e3
        pure $ IfThenElse pos e1' e2' e3'

-- | Resolve includes, for statements.
--
--   Returns a list of statements so included files can be inserted.
incs'stmt :: Ctx -> Stmt -> IO [Stmt]
incs'stmt ctx s0 = case s0 of
    StmtBind pos pat e1 -> do
        e1' <- incs'expr ctx e1
        let s0' = StmtBind pos pat e1'
        pure [s0']
    StmtLet pos rebindable ds -> do
        ds' <- incs'declgroup ctx ds
        let s0' = StmtLet pos rebindable ds'
        pure [s0']
    StmtCode{} -> pure [s0]
    StmtImport{} -> pure [s0]
    StmtInclude _pos name -> do
        result <- (ctxReader ctx) (Text.unpack name)
        case result of
            Left errs -> do
                ctxAddErrs ctx errs
                pure []
            Right stmts' ->
                pure stmts'
    StmtTypedef{} -> pure [s0]
    StmtPushdir{} -> pure [s0]
    StmtPopdir{} -> pure [s0]

-- | Resolve includes, for a list of statements.
--
--   Includes the implicit call to `concat`.
incs'stmts :: Ctx -> [Stmt] -> IO [Stmt]
incs'stmts ctx stmts = do
    stmtses <- mapM (incs'stmt ctx) stmts
    pure $ concat stmtses

-- | Resolve includes, for a single declaration.
incs'decl :: Ctx -> Decl -> IO Decl
incs'decl ctx d = do
    def' <- incs'expr ctx (dDef d)
    pure $ d { dDef = def' }

-- | Resolve includes, for a declaration group.
incs'declgroup :: Ctx -> DeclGroup -> IO DeclGroup
incs'declgroup ctx dg = case dg of
    Recursive ds -> do
        ds' <- mapM (incs'decl ctx) ds
        pure $ Recursive ds'
    NonRecursive d -> do
        d' <- incs'decl ctx d
        pure $ NonRecursive d'


------------------------------------------------------------
-- External interface

process :: Reader -> (Ctx -> a -> IO a) -> a -> IO (Either [Text] a)
process reader entrypoint tree = do
    errsRef <- IORef.newIORef []
    let ctx = Ctx { ctxReader = reader, ctxErrs = errsRef }
    tree' <- entrypoint ctx tree
    errlists <- IORef.readIORef errsRef
    case errlists of
        [] -> return $ Right tree'
        _ -> return $ Left (concat $ reverse errlists)

processExpr :: Reader -> Expr -> IO (Either [Text] Expr)
processExpr reader e = process reader incs'expr e

processStmts :: Reader -> [Stmt] -> IO (Either [Text] [Stmt])
processStmts reader stmts = process reader incs'stmts stmts
