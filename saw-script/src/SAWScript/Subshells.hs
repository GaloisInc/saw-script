{-# LANGUAGE OverloadedStrings #-}
{- |
Module      : SAWScript.Subshells
Description : Find "subshell" and "proof_subshell" usage for special handling
License     : BSD3
Maintainer  : saw@galois.com
Stability   : provisional

Pass that finds usages of @subshell@ and @proof_subshell@ for
downstream special handling.
-}

module SAWScript.Subshells (processExpr, processStmts) where

import qualified Data.IORef as IORef
import Data.IORef (IORef)

import SAWSupport.Console
import SAWSupport.ScopedMap (ScopedMap)
import qualified SAWSupport.ScopedMap as ScopedMap

import SAWCentral.AST

import SAWScript.Panic


------------------------------------------------------------
-- Support logic

-- | Context type for the pass.
--
--   We keep a scoped map that remembers which names have been locally
--   defined. If we see the builtin names we're looking for in this
--   map, they don't actually refer to the builtins and shouldn't be
--   rewritten.
data Ctx = Ctx {
    ctxShadowed :: IORef (ScopedMap Name Bool)
}

-- | Create a new context.
newctx :: IO Ctx
newctx = do
    shadowed <- IORef.newIORef $ ScopedMap.empty
    pure $ Ctx { ctxShadowed = shadowed }

-- | Enter a new scope.
pushScope :: Ctx -> IO ()
pushScope ctx = do
    shadowed <- IORef.readIORef (ctxShadowed ctx)
    let shadowed' = ScopedMap.push shadowed
    IORef.writeIORef (ctxShadowed ctx) shadowed'

-- | Leave a scope.
popScope :: Ctx -> IO ()
popScope ctx = do
    shadowed <- IORef.readIORef (ctxShadowed ctx)
    let shadowed' = ScopedMap.pop shadowed
    IORef.writeIORef (ctxShadowed ctx) shadowed'

-- | Mark a variable as locally defined.
shadow :: Ctx -> Name -> IO ()
shadow ctx x = do
    shadowed <- IORef.readIORef (ctxShadowed ctx)
    let shadowed' = ScopedMap.insert x True shadowed
    IORef.writeIORef (ctxShadowed ctx) shadowed'

-- | Check if a variable is locally (re)defined.
isShadowed :: Ctx -> Name -> IO Bool
isShadowed ctx x = do
    shadowed <- IORef.readIORef (ctxShadowed ctx)
    pure $ case ScopedMap.lookup x shadowed of
        Nothing -> False
        Just t -> t


------------------------------------------------------------
-- Main recursive pass

-- | Process an expression.
--
--   If we see @subshell@ or @proof_subshell@, convert to the
--   special-case version.
--
subshell'expr :: Ctx -> Expr -> IO Expr
subshell'expr ctx e0 = case e0 of
    Bool{} -> pure e0
    String{} -> pure e0
    Int{} -> pure e0
    Code{} -> pure e0
    CType{} -> pure e0
    Array pos es -> do
        es' <- mapM (subshell'expr ctx) es
        pure $ Array pos es'
    Block pos (stmts, e1) -> do
        pushScope ctx
        stmts' <- mapM (subshell'stmt ctx) stmts
        e1' <- subshell'expr ctx e1
        popScope ctx
        pure $ Block pos (stmts', e1')
    Tuple pos es -> do
        es' <- mapM (subshell'expr ctx) es
        pure $ Tuple pos es'
    Record pos etbl -> do
        etbl' <- traverse (subshell'expr ctx) etbl
        pure $ Record pos etbl'
    Index pos e1 e2 -> do
        e1' <- subshell'expr ctx e1
        e2' <- subshell'expr ctx e2
        pure $ Index pos e1' e2'
    Lookup pos e1 field -> do
        e1' <- subshell'expr ctx e1
        pure $ Lookup pos e1' field
    TLookup pos e1 field -> do
        e1' <- subshell'expr ctx e1
        pure $ TLookup pos e1' field
    Var pos x -> do
        unshadowed <- not <$> isShadowed ctx x
        pure $ case x of
            "subshell" | unshadowed -> Subshell pos emptyAnnotations
            "proof_subshell" | unshadowed -> ProofSubshell pos emptyAnnotations
            _ -> Var pos x
    Subshell{} ->
        panic "subshell'expr" ["Preexisting Subshell expression"]
    ProofSubshell{} ->
        panic "subshell'expr" ["Preexisting ProofSubshell expression"]
    Lambda pos mname paramPos params namedParams body -> do
        pushScope ctx
        mapM_ (subshell'pat ctx) params
        namedParams' <- do
            let once (namepos, (patpos, e, pat)) = do
                  -- A default argument value is an unlikely place to
                  -- find a subshell, but you never know...
                  e' <- subshell'expr ctx e
                  subshell'pat ctx pat
                  pure $ (namepos, (patpos, e', pat))
            traverse once namedParams
        body' <- subshell'expr ctx body
        popScope ctx
        pure $ Lambda pos mname paramPos params namedParams' body'
    Application pos e1 args -> do
        e1' <- subshell'expr ctx e1
        args' <- do
            let once (mname, e2) = do
                  e2' <- subshell'expr ctx e2
                  pure (mname, e2')
            mapM once args
        pure $ Application pos e1' args'
    Let pos dg e1 -> do
        dg' <- subshell'declgroup ctx dg
        pushScope ctx
        e1' <- subshell'expr ctx e1
        popScope ctx
        pure $ Let pos dg' e1'
    TSig pos e1 ty -> do
        e1' <- subshell'expr ctx e1
        pure $ TSig pos e1' ty
    IfThenElse pos e1 e2 e3 -> do
        e1' <- subshell'expr ctx e1
        e2' <- subshell'expr ctx e2
        e3' <- subshell'expr ctx e3
        pure $ IfThenElse pos e1' e2' e3'

-- | Process a pattern.
subshell'pat :: Ctx -> Pattern -> IO ()
subshell'pat ctx pat0 = case pat0 of
    PImplicit{} -> pure ()
    PWild{} -> pure ()
    PVar _allpos _xpos x _mty -> shadow ctx x
    PTuple _pos pats -> mapM_ (subshell'pat ctx) pats

-- | Process a declaration group.
subshell'declgroup :: Ctx -> DeclGroup -> IO DeclGroup
subshell'declgroup ctx dg = case dg of
    Recursive ds -> do
        -- Mutually recursive decls: all the bound names go in scope
        -- at once, then after that we inspect all the bodies.
        mapM_ (subshell'pat ctx) $ map dPat ds
        let once d = do
              pushScope ctx
              def' <- subshell'expr ctx $ dDef d
              popScope ctx
              pure $ d { dDef = def' }
        ds' <- mapM once ds
        pure $ Recursive ds'
    NonRecursive d -> do
        subshell'pat ctx $ dPat d
        pushScope ctx
        def' <- subshell'expr ctx $ dDef d
        popScope ctx
        let d' = d { dDef = def' }
        pure $ NonRecursive d'

-- | Process a statement.
subshell'stmt :: Ctx -> Stmt -> IO Stmt
subshell'stmt ctx s0 = case s0 of
    StmtBind spos pat e -> do
        subshell'pat ctx pat
        e' <- subshell'expr ctx e
        pure $ StmtBind spos pat e'
    StmtLet pos rb dg -> do
        dg' <- subshell'declgroup ctx dg
        pure $ StmtLet pos rb dg'
    StmtCode{} -> pure s0
    StmtImport{} -> pure s0
    StmtInclude{} -> pure s0
    StmtTypedef{} -> pure s0
    StmtPushdir{} -> pure s0
    StmtPopdir{} -> pure s0


------------------------------------------------------------
-- External interface

processExpr :: Expr -> IO Expr
processExpr e = do
    ctx <- newctx
    e' <- subshell'expr ctx e
    checkFail
    pure e'

-- | Run the pass, and return either errors or an updated tree.
processStmts :: [Stmt] -> IO [Stmt]
processStmts stmts = do
    ctx <- newctx
    stmts' <- mapM (subshell'stmt ctx) stmts
    checkFail
    pure stmts'
