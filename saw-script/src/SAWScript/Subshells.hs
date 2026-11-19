{-# LANGUAGE OverloadedStrings #-}
{- |
Module      : SAWScript.Subshells
Description : Find "subshell" and "proof_subshell" usage for special handling
License     : BSD3
Maintainer  : saw@galois.com
Stability   : provisional

Pass that finds usages of @subshell@ and @proof_subshell@ for
downstream special handling.

In particular, in order to be able to typecheck what's typed
interactively in a subshell we need to have captured the typing
environment at the point where the subshell is invoked.

For the time being, the way we do this is by replacing @subshell@ (and
@proof_subshell@) with special-case expressions, and at typechecking
time store a copy of the typing environment in those expressions. The
drawback of this approach is that the expressions appear at the point
where the builtin is mentioned, not where it is actually invoked.

Because the type of @subshell@ (and comparably @proof_subshell@) in
SAWScript is @() -> TopLevel ()@, two things have to happen after the
builtin is mentioned for it to be actually invoked: someone must apply
a unit argument, and then the resulting value must be monad-bound.

For soundness, the typing environment on entry to the subshell must
match the value environment. The value environment is captured at the
invocation point, not the mention point. (In principle that could be
changed, but it would be messy and the resulting semantics would be
kind of odd.)

Therefore, this version rejects uses of @subshell@ and
@proof_subshell@ other than @() <- subshell ()@ or its exact
equivalents. That ensures that, as far as both the typing environment
and value environments are concerned, the capture point is close
enough to the same that the environments will always correspond.

We have some preexisting cases in the test suite that do things like

@
   do {
      let x = 3;
      let s = subshell ();
      let x = 4;
      s;
      return ();
   };
@

and check the value of @x@ in the subshell. (It should be 4 and not 3.)
These arose because the historic behavior was extremely squirrelly.
(Some history: #2751, #2306, #2243, #2242.)

These cases are now rejected.

Normal usage never does anything like this, and the oddities got
discovered by prodding, not by anyone stepping on them in the field.
Nonetheless, there's at least one reasonable usage that's now
prohibited, namely this function or one like it:

@
   let rebindable use_subshells = true;

   let maybe_subshell () = do {
      if use_subshells then
         subshell ()
      else
         return ();
   };
@

This provides a function that conditionally starts a subshell when
monad-bound, in the context of where that monad binding happens.

Though it's very limited because it has to return the subshell value
out without monad-binding it. This variant, for example, invokes the
subshell from inside the @maybe_subshell@ function, which means it
won't be able to see the caller's context:

@
   let rebindable use_subshells = true;

   let maybe_subshell () = do {
      if use_subshells then do {
         print "Subshell:";
         subshell ();
         return ();
      }
      else
         return ();
   };
@

Nonetheless, it's not an entirely unreasonable thing to do. If we
decide that disallowing cases like this that push the subshell value
around before actually invoking it is too restrictive, there is
another approach that should work. However, it's quite a bit more
complicated and at least for now we've decided not to implement it.
It goes as follows.

Instead of saving the typing environment in special-case expression
nodes, save the typing environment in monad-bind statements. Then
there's a typing environment available in case the monad bind runs a
subshell. To make that work, we'll need to add two new cases of
`Value`: @VSubshell@ and @VProofSubshell@. Make the builtin table
entries point at a `VLambda` of the form @\() -> VSubshell@. Then
applying the unit argument will give the `@VSubshell@` value, and
it'll appear at monad-bind time. In the monad-bind code, check for
@VSubshell@ and @VProofSubshell@ and dispatch them to the actual
subshell code, using the typing environment stored in the monad bind
statement.

Now, remove the current @Subshell@ and @ProofSubshell@ expressions and
the code for introducing them. Instead, write a conservative static
analysis that decides which monad bind sites might be subshells, and
mark them. Most won't be. Then have the typechecker capture a typing
environment only at the marked cases. This will avoid generating
hundreds or thousands of copies of the typing environment, which is
not a huge data structure but is large enough to be noticeable.

This alternate approach has at least a couple advantages; for example,
it hardcodes the strings "subshell" and "proof_subshell" in fewer
places, and doesn't require putting placeholder `Value` entries in the
builtins table. But it's markedly more complicated, and there are some
details that will be a headache to sort out, e.g. making stack traces
work right. Plus there's some risk that the above will not interact
correctly with, or interfere with, the monadic/deferred execution
behavior in the interpreter, which is about as robust as a spiderweb
mounted on a clock face.

Beyond all that there's a further complication, since the most basic
and normal use of @proof_subshell@ is like this:

@
   prove_print (proof_subshell ()) {{ ... }};
@

which /does not have an actual bind site/ anywhere in SAWScript: it
reduces to a Haskell value of type @ProofScript@ and then that gets
evaluated in the internals, which captures the interpreter's
environment at that point.

I'm going to deal with this for now by wrapping any subshell found in
an argument position in a do-block. That will result in different
semantics from the prior behavior if the argument is a parameter of a
SAWScript function which explicitly monad-binds that parameter after
doing some other local bindings. I think we will just suck that up.

-}

module SAWScript.Subshells (processExpr, processStmts) where

import Control.Exception (throwIO) -- XXX temporary
import Control.Monad (unless)
import qualified Data.IORef as IORef
import Data.IORef (IORef)

import SAWSupport.Console
import SAWSupport.ConsoleSupport (Fatal(..))
import SAWSupport.ScopedMap (ScopedMap)
import qualified SAWSupport.ScopedMap as ScopedMap

import qualified SAWCentral.Position as Pos
import SAWCentral.AST

import SAWScript.Panic


------------------------------------------------------------
-- Support logic

-- | Type for indicating what we have.
data IsSubshell = IsSubshell | NotSubshell

-- | Context type for the pass.
--
--   We keep a scoped map that remembers which names have been locally
--   defined. If we see the builtin names we're looking for in this
--   map, they don't actually refer to the builtins and shouldn't be
--   rewritten.
--
--   We also remember if we've already printed the long explanation,
--   so it only comes out once.
data Ctx = Ctx {
    ctxShadowed :: IORef (ScopedMap Name Bool),
    ctxExplained :: IORef Bool
}

-- | Create a new context.
newctx :: IO Ctx
newctx = do
    shadowed <- IORef.newIORef $ ScopedMap.empty
    explained <- IORef.newIORef False
    pure $ Ctx { ctxShadowed = shadowed, ctxExplained = explained }

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
-- Error handling tools

-- | Reject an expression
reject :: Ctx -> Expr -> IO Expr
reject ctx e = do
    let pos = Pos.getPos e
    -- XXX: until we fix up the console handling, errDP will
    -- exit, even though it isn't supposed to, and so the explanation
    -- doesn't appear.
    --errDP pos "Invalid use of subshell"
    commentP pos "Error: Invalid use of subshell"
    explained <- IORef.readIORef (ctxExplained ctx)
    unless explained $ do
                 --------------------------------------------------------------------------------
        noteN $ "The usage of the \"subshell\" and \"proof_subshell\" builtins is" <>
                " restricted."
        noteN $ "In a block or at the top level, use these forms:"
        noteN $ "   subshell ();"
        noteN $ "   proof_subshell ();"
        noteN $ "They may not be the final value of a block."
        noteN $ "As a function argument, use these forms:"
        noteN $ "   ... (subshell ()) ..."
        noteN $ "   ... (proof_subshell ()) ..."
        noteN $ "but note that the subshell will run in the caller's context."
        IORef.writeIORef (ctxExplained ctx) True
    -- XXX: bail out directly. remove when we switch the above back to errDP.
    throwIO (Fatal False)
{-
    -- return a placeholder expression (doesn't matter what type it
    -- is, we'll bail before reaching the typechecker)
    pure $ Bool pos False
-}


------------------------------------------------------------
-- Main recursive pass

-- | Process an expression.
--
--   If we see @subshell@ or @proof_subshell@, convert to the
--   special-case version, and mark the return value accordingly.
--
subshell'expr_raw :: Ctx -> Expr -> IO (IsSubshell, Expr)
subshell'expr_raw ctx e0 = case e0 of
    Bool{} -> pure (NotSubshell, e0)
    String{} -> pure (NotSubshell, e0)
    Int{} -> pure (NotSubshell, e0)
    Code{} -> pure (NotSubshell, e0)
    CType{} -> pure (NotSubshell, e0)
    Array pos es -> do
        es' <- mapM (subshell'expr ctx) es
        pure (NotSubshell, Array pos es')
    Block pos (stmts, e1) -> do
        -- A block is never a subshell, even though the block might
        -- contain one. Don't allow the result value at the end of the
        -- block to be a subshell though, as that executes in the
        -- parent context rather than the current context.
        pushScope ctx
        stmts' <- mapM (subshell'stmt ctx) stmts
        e1' <- subshell'expr ctx e1
        popScope ctx
        pure (NotSubshell, Block pos (stmts', e1'))
    Tuple pos es -> do
        es' <- mapM (subshell'expr ctx) es
        pure (NotSubshell, Tuple pos es')
    Record pos etbl -> do
        etbl' <- traverse (subshell'expr ctx) etbl
        pure (NotSubshell, Record pos etbl')
    Index pos e1 e2 -> do
        e1' <- subshell'expr ctx e1
        e2' <- subshell'expr ctx e2
        pure (NotSubshell, Index pos e1' e2')
    Lookup pos e1 field -> do
        e1' <- subshell'expr ctx e1
        pure (NotSubshell, Lookup pos e1' field)
    TLookup pos e1 field -> do
        e1' <- subshell'expr ctx e1
        pure (NotSubshell, TLookup pos e1' field)
    Var pos x -> do
        unshadowed <- not <$> isShadowed ctx x
        pure $ case x of
            "subshell" | unshadowed ->
                (IsSubshell, Subshell pos emptyAnnotations)
            "proof_subshell" | unshadowed ->
                (IsSubshell, ProofSubshell pos emptyAnnotations)
            _ ->
                (NotSubshell, Var pos x)
    Subshell{} ->
        panic "subshell'expr_raw" ["Preexisting Subshell expression"]
    ProofSubshell{} ->
        panic "subshell'expr_raw" ["Preexisting ProofSubshell expression"]
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
        pure (NotSubshell, Lambda pos mname paramPos params namedParams' body')
    Application pos e1 args -> do
        -- Allow applying args to a subshell. We don't have to check
        -- that it's only exactly one unit argument; the typechecker
        -- will do that.
        (isshell, e1') <- subshell'expr_raw ctx e1
        args' <- do
            let once (mname, e2) = do
                  e2' <- subshell'expr_wrap ctx e2
                  pure (mname, e2')
            mapM once args
        pure (isshell, Application pos e1' args')
    Let pos dg e1 -> do
        dg' <- subshell'declgroup ctx dg
        pushScope ctx
        e1' <- subshell'expr ctx e1
        popScope ctx
        pure (NotSubshell, Let pos dg' e1')
    TSig pos e1 ty -> do
        -- Allow type signatures on subshell expressions. No real reason
        -- not to.
        (isshell, e1') <- subshell'expr_raw ctx e1
        pure (isshell, TSig pos e1' ty)
    IfThenElse pos e1 e2 e3 -> do
        e1' <- subshell'expr ctx e1
        e2' <- subshell'expr ctx e2
        e3' <- subshell'expr ctx e3
        pure (NotSubshell, IfThenElse pos e1' e2' e3')

-- | Process an expression, and wrap it in an implicit do-block if
--   it's a subshell with its unit argument applied. (This is used for
--   applications so passing @proof_subshell@ directly to builtins
--   works as expected.) We don't have to check if the arguments
--   applied are actually just unit; the typechecker does that.
subshell'expr_wrap :: Ctx -> Expr -> IO Expr
subshell'expr_wrap ctx e = do
    (isshell, e') <- subshell'expr_raw ctx e
    let deny ee = case ee of
            Application{} -> False
            TSig _ ee' _ -> deny ee'
            _ -> True
    case isshell of
        NotSubshell -> pure e'
        IsSubshell
          | deny e' -> reject ctx e'
          | otherwise -> do
              let pos = Pos.getPos e'
              let bind = StmtBind pos (PImplicit pos Nothing) e'
                  unit = Tuple pos []
                  ret = Application pos (Var pos "return") [(Nothing, unit)]
              pure $ Block pos ([bind], ret)

-- | Process an expression, and reject it if it's a subshell.
--   (This is the common case.)
subshell'expr :: Ctx -> Expr -> IO Expr
subshell'expr ctx e = do
    (isshell, e') <- subshell'expr_raw ctx e
    case isshell of
        IsSubshell -> reject ctx e'
        NotSubshell -> pure e'

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
              -- rec-binding subshells is not allowed
              def' <- subshell'expr ctx $ dDef d
              popScope ctx
              pure $ d { dDef = def' }
        ds' <- mapM once ds
        pure $ Recursive ds'
    NonRecursive d -> do
        subshell'pat ctx $ dPat d
        pushScope ctx
        -- let-binding subshells is not allowed
        def' <- subshell'expr ctx $ dDef d
        popScope ctx
        let d' = d { dDef = def' }
        pure $ NonRecursive d'

-- | Process a statement.
subshell'stmt :: Ctx -> Stmt -> IO Stmt
subshell'stmt ctx s0 = case s0 of
    StmtBind spos pat e -> do
        subshell'pat ctx pat
        -- Binding subshells is ok.
        (_isshell, e') <- subshell'expr_raw ctx e
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

-- | Run the pass, and return an updated expression.
processExpr :: Expr -> IO Expr
processExpr e = do
    ctx <- newctx
    e' <- subshell'expr ctx e
    checkFail
    pure e'

-- | Run the pass, and return an updated statement list.
processStmts :: [Stmt] -> IO [Stmt]
processStmts stmts = do
    ctx <- newctx
    stmts' <- mapM (subshell'stmt ctx) stmts
    checkFail
    pure stmts'
