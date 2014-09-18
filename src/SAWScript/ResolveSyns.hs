{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}

module SAWScript.ResolveSyns where

import SAWScript.AST
import SAWScript.Unify.Fix
import SAWScript.Compiler

import Control.Applicative
import Data.Traversable hiding (mapM)

resolveSyns :: Compiler (Module UnresolvedName RawT     )
                        (Module UnresolvedName ResolvedT)
resolveSyns = compiler "ResolveSyns" resolveCompiler

resolveCompiler :: Module UnresolvedName RawT
                -> Err (Module UnresolvedName ResolvedT)
resolveCompiler (Module nm ee pe ds cs) =
    Module nm <$> traverse (traverse (traverse resolve)) ee <*>
                  traverse resolve pe <*>
                  pure ds <*>
                  pure cs

resolve :: RawT -> Err ResolvedT
resolve = traverse resolveSig

resolveSig :: RawSigT -> Err FullT
resolveSig = foldMuM resolveF

class Functor f => Resolvable f where
  resolveF :: f FullT -> Err FullT

instance (Resolvable f, Resolvable g) => Resolvable (f :+: g) where
  resolveF cp = case cp of
    Inl e -> resolveF e
    Inr e -> resolveF e

instance Resolvable Syn where
  resolveF (Syn n) = fail $ "unbound type variable: " ++ show n

instance Resolvable TypeF where
  resolveF = return . inject


instance Resolvable ContextF where
  resolveF = return . inject
