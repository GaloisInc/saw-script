{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}

module SAWScript.ResolveSyns where

import SAWScript.AST
import SAWScript.Unify
import SAWScript.Compiler

import Control.Applicative
import Control.Monad.Trans.Reader
import qualified Data.Map as Map
import Data.Traversable hiding (mapM)

resolveSyns :: Compiler (Module UnresolvedName RawT      RawT)
                        (Module UnresolvedName ResolvedT ResolvedT)
resolveSyns = compiler "ResolveSyns" resolveCompiler

resolveCompiler :: Module UnresolvedName RawT RawT
                -> Err (Module UnresolvedName ResolvedT ResolvedT)
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

instance Resolvable I where
  resolveF = return . inject
