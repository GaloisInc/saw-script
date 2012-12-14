{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}

module SAWScript.ResolveSyns where

import SAWScript.AST
import SAWScript.Unify

import Control.Applicative
import Control.Monad.Trans.Reader
import Data.List
import Data.Foldable
import Data.Traversable hiding (mapM)

resolveSyns :: Module MPType -> Err (Module MPType)
resolveSyns m@(Module ds mb) = case res of
  Left e -> Left (intercalate "\n" ["ResolveSyns: " ++ e, "in:",show m])
  Right m' -> Right m'
  where
    env = buildEnv ds
    res = runReaderT (rSyns m) env

liftReader :: (Monad m) => m a -> ReaderT e m a
liftReader = ReaderT . const

-- Env {{{

buildEnv :: [TopStmt MPType] -> Env
buildEnv = foldMap extractSyn

extractSyn :: TopStmt MPType -> Env
extractSyn s = case s of
  TypeDef n pt -> [(n,pt)]
  _            -> []

-- }}}

type Env = [(Name,PType)]
type RS = ReaderT Env Err

class ResolveSyns f where
  rSyns :: f -> RS f

instance ResolveSyns (Module MPType) where
  rSyns (Module ds mb) = Module <$> mapM rSyns ds <*> mapM rSyns mb

instance ResolveSyns (TopStmt MPType) where
  rSyns s = case s of
    Import n mns mn  -> return (Import n mns mn)
    TypeDef n pt     -> TypeDef n <$> rSyns pt
    TopTypeDecl n pt -> TopTypeDecl n <$> rSyns pt
    TopLet nes       -> let (ns,es) = unzip nes in TopLet <$> zip ns <$> mapM rSyns es

instance ResolveSyns (BlockStmt MPType) where
  rSyns s = case s of
    Bind mn c e        -> Bind mn c <$> rSyns e
    BlockTypeDecl n pt -> BlockTypeDecl n <$> rSyns pt
    BlockLet nes       -> let (ns,es) = unzip nes in BlockLet <$> zip ns <$> mapM rSyns es

instance ResolveSyns (Expr MPType) where
  rSyns = traverse rSyns

instance ResolveSyns MPType where
  rSyns mpt = case mpt of
    Nothing -> return Nothing
    Just pt -> Just <$> rSyns pt

instance ResolveSyns PType where
  rSyns = foldMuM resolve

class Functor f => Resolvable f where
  resolve :: f PType -> RS PType

instance (Resolvable f, Resolvable g) => Resolvable (f :+: g) where
  resolve cp = case cp of
    Inl e -> resolve e
    Inr e -> resolve e

instance Resolvable Type where
  resolve t = case t of
    Syn n -> do found <- asks $ lookup n
                case found of
                  Nothing -> liftReader $ Left ("unbound type synonym: " ++ show n)
                  Just pt -> rSyns pt
    _     -> fmap inject $ traverse rSyns t

instance Resolvable Poly where
  resolve = return . inject

instance Resolvable I where
  resolve = return . inject

