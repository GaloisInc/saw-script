{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}

module SAWScript.ResolveSyns where

import SAWScript.AST
import SAWScript.Unify
import SAWScript.Compiler

import Control.Applicative
import Control.Monad.Trans.Reader
import Data.Monoid
import Data.Foldable
import Data.Traversable hiding (mapM)

type RSType t = t RawT RawSigT

resolveSyns :: Compiler (RSType ModuleSimple) (RSType ModuleSimple)
resolveSyns = compiler "ResolveSyns" $ \m@(Module _ ds _) ->
  runReaderT (rSyns m) $ buildEnv ds

liftReader :: (Monad m) => m a -> RS a
liftReader = ReaderT . const

failRS :: String -> RS a
failRS = liftReader . fail

getSynEnv :: RS (Env RawT)
getSynEnv = ask

getsSynEnv :: (Env RawT -> a) -> RS a
getSSynEnv = asks

-- Env {{{

buildEnv :: [RSType TopStmt] -> Env RawT
buildEnv = foldMap extractSyn

extractSyn :: TopStmt MPType -> Env RawT
extractSyn s = case s of
  TypeDef n t -> singleton n pt
  _           -> empty

-- }}}

type RS = ReaderT (Env RawT) Err

class ResolveSyns f where
  rSyns :: f -> RS f

instance ResolveSyns (RSType ModuleSimple) where
  rSyns (Module nm ee te ds) = Module mname <$> mapM rSyns ee <*> rSyns mn

instance ResolveSyns (RSType TopStmtSimple) where
  rSyns s = case s of
    Import n mns mn  -> pure $ Import n mns mn
    TypeDef n pt     -> TypeDef n <$> rSyns pt
    TopTypeDecl n pt -> TopTypeDecl n <$> rSyns pt
    TopBind n e      -> TopBind n <$> rSyns e

instance ResolveSyns (RSType BlockStmt) where
  rSyns s = case s of
    Bind mn c e        -> Bind mn c <$> rSyns e
    BlockTypeDecl n pt -> BlockTypeDecl n <$> rSyns pt
    BlockLet nes       -> let (ns,es) = unzip nes in BlockLet <$> zip ns <$> mapM rSyns es

instance ResolveSyns (RSType Expr) where
  rSyns = traverse rSyns

instance ResolveSyns RawT where
  rSyns mpt = case mpt of
    Nothing -> return Nothing
    Just pt -> Just <$> rSyns pt

instance ResolveSyns RawSigT where
  rSyns = foldMuM resolve

class Functor f => Resolvable f where
  resolve :: f PType -> RS PType

instance (Resolvable f, Resolvable g) => Resolvable (f :+: g) where
  resolve cp = case cp of
    Inl e -> resolve e
    Inr e -> resolve e

instance Resolvable TypeF where
  resolve = fmap inject . traverse rSyns

instance Resolvable Poly where
  resolve = return . inject

instance Resolvable Syn where
  resolve t = do found <- getsSynEnv $ lookupType n
    case found of
      Nothing -> failRS $ "unbound type synonym: " ++ show n
      Just pt -> rSyns pt

instance Resolvable I where
  resolve = return . inject

