{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}

module SAWScript.ResolveSyns where

import SAWScript.AST
import SAWScript.Unify
import SAWScript.Compiler

import Control.Applicative
import Control.Monad.Trans.Reader
import Data.Traversable hiding (mapM)

resolveSyns :: Compiler (ModuleSimple RawT RawT) (ModuleSimple ResolvedT ResolvedT)
resolveSyns = compiler "ResolveSyns" $ \(Module nm ee te ds) -> evalRS te $ 
  Module nm <$> traverse (traverse resolve) ee <*> traverse resolve te <*> pure ds

type RS = ReaderT RSEnv Err
type RSEnv = Env RawT

evalRS :: RSEnv -> RS a -> Err a
evalRS e m = runReaderT m e

liftReader :: Err a -> RS a
liftReader = ReaderT . const

failRS :: String -> RS a
failRS = liftReader . fail

getSynEnv :: RS RSEnv
getSynEnv = ask

getsSynEnv :: (RSEnv -> a) -> RS a
getsSynEnv = asks

resolve :: RawT -> RS ResolvedT
resolve mt = case mt of
  Nothing -> return Nothing
  Just t  -> Just <$> resolveSig t

resolveSig :: RawSigT -> RS FullT
resolveSig = foldMuM resolveF

class Functor f => Resolvable f where
  resolveF :: f FullT -> RS FullT

instance (Resolvable f, Resolvable g) => Resolvable (f :+: g) where
  resolveF cp = case cp of
    Inl e -> resolveF e
    Inr e -> resolveF e

instance Resolvable Syn where
  resolveF (Syn n) = do
    found <- getsSynEnv $ lookupEnv n
    case found of
      Nothing       -> failRS $ "unbound type synonym: " ++ show n
      Just Nothing  -> failRS $ "type synonym mistakenly bound to abstract type: " ++ show n
      Just (Just t) -> resolveSig t

instance Resolvable TypeF where
  resolveF = return . inject
    

instance Resolvable ContextF where
  resolveF = return . inject

instance Resolvable I where
  resolveF = return . inject

