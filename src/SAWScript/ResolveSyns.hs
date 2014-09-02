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
resolveCompiler (Module nm ee pe te ds cs) =
  evalRS tes $
    Module nm <$> traverse (traverse resolve) ee <*>
                  traverse resolve pe <*>
                  traverse resolve te <*>
                  pure ds <*>
                  pure cs
      where tes = Map.unions $ te : map (fixup . moduleTypeEnv) (Map.elems ds)
            fixup :: LEnv ResolvedT -> LEnv RawT
            fixup e = Map.fromList
                      [ (n, Nothing) | (n, Nothing) <- Map.toList e ]

type RS = ReaderT RSEnv Err
type RSEnv = LEnv RawT

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
    found <- getsSynEnv $ lookupLEnv n
    case found of
      Nothing       -> failRS $ "unbound type synonym: " ++ show n
      Just Nothing  -> return $ abstract (getVal n)
      Just (Just t) -> resolveSig t

instance Resolvable TypeF where
  resolveF = return . inject


instance Resolvable ContextF where
  resolveF = return . inject

instance Resolvable I where
  resolveF = return . inject
