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
  Just t  -> resolveSig t

resolveSig :: RawSigT -> RS ResolvedT
resolveSig = foldMuM resolveF

class Functor f => Resolvable f where
  resolveF :: f ResolvedT -> RS ResolvedT

instance (Resolvable f, Resolvable g) => Resolvable (f :+: g) where
  resolveF cp = case cp of
    Inl e -> resolveF e
    Inr e -> resolveF e

instance Resolvable Syn where
  resolveF (Syn n) = do
    found <- getsSynEnv $ lookupEnv n
    case found of
      Nothing -> failRS $ "unbound type synonym: " ++ show n
      Just (Just t)  -> resolveSig t
      Just Nothing   -> undefined

instance Resolvable TypeF where
  resolveF typ = case typ of
    UnitF           -> return $ Just unit
    BitF            -> return $ Just bit
    ZF              -> return $ Just z
    QuoteF          -> return $ Just quote
    PVar n          -> return $ Just $ pVar n
    ArrayF t1 t2    -> return $ array <$> t1 <*> t2
    BlockF t1 t2    -> return $ block <$> t1 <*> t2
    TupleF ts       -> return $ tuple <$> sequenceA ts
    RecordF nts     -> return $ record <$> traverse (\(n,t) -> (,) <$> pure n <*> t) nts
    FunctionF t1 t2 -> return $ function <$> t1 <*> t2
    PAbs ns t       -> return $ pAbs ns <$> t
    

instance Resolvable ContextF where
  resolveF cxt = case cxt of
    CryptolSetupContext -> return $ Just cryptolSetupContext
    JavaSetupContext    -> return $ Just javaSetupContext   
    LLVMSetupContext    -> return $ Just llvmSetupContext   
    ProofScriptContext  -> return $ Just proofScriptContext 
    TopLevelContext     -> return $ Just topLevelContext    

instance Resolvable I where
  resolveF (I n) = return $ Just $ i n

