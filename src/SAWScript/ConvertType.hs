{-# LANGUAGE TypeOperators #-}

module SAWScript.ConvertType where

import SAWScript.Compiler

import SAWScript.AST
import SAWScript.Unify

import Control.Applicative
import Control.Monad
import Control.Monad.State
import Data.Either
import Data.List
import qualified Data.Traversable as T

convertType :: Compiler (Module LType) (Module' PType Type)
convertType = groundType >=> defixType >=> removeEither >=> reifyDeclarations

varNames = drop 1 (("" : names') ++ ((++) <$> varNames <*> names'))
  where
  names' = [ [c] | c <- ['a'..'z'] ]

-- groundType {{{

groundType :: Compiler (Module LType) (Module' LType CType)
groundType = compiler "GroundType" $ \(Module ds mn) -> 
  Module ds <$> traverseFA gType mn

class Functor f => Groundable f where
  gType :: f CType -> Err CType

instance (Groundable f, Groundable g) => Groundable (f :+: g) where
  gType cp = case cp of
    Inl e -> gType e
    Inr e -> gType e

instance Groundable Logic where
  gType x = fail ("non-ground type: " ++ render x)

instance Groundable TypeF where
  gType = return . inject

instance Groundable I where
  gType = return . inject

-- }}}

-- defixType {{{

defixType :: Compiler (Module' LType CType) (Module' LType (Either Int Type))
defixType = compiler "DefixType" $ \(Module ds mn) ->
  Module ds <$> traverseFA dType mn

class Functor f => Defixable f where
  dType :: f (Either Int Type) -> Err (Either Int Type)

instance (Defixable f, Defixable g) => Defixable (f :+: g) where
  dType cp = case cp of
    Inl e -> dType e
    Inr e -> dType e

instance Defixable TypeF where
  dType t = case t of
    Unit'                           -> return $ Right UnitT
    Bit'                            -> return $ Right BitT
    Z'                              -> return $ Right ZT
    Quote'                          -> return $ Right QuoteT
    Array' (Right t') (Left l)      -> return $ Right $ ArrayT t' l
    Block' c (Right t')             -> return $ Right $ BlockT c t'
    Tuple' ts
      | null $ lefts ts             -> return $ Right $ TupleT $ rights ts
    Record' nts
      | null $ lefts $ map snd nts  -> let (ns,ts) = unzip nts in return $ Right $ RecordT $ zip ns $ rights ts
    Function' (Right at) (Right bt) -> return $ Right $ FunctionT at bt
    _                               -> fail ("Bad type: " ++ show t)

instance Defixable I where
  dType (I x) = return $ Left x

-- }}}

-- removeEither {{{

removeEither :: Compiler (Module' LType (Either Int Type)) (Module' LType Type)
removeEither = compiler "RemoveEither" $ \(Module ds mn) ->
  Module ds <$> T.traverse unEither mn

unEither :: Either Int Type -> Err Type
unEither (Right t) = return t
unEither (Left x)  = fail ("nonsense type: " ++ show x)

-- }}}

reifyDeclarations :: Compiler (Module' LType Type) (Module' PType Type)
reifyDeclarations = compiler "ReifyDeclarations" $ \(Module ds mn) ->
  Module <$> mapM runRDecs ds <*> pure mn
  where
  runRDecs = return . flip evalState initRState . traverseFA rDecs

class Functor f => ReifyDecs f where
  rDecs :: f PType -> State ReifyState PType

data ReifyState = ReifyState
  { reifyGen :: [String]
  , reifyEnv :: [(Index,PType)]
  }

initRState = ReifyState
  { reifyGen = varNames
  , reifyEnv = []
  }

instance (ReifyDecs f, ReifyDecs g) => ReifyDecs (f :+: g) where
  rDecs cp = case cp of
    Inl e -> rDecs e
    Inr e -> rDecs e

instance ReifyDecs I where
  rDecs (I n) = return $ i n

instance ReifyDecs TypeF where
  rDecs typ = case typ of
    Unit'           -> return unit
    Bit'            -> return bit
    Z'              -> return z
    Quote'          -> return quote
    Array' ar t     -> return $ array ar t
    Block' c t      -> return $ block c t
    Tuple' ts       -> return $ tuple ts
    Record' nts     -> return $ record nts
    Function' at bt -> return $ function at bt
    Syn n           -> return $ syn n

instance ReifyDecs Logic where
  rDecs (LV n) = do
    mt <- gets $ lookup n . reifyEnv
    case mt of
      Just t -> return t
      Nothing -> newVar n

newVar :: Index -> State ReifyState PType
newVar i = do
  n <- gets $ head . reifyGen
  let v = poly n
  modify $ \(ReifyState g e) ->
    ReifyState (tail g) ((i,v):e)
  return v

