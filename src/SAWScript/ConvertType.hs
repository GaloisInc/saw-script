{-# LANGUAGE TypeOperators #-}

module SAWScript.ConvertType where

import SAWScript.Compiler

import SAWScript.AST
import SAWScript.Unify

import Control.Applicative
import Control.Monad
import Data.Either
import Data.List
import Data.Traversable

convertType :: Compiler (Module LType) (Module' LType Type)
convertType = groundType >=> defixType >=> removeEither

-- groundType {{{

groundType :: Compiler (Module LType) (Module' LType CType)
groundType = compiler "GroundType" $ traverseMB $ foldMuM gType

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
defixType = compiler "DefixType" $ traverseMB $ foldMuM dType

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
removeEither = compiler "RemoveEither" $ traverseMB unEither

unEither :: Either Int Type -> Err Type
unEither (Right t) = return t
unEither (Left x)  = fail ("nonsense type: " ++ show x)

-- }}}

traverseMB :: (Applicative f) => (a -> f b) -> Module' c a -> f (Module' c b)
traverseMB f (Module ds mb) = Module ds <$> traverse (traverse f) mb

