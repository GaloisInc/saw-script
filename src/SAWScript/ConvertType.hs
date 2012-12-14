{-# LANGUAGE TypeOperators #-}

module SAWScript.ConvertType where

import SAWScript.AST
import SAWScript.Unify

import Control.Monad
import Data.Either
import Data.List
import Data.Traversable

convertType :: Module LType -> Err (Module Type')
convertType = groundType >=> defixType >=> removeEither

-- groundType {{{

groundType :: Module LType -> Err (Module CType)
groundType m = case traverse (foldMuM gType) m of
  Left e   -> Left (intercalate "\n" ["GroundType: " ++ e, "in:", show m])
  Right m' -> Right m'

class Functor f => Groundable f where
  gType :: f CType -> Err CType

instance (Groundable f, Groundable g) => Groundable (f :+: g) where
  gType cp = case cp of
    Inl e -> gType e
    Inr e -> gType e

instance Groundable Logic where
  gType x = Left ("non-ground type: " ++ render x)

instance Groundable Type where
  gType = Right . inject

instance Groundable I where
  gType = Right . inject

-- }}}

-- defixType {{{

defixType :: Module CType -> Err (Module (Either Int Type'))
defixType m = case traverse (foldMuM dType) m of
  Left e -> Left (intercalate "\n" ["DefixType: " ++ e, "in:", show m])
  Right m' -> Right m'

class Functor f => Defixable f where
  dType :: f (Either Int Type') -> Err (Either Int Type')

instance (Defixable f, Defixable g) => Defixable (f :+: g) where
  dType cp = case cp of
    Inl e -> dType e
    Inr e -> dType e

instance Defixable Type where
  dType t = case t of
    Unit'                           -> Right $ Right UnitT
    Bit'                            -> Right $ Right BitT
    Z'                              -> Right $ Right ZT
    Quote'                          -> Right $ Right QuoteT
    Array' (Right t') (Left l)      -> Right $ Right $ ArrayT t' l
    Block' c (Right t')             -> Right $ Right $ BlockT c t'
    Tuple' ts
      | null $ lefts ts             -> Right $ Right $ TupleT $ rights ts
    Record' nts
      | null $ lefts $ map snd nts  -> let (ns,ts) = unzip nts in Right $ Right $ RecordT $ zip ns $ rights ts
    Function' (Right at) (Right bt) -> Right $ Right $ FunctionT at bt
    _                               -> Left ("Bad type: " ++ show t)

instance Defixable I where
  dType (I x) = Right $ Left x

-- }}}

-- removeEither {{{

removeEither :: Module (Either Int Type') -> Err (Module Type')
removeEither m = case traverse unEither m of
  Left e -> Left (intercalate "\n" ["RemoveEither: " ++ e, "in:", show m])
  Right m' -> Right m'

unEither :: Either Int Type' -> Err Type'
unEither (Right t) = Right t
unEither (Left x)  = Left ("nonsense type: " ++ show x)

-- }}}

