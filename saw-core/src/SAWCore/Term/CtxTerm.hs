{- |
Module      : SAWCore.Term.CtxTerm
Copyright   : Galois, Inc. 2018
License     : BSD3
Stability   : experimental
Portability : non-portable (language extensions)
-}

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}

module SAWCore.Term.CtxTerm
  (
    -- * Constructor Argument Types
    CtorArg(..)
  , CtorArgStruct(..)
    -- * Parsing and Building Constructor Types
  , mkCtorArgStruct
  ) where

import Control.Monad

import SAWCore.Name
import SAWCore.Recognizer
import SAWCore.Term.Functor

-- | Test if a 'Term' is an application of a specific datatype with the
-- supplied context of parameters and indices
ctxAsDataTypeApp :: Name -> [param] ->
                    [index] -> Term ->
                    Maybe ([Term], [Term])
ctxAsDataTypeApp d params ixs t =
  do let (f, args) = asApplyAll t
     d' <- asConstant f
     guard (d == d')
     guard (length args == length params + length ixs)
     let (params', ixs') = splitAt (length params) args
     pure (params', ixs')

--
-- * Constructor Argument Types
--

-- | A specification of the type of an argument for a constructor of datatype
-- @d@, that has a specified list @ixs@ of indices, inside a context @ctx@ of
-- parameters and earlier arguments
data CtorArg where
  -- | A fixed, constant type
  ConstArg :: Term -> CtorArg
  -- | The construct @'RecursiveArg [(z1,tp1),..,(zn,tpn)] [e1,..,ek]'@
  -- specifies a recursive argument type of the form
  --
  -- > (z1::tp1) -> .. -> (zn::tpn) -> d p1 .. pm e1 .. ek
  --
  -- where @d@ is the datatype, the @zi::tpi@ are the elements of the Pi
  -- context (the first argument to 'RecursiveArgType'), the @pi@ are the
  -- parameters of @d@ (not given here), and the @ei@ are the type indices of
  -- @d@.
  RecursiveArg ::
    [(LocalName, Term)] ->
    [Term] ->
    CtorArg

-- | A structure that defines the parameters, arguments, and return type indices
-- of a constructor, using 'Term' and friends to get the bindings right
data CtorArgStruct =
  CtorArgStruct
  {
    ctorParams :: [(LocalName, Term)],
    ctorArgs :: [(LocalName, CtorArg)],
    ctorIndices :: [Term],
    dataTypeIndices :: [(LocalName, Term)]
  }


--
-- * Parsing and Building Constructor Types
--

-- | Generic method for testing whether a datatype occurs in an object
class UsesDataType a where
  usesDataType :: Name -> a -> Bool

instance UsesDataType (TermF Term) where
  usesDataType d (Constant d')
    | d' == d = True
--  usesDataType d (FTermF (DataTypeApp d' _ _))
--    | d' == d = True
  usesDataType d (FTermF (RecursorType d' _ _ _))
    | d' == d = True
  usesDataType d (FTermF (Recursor rec))
    | recursorDataType rec == d = True
  usesDataType d tf = any (usesDataType d) tf

instance UsesDataType Term where
  usesDataType d = usesDataType d . unwrapTermF

instance UsesDataType [(LocalName, Term)] where
  usesDataType _ [] = False
  usesDataType d ((_, tp) : tps) = usesDataType d tp || usesDataType d tps


-- | Check that a type is a valid application of datatype @d@ for use in
-- specific ways in the type of a constructor for @d@. This requires that this
-- application of @d@ be of the form
--
-- > d p1 .. pn x1 .. xm
--
-- where the @pi@ are the distinct bound variables bound in the @params@
-- context, given as argument, and that the @xj@ have no occurrences of @d@. If
-- the given type is of this form, return the @xj@.
asCtorDTApp :: Name -> [param] ->
               [index] ->
               [a] ->
               [b] ->
               Term ->
               Maybe [Term]
asCtorDTApp d params dt_ixs ctx1 ctx2 (ctxAsDataTypeApp d params dt_ixs ->
                                       Just (param_vars, ixs))
  | isVarList params ctx1 ctx2 param_vars &&
    not (any (usesDataType d) ixs)
  = Just ixs
  where
    -- Check that the given list of terms is a list of bound variables, one for
    -- each parameter, in the context extended by the given arguments
    isVarList :: [param] ->
                 [a] ->
                 [b] ->
                 [Term] ->
                 Bool
    isVarList _ _ _ [] = True
    isVarList (_ : ps) c1 c2 ((unwrapTermF -> LocalVar i) : ts) =
      i == length ps + length c1 + length c2 &&
      isVarList ps c1 c2 ts
    isVarList _ _ _ _ = False
asCtorDTApp _ _ _ _ _ _ = Nothing


-- | Check that an argument for a constructor has one of the allowed forms
asCtorArg :: Name -> [param] ->
             [index] ->
             [prev] ->
             Term ->
             Maybe CtorArg
asCtorArg d params dt_ixs prevs (asPiList ->
                                 (zs,
                                  asCtorDTApp d params dt_ixs prevs zs ->
                                  Just ixs))
  | not (usesDataType d zs)
  = Just (RecursiveArg zs ixs)
asCtorArg d _ _ _ tp
  | not (usesDataType d tp)
  = Just (ConstArg tp)
asCtorArg _ _ _ _ _ = Nothing

-- | Check that a constructor type is a pi-abstraction that takes as input an
-- argument of one of the allowed forms described by 'CtorArg'
asPiCtorArg :: Name -> [param] ->
               [index] ->
               [prev] ->
               Term ->
               Maybe (LocalName, CtorArg, Term)
asPiCtorArg d params dt_ixs prevs t =
  case asPi t of
    Just (x, asCtorArg d params dt_ixs prevs -> Just arg, rest) ->
      Just (x, arg, rest)
    _ ->
      Nothing

-- | Helper function for 'mkCtorArgStruct'
mkCtorArgsIxs :: Name -> [param] ->
                 [index] ->
                 [(LocalName, CtorArg)] ->
                 Term ->
                 Maybe ([(LocalName, CtorArg)], [Term])
mkCtorArgsIxs d params dt_ixs prevs (asPiCtorArg d params dt_ixs prevs ->
                                     Just (x, arg, rest)) =
  case mkCtorArgsIxs d params dt_ixs (prevs ++ [(x, arg)]) rest of
    Just (args, ixs) -> Just ((x, arg) : args, ixs)
    Nothing -> Nothing
mkCtorArgsIxs d params dt_ixs prevs (asCtorDTApp d params dt_ixs prevs [] ->
                                     Just ixs) =
  Just ([], ixs)
mkCtorArgsIxs _ _ _ _ _ = Nothing


-- | Take in a datatype and bindings lists for its parameters and indices, and
-- also a prospective type of a constructor for that datatype, where the
-- constructor type is allowed to have the parameters but not the indices free.
-- Test that the constructor type is an allowed type for a constructor of this
-- datatype, and, if so, build a 'CtorArgStruct' for it.
mkCtorArgStruct ::
  Name ->
  [(LocalName, Term)] ->
  [(LocalName, Term)] ->
  Term ->
  Maybe CtorArgStruct
mkCtorArgStruct d params dt_ixs ctor_tp =
  case mkCtorArgsIxs d params dt_ixs [] ctor_tp of
    Just (args, ctor_ixs) ->
      Just (CtorArgStruct params args ctor_ixs dt_ixs)
    Nothing -> Nothing
