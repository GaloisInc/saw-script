{- |
Module      : SAWCore.Term.CtxTerm
Copyright   : Galois, Inc. 2018
License     : BSD3
Stability   : experimental
Portability : non-portable (language extensions)
-}

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}

module SAWCore.Term.CtxTerm
  ( mkCtorArgStruct
  ) where

import Control.Monad

import SAWCore.Module (CtorArg(..), CtorArgStruct(..))
import SAWCore.Name
import SAWCore.Recognizer
import SAWCore.SharedTerm
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

-- | Test whether a specific datatype occurs in a term.
usesDataType :: Name -> Term -> Bool
usesDataType d t =
  case unwrapTermF t of
    Constant d'
      | d' == d -> True
    FTermF (Recursor (recursorDataType -> d'))
      | d' == d -> True
    tf -> any (usesDataType d) tf

-- | Check that a type is a valid application of datatype @d@ for use in
-- specific ways in the type of a constructor for @d@. This requires that this
-- application of @d@ be of the form
--
-- > d p1 .. pn x1 .. xm
--
-- where the @pi@ are the distinct bound variables bound in the @params@
-- context, given as argument, and that the @xj@ have no occurrences of @d@. If
-- the given type is of this form, return the @xj@.
asCtorDTApp :: Name -> [ExtCns Term] ->
               [index] ->
               Term ->
               Maybe [Term]
asCtorDTApp d params dt_ixs (ctxAsDataTypeApp d params dt_ixs ->
                                       Just (param_vars, ixs))
  | isVarList params param_vars && not (any (usesDataType d) ixs)
  = Just ixs
  where
    -- Check that the given list of terms is a list of named
    -- variables, one for each parameter
    isVarList :: [ExtCns Term] -> [Term] -> Bool
    isVarList _ [] = True
    isVarList (p : ps) ((asVariable -> Just ec) : ts) =
      ec == p && isVarList ps ts
    isVarList _ _ = False
asCtorDTApp _ _ _ _ = Nothing


-- | Check that an argument for a constructor has one of the allowed forms
asCtorArg ::
  SharedContext ->
  Name ->
  [ExtCns Term] ->
  [index] ->
  Term ->
  IO (Maybe CtorArg)
asCtorArg _ d _ _ tp
  | not (usesDataType d tp)
  = pure $ Just (ConstArg tp)
asCtorArg sc d params dt_ixs tp =
  do (zs, ret) <- scAsPiList sc tp
     case asCtorDTApp d params dt_ixs ret of
       Just ixs
         | not (any (usesDataType d . ecType) zs) ->
           pure $ Just (RecursiveArg zs ixs)
       _ ->
         pure Nothing

-- | Check that a constructor type is a pi-abstraction that takes as input an
-- argument of one of the allowed forms described by 'CtorArg'
asPiCtorArg ::
  SharedContext ->
  Name ->
  [ExtCns Term] ->
  [index] ->
  Term ->
  IO (Maybe (VarName, CtorArg, Term))
asPiCtorArg sc d params dt_ixs t =
  scAsPi sc t >>= \case
    Nothing -> pure Nothing
    Just (ec, rest) ->
      asCtorArg sc d params dt_ixs (ecType ec) >>= \case
        Nothing -> pure Nothing
        Just arg -> pure $ Just (ecName ec, arg, rest)

-- | Helper function for 'mkCtorArgStruct'
mkCtorArgsIxs ::
  SharedContext ->
  Name ->
  [ExtCns Term] ->
  [index] ->
  Term ->
  IO (Maybe ([(VarName, CtorArg)], [Term]))
mkCtorArgsIxs _sc d params dt_ixs (asCtorDTApp d params dt_ixs -> Just ixs) =
  pure $ Just ([], ixs)
mkCtorArgsIxs sc d params dt_ixs ty =
  asPiCtorArg sc d params dt_ixs ty >>= \case
    Nothing -> pure Nothing
    Just (x, arg, rest) ->
      mkCtorArgsIxs sc d params dt_ixs rest >>= \case
        Nothing -> pure Nothing
        Just (args, ixs) -> pure $ Just ((x, arg) : args, ixs)

-- | Take in a datatype and bindings lists for its parameters and indices, and
-- also a prospective type of a constructor for that datatype, where the
-- constructor type is allowed to have the parameters but not the indices free.
-- Test that the constructor type is an allowed type for a constructor of this
-- datatype, and, if so, build a 'CtorArgStruct' for it.
mkCtorArgStruct ::
  SharedContext ->
  Name ->
  [ExtCns Term] ->
  [ExtCns Term] ->
  Term ->
  IO (Maybe CtorArgStruct)
mkCtorArgStruct sc d params dt_ixs ctor_tp =
  mkCtorArgsIxs sc d params dt_ixs ctor_tp >>= \case
    Nothing -> pure Nothing
    Just (args, ctor_ixs) ->
      pure $ Just (CtorArgStruct params args ctor_ixs)
