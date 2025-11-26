{- |
Module      : SAWCore.Term.CtxTerm
Copyright   : Galois, Inc. 2018
License     : BSD3
Stability   : experimental
Portability : non-portable (language extensions)
-}

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
asCtorDTApp :: Name -> [(VarName, Term)] -> [index] -> Term -> Maybe [Term]
asCtorDTApp d params dt_ixs (ctxAsDataTypeApp d params dt_ixs ->
                                       Just (param_vars, ixs))
  | isVarList (map fst params) param_vars && not (any (usesDataType d) ixs)
  = Just ixs
  where
    -- Check that the given list of terms is a list of named
    -- variables, one for each parameter
    isVarList :: [VarName] -> [Term] -> Bool
    isVarList _ [] = True
    isVarList (p : ps) ((asVariable -> Just (x, _)) : ts) =
      x == p && isVarList ps ts
    isVarList _ _ = False
asCtorDTApp _ _ _ _ = Nothing


-- | Check that an argument for a constructor has one of the allowed forms
asCtorArg ::
  Name ->
  [(VarName, Term)] ->
  [index] ->
  Term ->
  Maybe CtorArg
asCtorArg d _ _ tp
  | not (usesDataType d tp)
  = Just (ConstArg tp)
asCtorArg d params dt_ixs tp =
  do let (zs, ret) = asPiList tp
     case asCtorDTApp d params dt_ixs ret of
       Just ixs
         | not (any (usesDataType d . snd) zs) ->
           Just (RecursiveArg zs ixs)
       _ ->
         Nothing

-- | Check that a constructor type is a pi-abstraction that takes as input an
-- argument of one of the allowed forms described by 'CtorArg'
asPiCtorArg ::
  Name ->
  [(VarName, Term)] ->
  [index] ->
  Term ->
  Maybe (VarName, CtorArg, Term)
asPiCtorArg d params dt_ixs t =
  case asPi t of
    Nothing -> Nothing
    Just (nm, tp, rest) ->
      case asCtorArg d params dt_ixs tp of
        Nothing -> Nothing
        Just arg -> Just (nm, arg, rest)

-- | Helper function for 'mkCtorArgStruct'
mkCtorArgsIxs ::
  Name ->
  [(VarName, Term)] ->
  [index] ->
  Term ->
  Maybe ([(VarName, CtorArg)], [Term])
mkCtorArgsIxs d params dt_ixs (asCtorDTApp d params dt_ixs -> Just ixs) =
  Just ([], ixs)
mkCtorArgsIxs d params dt_ixs ty =
  case asPiCtorArg d params dt_ixs ty of
    Nothing -> Nothing
    Just (x, arg, rest) ->
      case mkCtorArgsIxs d params dt_ixs rest of
        Nothing -> Nothing
        Just (args, ixs) -> Just ((x, arg) : args, ixs)

-- | Take in a datatype and bindings lists for its parameters and indices, and
-- also a prospective type of a constructor for that datatype, where the
-- constructor type is allowed to have the parameters but not the indices free.
-- Test that the constructor type is an allowed type for a constructor of this
-- datatype, and, if so, build a 'CtorArgStruct' for it.
mkCtorArgStruct ::
  Name ->
  [(VarName, Term)] ->
  [(VarName, Term)] ->
  Term ->
  Maybe CtorArgStruct
mkCtorArgStruct d params dt_ixs ctor_tp =
  case mkCtorArgsIxs d params dt_ixs ctor_tp of
    Nothing -> Nothing
    Just (args, ctor_ixs) ->
      Just (CtorArgStruct params args ctor_ixs)
