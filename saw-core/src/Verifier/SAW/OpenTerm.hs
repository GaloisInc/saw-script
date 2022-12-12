{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}

{- |
Module      : Verifier.SAW.OpenTerm
Copyright   : Galois, Inc. 2018
License     : BSD3
Stability   : experimental
Portability : non-portable (language extensions)

This module defines an interface to building SAW core terms in an incrementally
type-checked way, meaning that type-checking is performed as the terms are
built.
-}

module Verifier.SAW.OpenTerm (
  -- * Open terms and converting to closed terms
  OpenTerm(..), completeOpenTerm, completeNormOpenTerm, completeOpenTermType,
  -- * Basic operations for building open terms
  closedOpenTerm, openOpenTerm, failOpenTerm,
  bindTCMOpenTerm, bindPPOpenTerm, openTermType,
  flatOpenTerm, sortOpenTerm, natOpenTerm,
  unitOpenTerm, unitTypeOpenTerm,
  stringLitOpenTerm, stringTypeOpenTerm,
  trueOpenTerm, falseOpenTerm, boolOpenTerm, boolTypeOpenTerm,
  arrayValueOpenTerm, vectorTypeOpenTerm, bvLitOpenTerm, bvTypeOpenTerm,
  pairOpenTerm, pairTypeOpenTerm, pairLeftOpenTerm, pairRightOpenTerm,
  tupleOpenTerm, tupleTypeOpenTerm, projTupleOpenTerm,
  tupleOpenTerm', tupleTypeOpenTerm',
  recordOpenTerm, recordTypeOpenTerm, projRecordOpenTerm,
  ctorOpenTerm, dataTypeOpenTerm, globalOpenTerm, identOpenTerm, extCnsOpenTerm,
  applyOpenTerm, applyOpenTermMulti, applyGlobalOpenTerm,
  applyPiOpenTerm, piArgOpenTerm,
  lambdaOpenTerm, lambdaOpenTermMulti, piOpenTerm, piOpenTermMulti,
  arrowOpenTerm, letOpenTerm, sawLetOpenTerm, list1OpenTerm,
  -- * Monadic operations for building terms with binders
  OpenTermM(..), completeOpenTermM,
  dedupOpenTermM, lambdaOpenTermM, piOpenTermM,
  lambdaOpenTermAuxM, piOpenTermAuxM
  ) where

import qualified Data.Vector as V
import Control.Monad
import Control.Monad.State
import Control.Monad.Writer
import Data.Text (Text)
import Numeric.Natural

import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap

import Verifier.SAW.Term.Functor
import Verifier.SAW.Term.Pretty
import Verifier.SAW.SharedTerm
import Verifier.SAW.SCTypeCheck
import Verifier.SAW.Module
import Verifier.SAW.Recognizer

-- | An open term is represented as a type-checking computation that computes a
-- SAW core term and its type
newtype OpenTerm = OpenTerm { unOpenTerm :: TCM TypedTerm }

-- | "Complete" an 'OpenTerm' to a closed term or 'fail' on type-checking error
completeOpenTerm :: SharedContext -> OpenTerm -> IO Term
completeOpenTerm sc (OpenTerm termM) =
  either (fail . show) return =<<
  runTCM (typedVal <$> termM) sc Nothing []

-- | "Complete" an 'OpenTerm' to a closed term and 'betaNormalize' the result
completeNormOpenTerm :: SharedContext -> OpenTerm -> IO Term
completeNormOpenTerm sc m =
  completeOpenTerm sc m >>= sawLetMinimize sc >>= betaNormalize sc

-- | "Complete" an 'OpenTerm' to a closed term for its type
completeOpenTermType :: SharedContext -> OpenTerm -> IO Term
completeOpenTermType sc (OpenTerm termM) =
  either (fail . show) return =<<
  runTCM (typedType <$> termM) sc Nothing []

-- | Embed a closed 'Term' into an 'OpenTerm'
closedOpenTerm :: Term -> OpenTerm
closedOpenTerm t = OpenTerm $ typeInferComplete t

-- | Embed a 'Term' in the given typing context into an 'OpenTerm'
openOpenTerm :: [(LocalName, Term)] -> Term -> OpenTerm
openOpenTerm ctx t =
  -- Extend the local type-checking context, wherever this OpenTerm gets used,
  -- by appending ctx to the end, so that variables 0..length ctx-1 all get
  -- type-checked with ctx. If these are really the only free variables, then it
  -- won't matter what the rest of the ambient context is.
  --
  -- FIXME: we should check that the free variables of t are all < length ctx
  OpenTerm $ withCtx ctx $ typeInferComplete t

-- | Build an 'OpenTerm' that 'fail's in the underlying monad when completed
failOpenTerm :: String -> OpenTerm
failOpenTerm str = OpenTerm $ fail str

-- | Bind the result of a type-checking computation in building an 'OpenTerm'.
-- NOTE: this operation should be considered "unsafe" because it can create
-- malformed 'OpenTerm's if the result of the 'TCM' computation is used as part
-- of the resulting 'OpenTerm'. For instance, @a@ should not be 'OpenTerm'.
bindTCMOpenTerm :: TCM a -> (a -> OpenTerm) -> OpenTerm
bindTCMOpenTerm m f = OpenTerm (m >>= unOpenTerm . f)

-- | Bind the result of pretty-printing an 'OpenTerm' while building another
bindPPOpenTerm :: OpenTerm -> (String -> OpenTerm) -> OpenTerm
bindPPOpenTerm (OpenTerm m) f =
  OpenTerm $
  do ctx <- askCtx
     t <- typedVal <$> m
     unOpenTerm $ f $ renderSawDoc defaultPPOpts $
       ppTermInCtx defaultPPOpts (map fst ctx) t

-- | Return type type of an 'OpenTerm' as an 'OpenTerm
openTermType :: OpenTerm -> OpenTerm
openTermType (OpenTerm m) =
  OpenTerm $ do TypedTerm _ tp <- m
                ctx <- askCtx
                tp_tp <- liftTCM scTypeOf' (map snd ctx) tp
                return (TypedTerm tp tp_tp)

-- | Build an 'OpenTerm' from a 'FlatTermF'
flatOpenTerm :: FlatTermF OpenTerm -> OpenTerm
flatOpenTerm ftf = OpenTerm $
  (sequence (fmap unOpenTerm ftf) >>= typeInferComplete)

-- | Build an 'OpenTerm' for a sort
sortOpenTerm :: Sort -> OpenTerm
sortOpenTerm s = flatOpenTerm (Sort s False)

-- | Build an 'OpenTerm' for a natural number literal
natOpenTerm :: Natural -> OpenTerm
natOpenTerm = flatOpenTerm . NatLit

-- | The 'OpenTerm' for the unit value
unitOpenTerm :: OpenTerm
unitOpenTerm = flatOpenTerm UnitValue

-- | The 'OpenTerm' for the unit type
unitTypeOpenTerm :: OpenTerm
unitTypeOpenTerm = flatOpenTerm UnitType

-- | Build a SAW core string literal.
stringLitOpenTerm :: Text -> OpenTerm
stringLitOpenTerm = flatOpenTerm . StringLit

-- | Return the SAW core type @String@ of strings.
stringTypeOpenTerm :: OpenTerm
stringTypeOpenTerm = globalOpenTerm "Prelude.String"

-- | The 'True' value as a SAW core term
trueOpenTerm :: OpenTerm
trueOpenTerm = globalOpenTerm "Prelude.True"

-- | The 'False' value as a SAW core term
falseOpenTerm :: OpenTerm
falseOpenTerm = globalOpenTerm "Prelude.False"

-- | Convert a 'Bool' to a SAW core term
boolOpenTerm :: Bool -> OpenTerm
boolOpenTerm True = globalOpenTerm "Prelude.True"
boolOpenTerm False = globalOpenTerm "Prelude.False"

-- | The 'Bool' type as a SAW core term
boolTypeOpenTerm :: OpenTerm
boolTypeOpenTerm = globalOpenTerm "Prelude.Bool"

-- | Build an 'OpenTerm' for an array literal
arrayValueOpenTerm :: OpenTerm -> [OpenTerm] -> OpenTerm
arrayValueOpenTerm tp elems =
  flatOpenTerm $ ArrayValue tp $ V.fromList elems

-- | Create a SAW core term for a bitvector literal
bvLitOpenTerm :: [Bool] -> OpenTerm
bvLitOpenTerm bits =
  arrayValueOpenTerm boolTypeOpenTerm $ map boolOpenTerm bits

-- | Create a SAW core term for a vector type
vectorTypeOpenTerm :: OpenTerm -> OpenTerm -> OpenTerm
vectorTypeOpenTerm n a = applyGlobalOpenTerm "Prelude.Vec" [n,a]

-- | Create a SAW core term for the type of a bitvector
bvTypeOpenTerm :: Integral a => a -> OpenTerm
bvTypeOpenTerm n =
  applyOpenTermMulti (globalOpenTerm "Prelude.Vec")
  [natOpenTerm (fromIntegral n), boolTypeOpenTerm]

-- | Build an 'OpenTerm' for a pair
pairOpenTerm :: OpenTerm -> OpenTerm -> OpenTerm
pairOpenTerm t1 t2 = flatOpenTerm $ PairValue t1 t2

-- | Build an 'OpenTerm' for a pair type
pairTypeOpenTerm :: OpenTerm -> OpenTerm -> OpenTerm
pairTypeOpenTerm t1 t2 = flatOpenTerm $ PairType t1 t2

-- | Build an 'OpenTerm' for the left projection of a pair
pairLeftOpenTerm :: OpenTerm -> OpenTerm
pairLeftOpenTerm t = flatOpenTerm $ PairLeft t

-- | Build an 'OpenTerm' for the right projection of a pair
pairRightOpenTerm :: OpenTerm -> OpenTerm
pairRightOpenTerm t = flatOpenTerm $ PairRight t

-- | Build a right-nested tuple as an 'OpenTerm'
tupleOpenTerm :: [OpenTerm] -> OpenTerm
tupleOpenTerm = foldr pairOpenTerm unitOpenTerm

-- | Build a right-nested tuple type as an 'OpenTerm'
tupleTypeOpenTerm :: [OpenTerm] -> OpenTerm
tupleTypeOpenTerm = foldr pairTypeOpenTerm unitTypeOpenTerm

-- | Project the @n@th element of a right-nested tuple type
projTupleOpenTerm :: Integer -> OpenTerm -> OpenTerm
projTupleOpenTerm 0 t = pairLeftOpenTerm t
projTupleOpenTerm i t = projTupleOpenTerm (i-1) (pairRightOpenTerm t)

-- | Build a right-nested tuple as an 'OpenTerm' but without adding a final unit
-- as the right-most element
tupleOpenTerm' :: [OpenTerm] -> OpenTerm
tupleOpenTerm' [] = unitOpenTerm
tupleOpenTerm' ts = foldr1 pairTypeOpenTerm ts

-- | Build a right-nested tuple type as an 'OpenTerm'
tupleTypeOpenTerm' :: [OpenTerm] -> OpenTerm
tupleTypeOpenTerm' [] = unitTypeOpenTerm
tupleTypeOpenTerm' ts = foldr1 pairTypeOpenTerm ts

-- | Build a record value as an 'OpenTerm'
recordOpenTerm :: [(FieldName, OpenTerm)] -> OpenTerm
recordOpenTerm flds_ts =
  OpenTerm $ do let (flds,ots) = unzip flds_ts
                ts <- mapM unOpenTerm ots
                typeInferComplete $ RecordValue $ zip flds ts

-- | Build a record type as an 'OpenTerm'
recordTypeOpenTerm :: [(FieldName, OpenTerm)] -> OpenTerm
recordTypeOpenTerm flds_ts =
  OpenTerm $ do let (flds,ots) = unzip flds_ts
                ts <- mapM unOpenTerm ots
                typeInferComplete $ RecordType $ zip flds ts

-- | Project a field from a record
projRecordOpenTerm :: OpenTerm -> FieldName -> OpenTerm
projRecordOpenTerm (OpenTerm m) f =
  OpenTerm $ do t <- m
                typeInferComplete $ RecordProj t f

-- | Build an 'OpenTerm' for a constructor applied to its arguments
ctorOpenTerm :: Ident -> [OpenTerm] -> OpenTerm
ctorOpenTerm c all_args = OpenTerm $ do
  maybe_ctor <- liftTCM scFindCtor c
  ctor <- case maybe_ctor of
            Just ctor -> pure ctor
            Nothing -> throwTCError $ NoSuchCtor c
  (params, args) <- splitAt (ctorNumParams ctor) <$> mapM unOpenTerm all_args
  c' <- traverse typeInferComplete (ctorPrimName ctor)
  typeInferComplete $ CtorApp c' params args

-- | Build an 'OpenTerm' for a datatype applied to its arguments
dataTypeOpenTerm :: Ident -> [OpenTerm] -> OpenTerm
dataTypeOpenTerm d all_args = OpenTerm $ do
  maybe_dt <- liftTCM scFindDataType d
  dt <- case maybe_dt of
          Just dt -> pure dt
          Nothing -> throwTCError $ NoSuchDataType d
  (params, args) <- splitAt (dtNumParams dt) <$> mapM unOpenTerm all_args
  d' <- traverse typeInferComplete (dtPrimName dt)
  typeInferComplete $ DataTypeApp d' params args

-- | Build an 'OpenTerm' for a global name with a definition
globalOpenTerm :: Ident -> OpenTerm
globalOpenTerm ident =
  OpenTerm (do trm <- liftTCM scGlobalDef ident
               tp <- liftTCM scTypeOfGlobal ident
               return $ TypedTerm trm tp)

-- | Build an 'OpenTerm' for an 'Ident', which can either refer to a definition,
-- a constructor, or a datatype
identOpenTerm :: Ident -> OpenTerm
identOpenTerm ident =
  OpenTerm $
  do maybe_ctor <- liftTCM scFindCtor ident
     maybe_dt <- liftTCM scFindDataType ident

     -- First, determine the variables we need to abstract over and the function
     -- for building an application of this identifier dependent on the class of
     -- identifier
     let (var_ctx, app_fun) =
           case (maybe_ctor, maybe_dt) of
             (Just ctor, _) -> (fst (asPiList (ctorType ctor)), scCtorApp)
             (_, Just dt) -> (dtParams dt ++ dtIndices dt, scDataTypeApp)
             (Nothing, Nothing) -> ([], scGlobalApply)

     -- Build the term \ (x1:tp1) ... (xn:tpn) -> ident x1 ... xn as follows:
     -- 1. Construct vars as the list x1 ... xn of terms, noting that xn has
     --    deBruijn index 0 and x1 has deBruijn index (length var_ctx) - 1;
     -- 2. Apply ident to those variables; and
     -- 3. Lambda-abstract the variables.
     vars <- reverse <$> mapM (liftTCM scLocalVar) [0 .. (length var_ctx) - 1]
     ident_app <- liftTCM app_fun ident vars
     lam <- liftTCM scLambdaList var_ctx ident_app
     typeInferComplete lam

-- | Build an 'OpenTerm' for an external constant
extCnsOpenTerm :: ExtCns Term -> OpenTerm
extCnsOpenTerm ec = OpenTerm (liftTCM scExtCns ec >>= typeInferComplete)

-- | Apply an 'OpenTerm' to another
applyOpenTerm :: OpenTerm -> OpenTerm -> OpenTerm
applyOpenTerm (OpenTerm f) (OpenTerm arg) =
  OpenTerm ((App <$> f <*> arg) >>= typeInferComplete)

-- | Apply an 'OpenTerm' to 0 or more arguments
applyOpenTermMulti :: OpenTerm -> [OpenTerm] -> OpenTerm
applyOpenTermMulti = foldl applyOpenTerm

-- | Apply a named global to 0 or more arguments
applyGlobalOpenTerm :: Ident -> [OpenTerm] -> OpenTerm
applyGlobalOpenTerm ident = applyOpenTermMulti (globalOpenTerm ident)

-- | Compute the output type of applying a function of a given type to an
-- argument. That is, given @tp@ and @arg@, compute the type of applying any @f@
-- of type @tp@ to @arg@.
applyPiOpenTerm :: OpenTerm -> OpenTerm -> OpenTerm
applyPiOpenTerm (OpenTerm m_f) (OpenTerm m_arg) =
  OpenTerm $
  do f <- m_f
     arg <- m_arg
     ret <- applyPiTyped (NotFuncTypeInApp f arg) (typedVal f) arg
     ctx <- askCtx
     ret_tp <- liftTCM scTypeOf' (map snd ctx) ret
     return (TypedTerm ret ret_tp)

-- | Get the argument type of a function type, 'fail'ing if the input term is
-- not a function type
piArgOpenTerm :: OpenTerm -> OpenTerm
piArgOpenTerm (OpenTerm m) =
  OpenTerm $ m >>= \case
  (unwrapTermF . typedVal -> Pi _ tp _) -> typeInferComplete tp
  t ->
    do ctx <- askCtx
       fail ("piArgOpenTerm: not a pi type: " ++
             scPrettyTermInCtx defaultPPOpts (map fst ctx) (typedVal t))

-- | Build an 'OpenTerm' for the top variable in the current context, by
-- building the 'TCM' computation which checks how much longer the context has
-- gotten since the variable was created and uses this to compute its deBruijn
-- index
openTermTopVar :: TCM OpenTerm
openTermTopVar =
  do outer_ctx <- askCtx
     return $ OpenTerm $ do
       inner_ctx <- askCtx
       typeInferComplete (LocalVar (length inner_ctx
                                    - length outer_ctx) :: TermF Term)

-- | Build an open term inside a binder of a variable with the given name and
-- type, where the binder is represented as a Haskell function on 'OpenTerm's
bindOpenTerm :: LocalName -> TypedTerm -> (OpenTerm -> OpenTerm) -> TCM TypedTerm
bindOpenTerm x tp body_f =
  do tp_whnf <- typeCheckWHNF $ typedVal tp
     withVar x tp_whnf (openTermTopVar >>= (unOpenTerm . body_f))

-- | Build a lambda abstraction as an 'OpenTerm'
lambdaOpenTerm :: LocalName -> OpenTerm -> (OpenTerm -> OpenTerm) -> OpenTerm
lambdaOpenTerm x (OpenTerm tpM) body_f = OpenTerm $
  do tp <- tpM
     body <- bindOpenTerm x tp body_f
     typeInferComplete $ Lambda x tp body

-- | Build a nested sequence of lambda abstractions as an 'OpenTerm'
lambdaOpenTermMulti :: [(LocalName, OpenTerm)] -> ([OpenTerm] -> OpenTerm) ->
                       OpenTerm
lambdaOpenTermMulti xs_tps body_f =
  foldr (\(x,tp) rest_f xs ->
          lambdaOpenTerm x tp (rest_f . (:xs))) (body_f . reverse) xs_tps []

-- | Build a Pi abstraction as an 'OpenTerm'
piOpenTerm :: LocalName -> OpenTerm -> (OpenTerm -> OpenTerm) -> OpenTerm
piOpenTerm x (OpenTerm tpM) body_f = OpenTerm $
  do tp <- tpM
     body <- bindOpenTerm x tp body_f
     typeInferComplete $ Pi x tp body

-- | Build a non-dependent function type.
arrowOpenTerm :: LocalName -> OpenTerm -> OpenTerm -> OpenTerm
arrowOpenTerm x tp body = piOpenTerm x tp (const body)

-- | Build a nested sequence of Pi abstractions as an 'OpenTerm'
piOpenTermMulti :: [(LocalName, OpenTerm)] -> ([OpenTerm] -> OpenTerm) ->
                       OpenTerm
piOpenTermMulti xs_tps body_f =
  foldr (\(x,tp) rest_f xs ->
          piOpenTerm x tp (rest_f . (:xs))) (body_f . reverse) xs_tps []

-- | Build a let expression as an 'OpenTerm'. This is equivalent to
-- > 'applyOpenTerm' ('lambdaOpenTerm' x tp body) rhs
letOpenTerm :: LocalName -> OpenTerm -> OpenTerm -> (OpenTerm -> OpenTerm) ->
               OpenTerm
letOpenTerm x tp rhs body_f = applyOpenTerm (lambdaOpenTerm x tp body_f) rhs

-- | Build a let expression as an 'OpenTerm'. This is equivalent to
-- > 'applyOpenTerm' ('lambdaOpenTerm' x tp body) rhs
sawLetOpenTerm :: LocalName -> OpenTerm -> OpenTerm -> OpenTerm ->
                  (OpenTerm -> OpenTerm) -> OpenTerm
sawLetOpenTerm x tp tp_ret rhs body_f =
  applyOpenTermMulti (globalOpenTerm "Prelude.sawLet")
  [tp, tp_ret, rhs, lambdaOpenTerm x tp body_f]

-- | Build an 'OpenTerm' of type @List1 tp@ from 'OpenTerm's of type @tp@
list1OpenTerm :: OpenTerm -> [OpenTerm] -> OpenTerm
list1OpenTerm tp xs =
  foldr (\hd tl -> ctorOpenTerm "Prelude.Cons1" [tp, hd, tl])
  (ctorOpenTerm "Prelude.Nil1" [tp])
  xs

-- | The monad for building 'OpenTerm's if you want to add in 'IO' actions. This
-- is just the type-checking monad, but we give it a new name to keep this
-- module self-contained.
newtype OpenTermM a = OpenTermM { unOpenTermM :: TCM a }
                    deriving (Functor, Applicative, Monad)

instance MonadIO OpenTermM where
  liftIO = OpenTermM . liftIO

-- | "Complete" an 'OpenTerm' build in 'OpenTermM' to a closed term, or 'fail'
-- on a type-checking error
completeOpenTermM :: SharedContext -> OpenTermM OpenTerm -> IO Term
completeOpenTermM sc (OpenTermM termM) =
  either (fail . show) return =<<
  runTCM (typedVal <$> join (fmap unOpenTerm termM)) sc Nothing []

-- | "De-duplicate" an open term, so that duplicating the returned 'OpenTerm'
-- does not lead to duplicated WHNF work
dedupOpenTermM :: OpenTerm -> OpenTermM OpenTerm
dedupOpenTermM (OpenTerm trmM) =
  OpenTermM $ do trm <- trmM
                 return $ OpenTerm $ return trm

-- | Build an open term inside a binder of a variable with the given name and
-- type, where the binder is represented as a monadic Haskell function on
-- 'OpenTerm's that also returns an auxiliary value. Returns the normalized type
-- and the body, along with the auxiliary result returned by the body-generating
-- function.
bindOpenTermAuxM ::
  LocalName -> OpenTerm ->
  (OpenTerm -> OpenTermM (OpenTerm, a)) ->
  OpenTermM (TypedTerm, TypedTerm, a)
bindOpenTermAuxM x (OpenTerm tpM) body_f =
  OpenTermM $
  do TypedTerm tp tp_tp <- tpM
     tp_whnf <- typeCheckWHNF tp
     (OpenTerm bodyM, a) <-
       withVar x tp_whnf (openTermTopVar >>= (unOpenTermM . body_f))
     body <- bodyM
     return (TypedTerm tp_whnf tp_tp, body, a)

-- | Build a lambda abstraction in the 'OpenTermM' monad
lambdaOpenTermM ::
  LocalName -> OpenTerm -> (OpenTerm -> OpenTermM OpenTerm) ->
  OpenTermM OpenTerm
lambdaOpenTermM x tp body_f =
  fst <$> lambdaOpenTermAuxM x tp (body_f >=> (\t -> return (t, ())))

-- | Build a pi abstraction in the 'OpenTermM' monad
piOpenTermM ::
  LocalName -> OpenTerm -> (OpenTerm -> OpenTermM OpenTerm) ->
  OpenTermM OpenTerm
piOpenTermM x tp body_f =
  fst <$> piOpenTermAuxM x tp (body_f >=> (\t -> return (t, ())))

-- | Build a lambda abstraction with an auxiliary return value in the
-- 'OpenTermM' monad
lambdaOpenTermAuxM ::
  LocalName -> OpenTerm ->
  (OpenTerm -> OpenTermM (OpenTerm, a)) ->
  OpenTermM (OpenTerm, a)
lambdaOpenTermAuxM x tp body_f =
  do (tp', body, a) <- bindOpenTermAuxM x tp body_f
     return (OpenTerm (typeInferComplete $ Lambda x tp' body), a)

-- | Build a pi abstraction with an auxiliary return value in the 'OpenTermM'
-- monad
piOpenTermAuxM ::
  LocalName -> OpenTerm -> (OpenTerm -> OpenTermM (OpenTerm, a)) ->
  OpenTermM (OpenTerm, a)
piOpenTermAuxM x tp body_f =
  do (tp', body, a) <- bindOpenTermAuxM x tp body_f
     return (OpenTerm (typeInferComplete $ Pi x tp' body), a)


--------------------------------------------------------------------------------
-- sawLet-minimization

-- | A map from each deBruijn index to a count of its occurrences in a term
newtype VarOccs = VarOccs [Integer]

-- | Make a 'VarOccs' with a single occurrence of a deBruijn index
varOccs1 :: DeBruijnIndex -> VarOccs
varOccs1 i = VarOccs (take i (repeat 0) ++ [1])

-- | Move a 'VarOccs' out of a binder by returning the number of occurrences of
-- deBruijn index 0 along with the result of subtracting 1 from all other indices
unconsVarOccs :: VarOccs -> (Integer, VarOccs)
unconsVarOccs (VarOccs []) = (0, VarOccs [])
unconsVarOccs (VarOccs (cnt:occs)) = (cnt, VarOccs occs)

-- | Multiply every index in a 'VarOccs' by a constant
multVarOccs :: Integer -> VarOccs -> VarOccs
multVarOccs i (VarOccs occs) = VarOccs $ map (* i) occs

-- | The infinite list of zeroes
zeroes :: [Integer]
zeroes = 0:zeroes

instance Semigroup VarOccs where
  (VarOccs occs1) <> (VarOccs occs2)
    | length occs1 < length occs2
    = VarOccs (zipWith (+) (occs1 ++ zeroes) occs2)
  (VarOccs occs1) <> (VarOccs occs2)
    = VarOccs (zipWith (+) occs1 (occs2 ++ zeroes))

instance Monoid VarOccs where
  mempty = VarOccs []

-- | 'listen' to the output of a writer computation and return that output but
-- drop it from the writer output of the computation
listenDrop :: MonadWriter w m => m a -> m (a, w)
listenDrop m = pass (listen m >>= \aw -> return (aw, const mempty))

-- | The monad for sawLet minimization
type SLMinM = StateT (IntMap (Term, VarOccs)) (WriterT VarOccs IO)

-- | Find every subterm of the form @sawLet a b rhs (\ x -> body)@ and, whenever
-- @x@ occurs at most once in @body@, unfold the @sawLet@ by substituting @rhs@
-- into @body@
sawLetMinimize :: SharedContext -> Term -> IO Term
sawLetMinimize sc t_top =
  fst <$> runWriterT (evalStateT (slMinTerm t_top) IntMap.empty) where
  slMinTerm :: Term -> SLMinM Term
  slMinTerm (Unshared tf) = slMinTermF tf
  slMinTerm t@(STApp { stAppIndex = i }) =
    do memo_table <- get
       case IntMap.lookup i memo_table of
         Just (t', occs) ->
           -- NOTE: the fact that we explicitly tell occs here means that we are
           -- going to double-count variable occurrences for multiple
           -- occurrences of the same subterm. That is, a variable occurence
           -- counts for each copy of a shared subterm.
           tell occs >> return t'
         Nothing ->
           do (t', occs) <- listen $ slMinTermF (unwrapTermF t)
              modify $ IntMap.insert i (t', occs)
              return t'

  slMinTermF :: TermF Term -> SLMinM Term
  slMinTermF tf@(App (asApplyAll ->
                      (isGlobalDef "Prelude.sawLet" -> Just _, [_a, _b, rhs]))
                 (asLambda -> Just (_, _, body))) =
    do (body', (unconsVarOccs ->
                (x_cnt, body_occs))) <- listenDrop $ slMinTerm body
       if x_cnt > 1 then slMinTermF' tf else
         do (rhs', rhs_occs) <- listenDrop $ slMinTerm rhs
            tell (multVarOccs x_cnt rhs_occs <> body_occs)
            liftIO $ instantiateVar sc 0 rhs' body'
  slMinTermF tf = slMinTermF' tf

  slMinTermF' :: TermF Term -> SLMinM Term
  slMinTermF' (FTermF ftf) = slMinFTermF ftf
  slMinTermF' (App f arg) =
    do f' <- slMinTerm f
       arg' <- slMinTerm arg
       liftIO $ scTermF sc (App f' arg')
  slMinTermF' (Lambda x tp body) =
    do tp' <- slMinTerm tp
       (body', body_occs) <- listenDrop $ slMinTerm body
       tell $ snd $ unconsVarOccs body_occs
       liftIO $ scTermF sc (Lambda x tp' body')
  slMinTermF' (Pi x tp body) =
    do tp' <- slMinTerm tp
       (body', body_occs) <- listenDrop $ slMinTerm body
       tell $ snd $ unconsVarOccs body_occs
       liftIO $ scTermF sc (Pi x tp' body')
  slMinTermF' tf@(LocalVar i) =
    tell (varOccs1 i) >> liftIO (scTermF sc tf)
  slMinTermF' tf@(Constant _ _) = liftIO (scTermF sc tf)

  slMinFTermF :: FlatTermF Term -> SLMinM Term
  slMinFTermF ftf@(ExtCns _) = liftIO $ scFlatTermF sc ftf
  slMinFTermF ftf = traverse slMinTerm ftf >>= liftIO . scFlatTermF sc
