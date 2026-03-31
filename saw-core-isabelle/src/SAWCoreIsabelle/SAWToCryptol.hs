{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ImplicitParams #-}

module SAWCoreIsabelle.CryptolSchema 
  ( translateAsExpr
  , termToSchemaExpr
  , runTT
  , TTEnv
  , TTError
  , initTTEnv
  , prettyTTError
  ) where


import           Control.Applicative
import           Control.Monad
import           Control.Monad.Except
import           Control.Monad.Reader

import           Data.Bimap (Bimap)
import qualified Data.Bimap as Bimap
import qualified Data.ByteString as BS
import qualified Data.List.NonEmpty as NE
import qualified Data.Map as Map
import           Data.Maybe (mapMaybe)
import           Data.Text (Text)
import qualified Data.Text as Text

import qualified Cryptol.Parser.AST as P
import qualified Cryptol.ModuleSystem.Name as C
import qualified Cryptol.Parser.Position as Pos
import qualified Cryptol.Utils.Ident as C
import qualified Cryptol.TypeCheck.AST as C

import qualified SAWCore.Name as SAW
import           SAWCore.Recognizer
import           SAWCore.SharedTerm
import           SAWCore.Term.Functor
import qualified SAWSupport.Pretty as PPS

import qualified CryptolSAWCore.CryptolEnv as CrySAW
import qualified CryptolSAWCore.Cryptol as CrySAW
import           CryptolSAWCore.CryptolEnv (CryptolEnv)

import qualified Prettyprinter as PP

envToConstToPName :: CryptolEnv -> SAW.Name -> Maybe P.PName
envToConstToPName cenv = 
  let 
    go (cnm,t) = case asConstant t of
      Just snm -> Just (snm,C.nameToDefPName cnm)
      Nothing -> Nothing
    rev_env = Map.fromList $ mapMaybe go (Map.toList (CrySAW.eTermEnv cenv))
  in \snm -> Map.lookup snm rev_env

termToExpr :: CryptolEnv -> Term -> Either TTError (P.Expr P.PName)
termToExpr env t = runTT (initTTEnv $ envToConstToPName env) $
    translateAsExpr t

checkConvertible :: SharedContext -> Term -> Term -> IO ()
checkConvertible sc t1 t2 = scConvertible sc t1 t2 >>= \case
  True -> return ()
  False -> do
    t1' <- prettyTerm sc PPS.defaultOpts t1
    t2' <- prettyTerm sc PPS.defaultOpts t2
    fail $ "Not convertible:\n" ++ show t1' ++ "\nvs.\n" ++ show t2'

-- | Attempt to convert a SAWCore term into an equivalent Cryptol expression and corresponding
--   schema. Only intended for Terms that are the result of importing a Cryptol expression, in order
--   to recover the original expression if it is not available.
termToSchemaExpr :: 
 SharedContext -> CryptolEnv -> Term -> IO (C.Schema, C.Expr)
termToSchemaExpr sc env t = let ?fileReader = BS.readFile in
  case termToExpr env t of
    Left er -> do
      msg <- prettyTTError sc PPS.defaultOpts er
      fail (show msg)
    Right d -> do
      ((s,e),env') <- CrySAW.inferExpr env d
      cryenv <- CrySAW.mkCryEnv env'
      s' <- CrySAW.importSchema sc cryenv s
      e' <- CrySAW.importExpr sc cryenv e
      tT <- scTypeOf sc t
      checkConvertible sc s' tT
      checkConvertible sc e' t
      return (s,e)


type Name = P.PName
type TParam = P.TParam Name
type Type = P.Type Name
type Expr = P.Expr Name
type Prop = P.Prop Name

data CryptolVarK = CryTParam TParam | CryParam Name Type | CryConstraint Prop

data CryptolVar = CryptolVar 
 { _varIndexSaw :: VarIndex, _varKind :: CryptolVarK }


data TTEnv = TTEnv 
 { ttEnvVars :: Bimap VarIndex Text -- ^ bijection between SAW variables and unqualified (fresh) names
 , ttConstName :: SAW.Name -> Maybe P.PName -- ^ how to generate a parsed Cryptol constant name from a SAW constant
 }


initTTEnv :: (SAW.Name -> Maybe P.PName) -> TTEnv
initTTEnv = TTEnv Bimap.empty

data TTError = TTError { _ttErrMsg :: String, ttErrContext :: [Term] }

prettyTTError :: SharedContext -> PPS.Opts -> TTError -> IO PPS.Doc
prettyTTError sc opts (TTError msg ts) | Just ts' <- NE.nonEmpty ts = do
  prettyFirst <- prettyTerm sc opts (NE.head ts')
  case length ts > 1 of
    True -> do
      prettyLast <- prettyTerm sc opts (NE.last ts')
      return $ PP.vcat
        [ "Translation to Cryptol failed for term:"
        , PP.indent 2 prettyFirst
        , "in subterm:"
        , PP.indent 2 prettyLast
        , PP.pretty msg
        ]
    False -> do
      return $ PP.vcat
        [ "Translation to Cryptol failed for term:"
        , PP.indent 2 prettyFirst
        , PP.pretty msg
        ]
prettyTTError _ _ (TTError msg _) = 
  return $ PP.pretty $ "Translation to Cryptol failed: " ++ show msg


bindPName :: VarIndex -> Text -> TTEnv -> TTEnv
bindPName idx pname env = 
  env { ttEnvVars = Bimap.insert idx pname (ttEnvVars env) }

lookupVarName :: VarIndex -> TT P.PName
lookupVarName idx = do
  m <- asks ttEnvVars
  txt <- mreturn $ Bimap.lookup idx m
  return $ P.UnQual' (C.mkIdent txt) C.SystemName


constToPName :: SAW.Name -> TT P.PName
constToPName nm = do
  f <- asks ttConstName
  case f nm of
    Just a -> return a
    Nothing -> fail $ "No corresponding Cryptol name for SAW constant: " ++ Text.unpack (toAbsoluteName $ nameInfo nm)

builtinName :: Text -> P.PName
builtinName nm = P.Qual C.preludeName (C.mkIdent nm)

bindVarName :: SAW.VarName  -> TTEnv -> TTEnv
bindVarName vn env = go 0
  where 
    go :: Integer -> TTEnv
    go i =
      let pname = SAW.vnName vn <> Text.pack (show i)
      in case Bimap.lookupR pname (ttEnvVars env) of
        Just idx -> case idx == SAW.vnIndex vn of
          True -> env
          False -> go (i+1)
        Nothing -> bindPName (SAW.vnIndex vn) pname env

mreturn :: MonadPlus m => Maybe a -> m a
mreturn (Just a) = return a
mreturn Nothing = mzero

newtype TT a = TT { unTT :: ExceptT TTError (Reader TTEnv) a }
  deriving (Functor, Applicative, Monad, MonadReader TTEnv)

-- | Commit to an alternative by considering any uncaught errors thrown
--   by the sub-computation to be unrecoverable, attaching a
--   'Term' as context to the resulting error.
commit :: Term -> TT a -> TT a
commit t f = TT $ catchError (unTT f) $ \e -> 
  throwError (e {ttErrContext = t : ttErrContext e })

-- Alternative branches are implicit try-catches as long as the
-- thrown error is not committed (i.e. uncaught during a 'commit' action).
instance Alternative TT where
  empty = TT $ throwError $ TTError "no alternatives" []
  (TT f) <|> (TT g) = TT $ 
    catchError f $ \e -> case ttErrContext e of
      [] -> g
      _ -> throwError e

instance MonadPlus TT

instance MonadFail TT where
  fail msg = TT $ throwError $ TTError msg []

runTT :: TTEnv -> TT a -> Either TTError a
runTT env f = runReader (runExceptT (unTT f)) env

noLoc :: a -> Pos.Located a
noLoc = Pos.Located Pos.emptyRange

userT :: Name -> [Type] -> Type
userT nm ts = P.TUser (noLoc nm) ts

translateAsType :: Term -> TT Type
translateAsType t = msum 
  [ mreturn (asBoolType t) >> return P.TBit
  , mreturn (asIntegerType t) >> 
      (return $ userT (builtinName "Integer") [])
  , do [n,a] <- mreturn $ asGlobalApply "Cryptol.seq" t
       commit t $ do
         n' <- translateAsType n
         a' <- translateAsType a
         return $ P.TSeq n' a'
  , do [n] <- mreturn $ asGlobalApply "Cryptol.TCNum" t
       n' <- mreturn $ asNat n
       return $ P.TNum (fromIntegral n')
       -- TODO: nested function types cannot be dependent. This
       -- check catches the usual case where the bound variable is
       -- anonymous (named "_") but this can be improved.
  , do (vn, a, b) <- mreturn $ asPi t
       commit t $ do 
         "_" <- return $ SAW.vnName vn
         a' <- translateAsType a
         b' <- translateAsType b
         return $ P.TFun a' b'
  , do (vn, tT) <- mreturn $ asVariable t
       _ <- translateAsKind tT
       commit t $ do
        nm <- lookupVarName (SAW.vnIndex vn)
        return $ userT nm []
  ]

translateAsTypeApp :: Ident -> Term -> TT [Type]
translateAsTypeApp i t = do
  tps <- mreturn $ asGlobalApply i t
  mapM translateAsType tps

translateAsConstraint :: Term -> TT Prop
translateAsConstraint t = msum 
  [ tc "Cryptol.PLogic" (C.mkIdent "Logic")
  , tc "Cryptol.PZero" (C.mkIdent "Zero")
  , tc "Cryptol.PEq" (C.mkIdent "Eq")
  , tc "Cryptol.tcFin" (C.mkIdent "fin")
  , tc "Cryptol.tcEqual" (C.mkInfix "==")
  ]
  where
    tc d pc = do
      tps <- translateAsTypeApp d t
      return $ P.CType $ userT (P.Qual C.preludeName pc) tps

translateAsKind :: Term -> TT P.Kind
translateAsKind t = msum
  [ mreturn $ isGlobalDef "Cryptol.Num" t >> return P.KNum
  , do (TypeSort 0) <- mreturn $ asSort t
       return P.KType
  ]


termType :: Term -> TT Term
termType t = case termSortOrType t of
  Left s -> fail $ "termType: unexpected sort: " ++ show s
  Right tT -> return tT

translateApp :: [Term] -> TT ([Type],[Expr])
translateApp [] = return ([],[])
translateApp (arg:args) = do
  (argTs,argEs) <- translateApp args
  msum
    [ do arg' <- translateAsType arg
         return (arg':argTs,argEs)
    , do arg' <- translateAsExpr arg
         return (argTs,arg':argEs)
    , do argT <- termType arg
         _ <- translateAsConstraint argT
         return (argTs, argEs)
    ]

eApps :: P.Expr n -> [P.Expr n] -> P.Expr n
eApps e [] = e
eApps e (arg:args) = eApps (P.EApp e arg) args

translateAsExpr :: Term -> TT Expr
translateAsExpr t = msum
  [ do (fn, args@(_:_)) <- return $ asApplyAll t
       fn' <- translateAsExpr fn
       commit t $ do
         (argTs,argEs) <- translateApp args
         return $ eApps (P.EAppT fn' (map P.PosInst argTs)) argEs
  , do (vars@(_:_), fn) <- return $ asLambdaList t
       commit t $ do
         withVars vars $ \vs -> do
          let asParam = \case
                CryptolVar _ (CryParam nm tp) -> 
                  Just $ P.PTyped (P.PVar (noLoc nm)) tp
                _ -> Nothing
          let vars' = mapMaybe asParam vs
          fn' <- translateAsExpr fn
          return $ P.EFun P.emptyFunDesc vars' fn'
  , do (vn,tT) <- mreturn $ asVariable t
       tT' <- translateAsType tT
       commit t $ do
         nm <- lookupVarName (SAW.vnIndex vn)
         return $ P.ETyped (P.EVar nm) tT'
  , do nm <- mreturn $ asConstant t
       commit t $ do
         pname <- constToPName nm
         return $ P.EVar pname
  , do n <- mreturn $ asNat t
       return $ P.ELit $ P.ECNum (fromIntegral n) (P.DecLit $ Text.pack $ show n)
  ]

withVars :: [(SAW.VarName, Term)] -> ([CryptolVar] -> TT a) -> TT a
withVars [] f = f []
withVars ((vn,t):vs) f = withVar vn t $ \p -> withVars vs $ \ps ->
  f (p:ps)

withVar :: SAW.VarName -> Term -> (CryptolVar -> TT a) -> TT a
withVar vn t f = msum 
  [ do c <- translateAsConstraint t
       commit t $ f (CryptolVar (SAW.vnIndex vn) (CryConstraint c))
  , do t' <- translateAsType t
       commit t $ local (bindVarName vn) $ do
          nm <- lookupVarName (SAW.vnIndex vn)
          f $ CryptolVar (SAW.vnIndex vn) (CryParam nm t')
  , do tk <- translateAsKind t
       commit t $ local (bindVarName vn) $ do
          nm <- lookupVarName (SAW.vnIndex vn)
          let tp = P.TParam nm (Just tk) Nothing
          f $ CryptolVar (SAW.vnIndex vn) (CryTParam tp)
  ]