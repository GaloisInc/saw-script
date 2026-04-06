{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ImplicitParams #-}

{-
Provides a (very) partial mapping from SAWCore terms back to Cryptol expressions.
-}

module CryptolSAWCore.SAWCoreCryptol
  ( termToSchemaExpr
  , termToExpr
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
import           Data.Map (Map)
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
import           Cryptol.TypeCheck.PP (pp)

import Cryptol.ModuleSystem.Env (lookupModule, lmInterface)
import Cryptol.ModuleSystem.Interface (ifacePrimMap)

revMap :: (Ord k, Ord u) => (v -> Maybe u) -> Map k v -> Map u k
revMap f m = 
  let 
    go (cnm,t) = case f t of
      Just snm -> Just (snm,cnm)
      Nothing -> Nothing
  in Map.fromList $ mapMaybe go (Map.toList m)


extraPrims :: C.PrimMap -> [(SAW.Ident, C.Name)]
extraPrims pm = map go
  [ ("Prelude.Integer", "Integer")
  , ("Prelude.Bool", "Bit")
  , ("Cryptol.PIntegral", "Integral")
  , ("Cryptol.PLiteral", "Literal")
  , ("Cryptol.PEq", "Eq")
  ]
  where
    go (x,txt) = (x, C.lookupPrimType (C.prelPrim txt) pm)

initTTEnv :: CryptolEnv -> C.PrimMap -> TTEnv
initTTEnv env pmap = TTEnv 
  { ttEnvVars = Bimap.empty
  , ttConstMap = Map.unions [revMap asConstant (CrySAW.eTermEnv env), exprPrims, typePrims]
  , ttExtras = Map.fromList (extraPrims pmap)
  }
  where
    exprPrims = fmap (\x -> C.lookupPrimDecl x pmap) $ revMap asConstant (CrySAW.ePrims env)
    typePrims = fmap (\x -> C.lookupPrimType x pmap) $ revMap asConstant (CrySAW.ePrimTypes env)

termToExpr :: CryptolEnv -> C.PrimMap -> Term -> Either TTError (P.Expr P.PName)
termToExpr env prims t = 
  runTT (initTTEnv env prims) $ translateAsExpr t

checkConvertible :: SharedContext -> Term -> Term -> IO (Maybe TTError)
checkConvertible sc t1 t2 = scConvertible sc t1 t2 >>= \case
  True -> return Nothing
  False -> do
    t1' <- prettyTerm sc PPS.defaultOpts t1
    t2' <- prettyTerm sc PPS.defaultOpts t2
    return $ Just $ (TTError ("Not convertible:\n" ++ show t1' ++ "\nvs.\n" ++ show t2') [] True)

prettySawName :: SAW.Name -> String
prettySawName nm = Text.unpack (SAW.toAbsoluteName $ SAW.nameInfo nm)

revTopProofs :: C.Expr -> C.Expr
revTopProofs = go []
  where
    unwind prfs e = case prfs of
      x:xs -> C.EProofAbs x (unwind xs e)
      [] -> e
    go prfs = \case
      C.ETAbs tp e -> C.ETAbs tp (go prfs e)
      C.ELocated loc e -> C.ELocated loc (go prfs e)
      C.EProofAbs prf e -> go (prf:prfs) e
      e -> unwind prfs e

-- | SAW reverses the guards when importing expressions, so we need to reverse the
--   result after type inference in order to recover the original type/term
revGuards :: (C.Schema, C.Expr) -> (C.Schema, C.Expr)
revGuards (s,e) = (s { C.sProps = reverse (C.sProps s)}, revTopProofs e)

-- | Attempt to convert a SAWCore term into an equivalent Cryptol expression and corresponding
--   schema. Only expected to work for terms that are the immediate result of importing a Cryptol
--   expression, or a simple transformation of one.
termToSchemaExpr :: 
 SharedContext -> CryptolEnv -> Term -> IO (Either TTError (C.Schema, C.Expr))
termToSchemaExpr sc env t = let ?fileReader = BS.readFile in
  do
    let menv = CrySAW.eModuleEnv env
    Just prel <- return $ lookupModule C.preludeName menv
    let prims = ifacePrimMap $ lmInterface prel
    case termToExpr env prims t of
      Left er -> return $ Left er
      Right d -> do
        (r,env') <- CrySAW.inferExpr env d
        let (s,e) = revGuards r
        cryenv <- CrySAW.mkCryEnv env'
        s' <- CrySAW.importSchema sc cryenv s
        e' <- CrySAW.importExpr sc cryenv e
        tT <- scTypeOf sc t
        checkConvertible sc s' tT >>= \case
          Just er -> return $ Left er
          Nothing -> 
            checkConvertible sc e' t >>= \case
              Just er -> return $ Left er
              Nothing -> return $ Right (s,e)

type Name = P.PName
type TParam = P.TParam Name
type Type = P.Type Name
type Expr = P.Expr Name
type Prop = P.Prop Name

data CryptolVar = CryTParam TParam | CryParam Name Type | CryConstraint Prop

data TTEnv = TTEnv 
 { ttEnvVars :: Bimap VarIndex Text -- ^ bijection between SAW variables and unqualified (fresh) names
 , ttConstMap :: Map SAW.Name C.Name -- ^ map from SAW constants back to Cryptol
 , ttExtras :: Map Ident C.Name -- ^ map from SAW identifiers back to Cryptol
 }

data CallContext = CallContext { ctxMsg :: String, ctxtContent :: SharedContext -> PPS.Opts -> IO PPS.Doc }

prettyContext :: SharedContext -> PPS.Opts -> CallContext -> IO PPS.Doc
prettyContext sc opts ctx | debug = do
  doc <- ctxtContent ctx sc opts
  return $ PP.vcat $ [PP.pretty (ctxMsg ctx) PP.<> ": ", PP.indent 2 doc]
prettyContext sc opts ctx = ctxtContent ctx sc opts

data TTError = TTError { _ttErrMsg :: String, ttErrContext :: [CallContext], ttErrCommitted :: Bool }

debug :: Bool
debug = True

prettyTTError :: SharedContext -> PPS.Opts -> TTError -> IO PPS.Doc
prettyTTError sc opts (TTError msg ts _) | debug = do
  docs <- mapM (prettyContext sc opts) ts
  return $ PP.vcat $ [ "Translation to Cryptol failed: ", PP.pretty msg ] ++ docs
prettyTTError sc opts (TTError msg ts _) | Just ts' <- NE.nonEmpty ts = do
  prettyFirst <- prettyContext sc opts (NE.head ts')
  case length ts > 1 of
    True -> do
      prettyLast <- prettyContext sc opts (NE.last ts')
      return $ PP.vcat
        [ "Translation to Cryptol failed for term:"
        , PP.indent 2 prettyFirst
        , "in subterm:"
        , PP.indent 2 prettyLast
        , PP.pretty msg
        ]
    False -> do
      return $ PP.vcat $
        [ "Translation to Cryptol failed for term:"
        , PP.indent 2 prettyFirst
        , PP.pretty msg
        ]
prettyTTError _ _ (TTError msg _ _) = return $ PP.vcat
  [ "Translation to Cryptol failed: ", PP.pretty msg  ]

bindPName :: VarIndex -> Text -> TTEnv -> TTEnv
bindPName idx pname env = 
  env { ttEnvVars = Bimap.insert idx pname (ttEnvVars env) }

lookupVarName :: VarIndex -> TT P.PName
lookupVarName idx = do
  m <- asks ttEnvVars
  case Bimap.lookup idx m of
    Just txt -> return $ P.UnQual' (C.mkIdent txt) C.SystemName
    Nothing -> fail $ "lookupVarName: could not find variable: " ++ show idx

constToName :: SAW.Name -> TT C.Name
constToName nm = do
  m <- asks ttConstMap
  mT <- asks ttExtras
  msum 
    [ mreturn $ Map.lookup nm m
    , do SAW.ModuleIdentifier ident <- return $ SAW.nameInfo nm
         mreturn $ Map.lookup ident mT
    , fail $ "No corresponding Cryptol name for SAW constant: " ++ 
        Text.unpack (SAW.toAbsoluteName $ SAW.nameInfo nm)
    ]

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
mreturn Nothing = empty

newtype TT a = TT { unTT :: ExceptT TTError (Reader TTEnv) a }
  deriving (Functor, Applicative, Monad, MonadReader TTEnv, MonadError TTError)

-- | Commit to an alternative by considering any uncaught errors thrown
--   by the sub-computation to be unrecoverable.
commit :: TT a -> TT a
commit = withError (\e -> (e {ttErrCommitted = True}))

withContext :: CallContext -> TT a -> TT a
withContext ctx = withError (\e -> (e {ttErrContext = ctx : ttErrContext e}))

withTermContext :: String -> Term -> TT a -> TT a
withTermContext msg t = withContext $ CallContext msg (\sc opts -> prettyTerm sc opts t)

withNameContext :: String -> SAW.Name -> TT a -> TT a
withNameContext msg nm = withContext $ CallContext msg (\_ _ -> return $ PP.pretty $ prettySawName nm)

-- Alternative branches are implicit try-catches as long as the
-- thrown error is not committed (i.e. uncaught during a 'commit' action).
instance Alternative TT where
  empty = fail ""
  f <|> g =
    catchError f $ \e -> case ttErrCommitted e of
      False -> catchError g $ \e2 -> case e2 of 
        TTError "" [] False -> throwError e
        _ -> throwError e2
      True -> throwError e 

instance MonadPlus TT

instance MonadFail TT where
  fail msg = throwError $ TTError msg [] False

alts :: String -> Term -> [TT a] -> TT a
alts msg t ttfs = withContext (CallContext msg (\sc opts -> prettyTerm sc opts t)) $ msum ttfs

runTT :: TTEnv -> TT a -> Either TTError a
runTT env f = runReader (runExceptT (unTT f)) env

noLoc :: a -> Pos.Located a
noLoc = Pos.Located Pos.emptyRange

userT :: Name -> [Type] -> Type
userT nm ts = P.TUser (noLoc nm) ts

translateAsType :: Term -> TT Type
translateAsType t = alts "translateAsType" t
  [ do [n,a] <- mreturn $ asGlobalApply "Cryptol.seq" t
       commit $ do
         n' <- translateAsType n
         a' <- translateAsType a
         return $ P.TSeq n' a'
  , do [n] <- mreturn $ asGlobalApply "Cryptol.TCNum" t
       n' <- mreturn $ asNat n
       return $ P.TNum (fromIntegral n')
       -- NOTE: this will intentionally fail if 'b' depends on 'a'
  , do (_, a, b) <- mreturn $ asPi t
       b' <- translateAsType b
       commit $ do
        a' <- translateAsType a
        return $ P.TFun a' b'
  , do (vn, tT) <- mreturn $ asVariable t
       _ <- translateAsKind tT
       commit $ do
        nm <- lookupVarName (SAW.vnIndex vn)
        return $ userT nm []
  , do (tc, nm, ts) <- translateAsTCon t
       case tc of
         C.TC _ -> return ()
         C.TF _ -> return ()
         _ -> fail $ "Unexpected type constructor: " ++ (show $ pp tc)
       commit $ do
         ts' <- mapM translateAsType ts
         return $ userT nm ts'
  ]

nameToTCon :: SAW.Name -> TT (C.TCon, Name)
nameToTCon nm = withNameContext "nameToTCon" nm $ msum
  [ do nm' <- constToName nm
       tc <- mreturn $ C.builtInType nm'
       return $ (tc, C.nameToDefPName nm')
  , fail $ "Could not find Cryptol type for: " ++ prettySawName nm
  ]

translateAsTCon :: Term -> TT (C.TCon, Name, [Term])
translateAsTCon t = do
  let (f, ts) = asApplyAll t
  nm <- mreturn $ asConstant f
  (tc, pnm) <- nameToTCon nm
  return $ (tc, pnm, ts)

translateAsConstraint :: Term -> TT Prop
translateAsConstraint t = withTermContext "translateAsConstraint" t $ do
  (C.PC _ , nm, ts) <- translateAsTCon t
  commit $ do
    ts' <- mapM translateAsType ts
    return $ P.CType $ userT nm ts'

translateAsKind :: Term -> TT P.Kind
translateAsKind t = alts "translateAsKind" t
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
  alts "translateApp" arg
    [ do argT <- termType arg
         _ <- translateAsConstraint argT
         return (argTs, argEs)
    , do arg' <- translateAsExpr arg
         return (argTs,arg':argEs)
    , do arg' <- translateAsType arg
         return (arg':argTs,argEs)
    ]

eApps :: P.Expr n -> [P.Expr n] -> P.Expr n
eApps e [] = e
eApps e (arg:args) = eApps (P.EApp e arg) args

isValueName :: C.Name -> Bool
isValueName nm = case C.nameNamespace nm of
  C.NSValue -> True
  C.NSConstructor -> True
  _ -> False

translateAsExpr :: Term -> TT Expr
translateAsExpr t = alts "translateAsExpr" t
  [ do (fn, args@(_:_)) <- return $ asApplyAll t
       fn' <- translateAsExpr fn
       commit $ do
         (argTs,argEs) <- translateApp args
         return $ eApps (P.EAppT fn' (map P.PosInst argTs)) argEs
  , do (vars@(_:_), fn) <- return $ asLambdaList t
       withVars vars $ \vs -> do
          let asParam = \case
                CryParam nm tp -> 
                  Just $ P.PTyped (P.PVar (noLoc nm)) tp
                _ -> Nothing
          let vars' = mapMaybe asParam vs
          fn' <- translateAsExpr fn
          return $ P.EFun P.emptyFunDesc vars' fn'
  , do (vn,tT) <- mreturn $ asVariable t
       tT' <- translateAsType tT
       commit $ do
         nm <- lookupVarName (SAW.vnIndex vn)
         return $ P.ETyped (P.EVar nm) tT'
  , do nm <- mreturn $ asConstant t
       nm' <- constToName nm
       True <- return $ isValueName nm'
       return $ P.EVar (C.nameToDefPName nm')
  ]

withVars :: [(SAW.VarName, Term)] -> ([CryptolVar] -> TT a) -> TT a
withVars [] f = f []
withVars ((vn,t):vs) f = withVar vn t $ \p -> withVars vs $ \ps ->
  f (p:ps)

withVar :: SAW.VarName -> Term -> (CryptolVar -> TT a) -> TT a
withVar vn t f = alts "withVar"  t
  [ do t' <- translateAsType t
       commit $ local (bindVarName vn) $ do
          nm <- lookupVarName (SAW.vnIndex vn)
          f $ (CryParam nm t')
  , do c <- translateAsConstraint t
       commit $ f (CryConstraint c)
  , do tk <- translateAsKind t
       commit $ local (bindVarName vn) $ do
          nm <- lookupVarName (SAW.vnIndex vn)
          let tp = P.TParam nm (Just tk) Nothing
          f $ (CryTParam tp)
  ]