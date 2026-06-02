{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-
Provides a (very) partial mapping from SAWCore terms back to Cryptol expressions.
-}

module CryptolSAWCore.SAWCoreCryptol
  ( termToSchemaExpr
  , propToSchemaExpr
  , prettyTTError
  , termToPExpr
  ) where

import           Control.Applicative
import           Control.Exception (try, IOException)
import           Control.Monad
import           Control.Monad.Except 
                   ( MonadError, throwError, catchError, ExceptT, runExceptT
                   , handleError)
import           Control.Monad.Reader
import           Control.Monad.Writer

import           Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import           Data.IORef
import qualified Data.List.NonEmpty as NE
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Maybe (mapMaybe,catMaybes)
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Text (Text)
import qualified Data.Text as Text

import qualified Cryptol.Parser.AST as P
import qualified Cryptol.Parser.Position as P
import qualified Cryptol.ModuleSystem.Name as C
import qualified Cryptol.ModuleSystem.Names as C
import qualified Cryptol.ModuleSystem.NamingEnv as C
import qualified Cryptol.Parser.Position as Pos
import qualified Cryptol.Utils.Ident as C
import qualified Cryptol.TypeCheck.AST as C
import qualified Cryptol.Utils.RecordMap as C

import qualified SAWCore.Name as SAW
import           SAWCore.Recognizer
import           SAWCore.SharedTerm
import           SAWCore.Term.Functor
import qualified SAWCore.Term.Pretty as SAW

import qualified SAWSupport.Pretty as PPS

import qualified CryptolSAWCore.CryptolEnv as CrySAW
import qualified CryptolSAWCore.Cryptol as CrySAW
import           CryptolSAWCore.GlobalCryptolEnv (CryptolEnv)

import qualified Prettyprinter as PP
import           Cryptol.TypeCheck.PP (pp, pretty)


import Cryptol.ModuleSystem.Env (lookupModule, lmInterface)
import Cryptol.ModuleSystem.Interface (ifacePrimMap)




revMap :: (Ord k, Ord u) => (v -> Maybe u) -> Map k v -> Map u k
revMap f m = Map.fromList $ mapMaybe (\(k,v) -> (,k) <$> (f v)) (Map.toList m)

extraPrims :: C.PrimMap -> [(SAW.Ident, C.Name)]
extraPrims pm = map go
  [ -- types from Prelude.sawcore
      ("Prelude.Integer", "Integer")
    , ("Prelude.Bool", "Bit")
    -- types from Cryptol.sawcore 

    -- from CryptolSAWCore.Cryptol.importPC
    , ("Cryptol.PZero"            , "Zero")
    , ("Cryptol.PLogic"           , "Logic")
    , ("Cryptol.PRing"            , "Ring")
    , ("Cryptol.PIntegral"        , "Integral")
    , ("Cryptol.PField"           , "Field")
    , ("Cryptol.PRound"           , "Round")
    , ("Cryptol.PEq"              , "Eq")
    , ("Cryptol.PCmp"             , "Cmp")
    , ("Cryptol.PSignedCmp"       , "SignedCmp")
    , ("Cryptol.PLiteral"         , "Literal")
    , ("Cryptol.PLiteralLessThan" , "LiteralLessThan")
    , ("Cryptol.PFLiteral"        , "FLiteral")
    -- from CryptolSAWCore.Cryptol.importTFun
    , ("Cryptol.tcWidth"          , "width")
    , ("Cryptol.tcAdd"            , "+")          
    , ("Cryptol.tcSub"            , "-")
    , ("Cryptol.tcMul"            , "*")
    , ("Cryptol.tcDiv"            , "/")
    , ("Cryptol.tcMod"            , "%")
    , ("Cryptol.tcExp"            , "^^")
    , ("Cryptol.tcMin"            , "min")
    , ("Cryptol.tcMax"            , "max")
    , ("Cryptol.tcCeilDiv"        , "/^")
    , ("Cryptol.tcCeilMod"        , "%^")
    , ("Cryptol.tcLenFromThenTo"  , "lengthFromThenTo")
  ]
  where
    go (x,txt) = (x, C.lookupPrimType (C.prelPrim txt) pm)

initTTEnv :: SharedContext -> CryptolEnv -> IO TTEnv
initTTEnv sc env = do
  modEnv <- CrySAW.eModuleEnv sc
  case lookupModule C.preludeName modEnv of
    Just prelude -> do
      allPrims <- CrySAW.ePrims sc
      allPrimTypes <- CrySAW.ePrimTypes sc
      allTerms <- CrySAW.eAllTerms sc
      envVarsRef <- newIORef IntMap.empty
      usedNamesRef <- newIORef Set.empty
      eCacheRef <- newIORef IntMap.empty
      tCacheRef <- newIORef IntMap.empty
      let
        pmap = ifacePrimMap $ lmInterface prelude
        exprPrims = fmap (\x -> C.lookupPrimDecl x pmap) $ revMap asConstant allPrims
        typePrims = fmap (\x -> C.lookupPrimType x pmap) $ revMap asConstant allPrimTypes
        gvmap = IntMap.fromList $
          mapMaybe (\(nm,t) -> (\(vn,_) -> (SAW.vnIndex vn, nm)) <$> asVariable t)
          (Map.toList allTerms)
      nenv <- CrySAW.getCompleteNamingEnv sc env
      return $
        TTEnv
          { ttAllEnvVars = envVarsRef
          , ttEnvVars = IntMap.empty
          , ttUsedNames = usedNamesRef
          , ttConstMap = Map.unions [revMap asConstant allTerms, exprPrims, typePrims]
          , ttExtras = Map.fromList (extraPrims pmap)
          , ttCryEnv = env
          , ttSc = sc
          , ttGlobalNamingEnv = nenv
          , ttGlobalVarMap = gvmap
          , ttBoundExprs = IntMap.empty
          , ttExprCache = eCacheRef
          , ttTypeCache = tCacheRef
          }
    Nothing -> fail "initTTEnv: missing Cryptol prelude"

checkConvertible :: Term -> Term -> TT ()
checkConvertible t1 t2 = do
  sc <- asks ttSc
  (liftIO $ scConvertible sc t1 t2) >>= \case
    True -> return ()
    False -> do
      let ppts = do
            t1' <- liftIO $ prettyTerm sc t1
            t2' <- liftIO $ prettyTerm sc t2
            return $ PP.vcat [t1', PP.indent 2 "vs.",t2']
      withContext (CallContext  "checkConvertible" ppts) $ 
        errMsg "Terms are not convertible"

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

-- | SAW sometimes reverses the guards when importing expressions, in which case we need to reverse the
--   result after type inference in order to recover the original type/term
revGuards :: (Expr, C.Expr, C.Schema) -> (Expr, C.Expr, C.Schema)
revGuards (pe, e,s) = (pe, revTopProofs e, s { C.sProps = reverse (C.sProps s)})

validateImport :: Term -> (Expr, C.Expr, C.Schema) -> TT (Expr, C.Expr, C.Schema)
validateImport t (pe, e, s) = do
  sc <- asks ttSc
  s' <- liftIO $ CrySAW.importSchema sc s
  e' <- liftIO $ CrySAW.importExpr sc e
  tT <- liftIO $ scTypeOf sc t
  checkConvertible tT s'
  checkConvertible e' t
  return (pe,e,s)


inferSchemaExpr :: Term -> TT (Expr, C.Expr, C.Schema)
inferSchemaExpr t = do
  sc <- asks ttSc
  (pe,ttout) <- listen $ translateAsExprShared t
  (res,_) <- liftIO $ CrySAW.inferExpr sc (ttNamingEnv ttout) pe
  case res of
    Left e -> errMsg (pretty e)
    Right (expr,schema) -> do
      let r = (pe,expr,schema)
      -- the order of the guards is somewhat inconsistent, so we try
      -- either the original or reverse orderings and return the one that validates
      -- in most cases the reversed order seems to be preferred
      validateImport t (revGuards r) <|> validateImport t r

-- | Attempt to convert a SAWCore term into an equivalent Cryptol expression and corresponding
--   schema. Validates that the resulting type-checked expression and schema will
--   re-produce the given term if imported.
termToSchemaExpr ::
 SharedContext -> CryptolEnv -> Term -> IO (Either TTError (Expr, C.Expr, C.Schema))
termToSchemaExpr sc cenv t = do
  env <- initTTEnv sc cenv
  runTT env $ inferSchemaExpr t

-- | Attempt to convert a SAWCore term into an untyped Cryptol expression.
--   Does not validate that the result will correctly translate back into
--   the given term.
termToPExpr :: 
  SharedContext -> CryptolEnv -> Term -> IO (Either TTError Expr)
termToPExpr sc cenv t = do
  env <- initTTEnv sc cenv
  runTT env $ translateAsExpr t

lookupName :: C.Name -> TT Term
lookupName cnm = do
  sc <- asks ttSc
  allTerms <- liftIO $ CrySAW.eAllTerms sc
  mreturn $ Map.lookup cnm allTerms

lookupPrim :: Text -> TT Term
lookupPrim nm = do
  sc <- asks ttSc
  modEnv <- liftIO $ CrySAW.eModuleEnv sc
  prelude <- mreturn $ lookupModule C.preludeName modEnv
  let pmap = ifacePrimMap $ lmInterface prelude
  let pnm = C.prelPrim nm
  cnm <- mreturn $ Map.lookup pnm (C.primDecls pmap)
  lookupName cnm

propToLambda :: Term -> TT Term
propToLambda t = withTermContext "propToLambda" t $ go t
  where
    go :: Term -> TT Term
    go e = case asPi e of
      Just (vn, tp, body) -> do
        sc <- asks ttSc
        case asEqTrue tp of
          Just tp' -> do
            body' <- go body
            imp <- lookupPrim "==>"
            liftIO $ scApplyAll sc imp [tp',body']
          Nothing -> do
            body' <- go body
            liftIO $ scLambda sc vn tp body'
      Nothing -> case asEqTrue e of
        Just e' -> return e'
        Nothing -> errMsg "Unexpected term shape"

-- | Attempt to convert a SAWCore proposition into an equivalent Cryptol predicate and corresponding
--   schema. Validates that the resulting type-checked expression and schema will
--   re-produce the given term if imported.
propToSchemaExpr :: SharedContext -> CryptolEnv -> Term -> IO (Either TTError (Expr, C.Expr, C.Schema))
propToSchemaExpr sc cenv t = do
  env <- initTTEnv sc cenv
  runTT env $ propToLambda t >>= inferSchemaExpr

type Name = P.PName
type Type = P.Type Name
type Expr = P.Expr Name
type Prop = P.Prop Name

data CryptolVar = CryTParam Name | CryParam Name


data TTEnv = TTEnv 
 { ttAllEnvVars :: IORef (IntMap Name)
     -- ^ global map from SAW VarIndex to Cryptol variable names
 , ttEnvVars :: IntMap CryptolVar
     -- ^ map from SAW VarIndex to CryptolVar (distinguishes type and value vars)
 , ttUsedNames :: IORef (Set Name)
     -- ^ all generated Cryptol names (codomain of ttAllEnvVars)
 , ttConstMap :: Map SAW.Name C.Name
     -- ^ map from SAW constants back to Cryptol
 , ttExtras :: Map Ident C.Name
     -- ^ map from SAW identifiers back to Cryptol
 , ttCryEnv :: CryptolEnv
 , ttSc :: SharedContext
 , ttGlobalNamingEnv :: C.NamingEnv 
     -- ^ global naming environment, used to check for name clashes
 , ttGlobalVarMap :: IntMap C.Name
     -- ^ map from global SAW variables (i.e. "invented" variables) back to Cryptol, and
     --   the SAW type of the variable
 , ttBoundExprs :: IntMap Name
     -- ^ map from terms to corresponding let-bound variables
 , ttExprCache :: IORef (IntMap (CachedResult Expr))
     -- ^ cached results (including failed attempts) for 'translateAsExpr'
 , ttTypeCache :: IORef (IntMap (CachedResult Type))
     -- ^ cached results (including failed attempts) for 'translateAsType'
 }

type CachedResult a = Either TTError (a, TTOut)

data CallContext = CallContext { ctxMsg :: String, ctxtContent :: IO PPS.Doc }

prettyContext :: CallContext -> IO PPS.Doc
prettyContext ctx | debug = do
  doc <- ctxtContent ctx
  return $ PP.vcat $ [PP.pretty (ctxMsg ctx) PP.<> ": ", PP.indent 2 doc]
prettyContext ctx = ctxtContent ctx

data TTError = TTError { _ttErrMsg :: String, ttErrContext :: [CallContext], ttErrCommitted :: Bool }

debug :: Bool
debug = False

prettyTTError :: TTError -> IO PPS.Doc
prettyTTError (TTError msg ts _) | debug = do
  docs <- mapM prettyContext ts
  return $ PP.vcat $ [ "Translation to Cryptol failed: ", PP.pretty msg ] ++ docs
prettyTTError (TTError msg ts _) | Just ts' <- NE.nonEmpty ts = do
  prettyFirst <- prettyContext (NE.head ts')
  case length ts > 1 of
    True -> do
      prettyLast <- prettyContext (NE.last ts')
      return $ PP.vcat
        [ "Translation to Cryptol failed:"
        , PP.pretty msg PP.<> ":"
        , PP.indent 2 prettyFirst
        , "in subterm:"
        , PP.indent 2 prettyLast
        ]
    False -> do
      return $ PP.vcat $
        [ "Translation to Cryptol failed:"
        , PP.pretty msg PP.<> ":"
        , PP.indent 2 prettyFirst
        ]
prettyTTError (TTError msg _ _) = return $ PP.vcat
  [ "Translation to Cryptol failed: ", PP.pretty msg  ]

bindVar :: VarIndex -> CryptolVar -> TTEnv -> TTEnv
bindVar idx cv env = 
  env { ttEnvVars = IntMap.insert idx cv (ttEnvVars env) }

lookupVar :: VarIndex -> TT CryptolVar
lookupVar idx = do
  m <- asks ttEnvVars
  case IntMap.lookup idx m of
    Just cv -> return cv
    Nothing -> do
      g <- asks ttGlobalVarMap
      case IntMap.lookup idx g of
        Just nm -> do
          nm' <- uncheckName nm
          case isValueName nm of
            True -> return $ CryParam nm'
            False -> return $ CryTParam nm'
        Nothing -> errMsg $ "lookupVarName: could not find variable: " ++ show idx

constToName :: SAW.Name -> TT C.Name
constToName nm = do
  m <- asks ttConstMap
  mT <- asks ttExtras
  msum 
    [ mreturn $ Map.lookup nm m
    , do SAW.ModuleIdentifier ident <- return $ SAW.nameInfo nm
         mreturn $ Map.lookup ident mT
    , errMsg $ "No corresponding Cryptol name for SAW constant: " ++
        Text.unpack (SAW.toAbsoluteName $ SAW.nameInfo nm)
    ]

mkFreshName :: Text -> TT Name
mkFreshName txt = go 0
  where
    go :: Integer -> TT Name
    go i = do
      let 
        txt' = if i == 0 then txt else (txt <> Text.pack (show i))
        nm = P.UnQual' (C.mkIdent txt') C.SystemName
        nm' = P.UnQual' (C.mkIdent txt') C.UserName
      m <- deref ttUsedNames
      ne <- asks ttGlobalNamingEnv
      case Set.member nm m of
        False | 
           Nothing <- C.lookupNS C.NSValue nm ne
         , Nothing <- C.lookupNS C.NSValue nm' ne
         , Nothing <- C.lookupNS C.NSType nm ne
         , Nothing <- C.lookupNS C.NSType nm' ne
         -> do
          usedNamesRef <- asks ttUsedNames
          liftIO $ modifyIORef' usedNamesRef (Set.insert nm)
          return nm
        _ -> go (i+1)

deref :: (TTEnv -> IORef a) -> TT a
deref f = do
  ref <- asks f
  liftIO $ readIORef ref

mkVarName :: SAW.VarName -> TT Name
mkVarName vn = do
  envVarsRef <- asks ttAllEnvVars
  envVars <- liftIO $ readIORef envVarsRef
  case IntMap.lookup (SAW.vnIndex vn) envVars of
    Just nm -> return nm
    Nothing -> do
      nm <- mkFreshName (SAW.vnName vn)
      liftIO $ modifyIORef' envVarsRef $
        IntMap.insert (SAW.vnIndex vn) nm
      return nm

withFreshVar :: SAW.VarName -> TT a -> TT a
withFreshVar vn f = do
  nm <- mkVarName vn
  local (bindVar (SAW.vnIndex vn) (CryParam nm)) f

withFreshTVar :: SAW.VarName -> TT a -> TT a
withFreshTVar vn f = do
  nm <- mkVarName vn
  local (bindVar (SAW.vnIndex vn) (CryTParam nm)) f

mreturn :: MonadPlus m => Maybe a -> m a
mreturn (Just a) = return a
mreturn Nothing = empty

newtype TTOut = TTOut { ttNamingEnv :: C.NamingEnv }
  deriving (Semigroup,Monoid)

newtype TT a = TT { unTT :: ExceptT TTError (WriterT TTOut (ReaderT TTEnv IO)) a }
  deriving (Functor, Applicative, Monad, MonadReader TTEnv, MonadError TTError, MonadWriter TTOut )

addName :: Name -> C.Name -> TT ()
addName pnm nm = 
  tell $ TTOut (C.singletonNS (C.nameNamespace nm) pnm nm)

instance MonadIO TT where
  liftIO f = do
    mres <- TT $ liftIO (try f)
    case mres of
      Left (e :: IOException) -> throwError $ TTError (show e) [] True
      Right a -> return a

-- Copied from Control.Monad.Error base 2.3
withError :: MonadError e m => (e -> e) -> m a -> m a
withError f = handleError (throwError . f)

tryError :: MonadError e m => m a -> m (Either e a)
tryError f = (Right <$> f) `catchError` (pure . Left)

-- | Commit to an alternative by considering any uncaught errors thrown
--   by the sub-computation to be unrecoverable.
commit :: TT a -> TT a
commit = withError (\e -> (e {ttErrCommitted = True}))

-- | Ignore committed errors in the sub-computation
uncommit :: TT a -> TT a
uncommit = withError (\e -> (e {ttErrCommitted = False}))

withContext :: CallContext -> TT a -> TT a
withContext ctx f = withError (\e -> (e {ttErrContext = ctx  : ttErrContext e})) f

withTermContext :: String -> Term -> TT a -> TT a
withTermContext msg t f = do
  sc <- asks ttSc
  withContext (CallContext msg (prettyTerm sc t)) f

withNameContext :: String -> SAW.Name -> TT a -> TT a
withNameContext msg nm = withContext $ CallContext msg (return $ PP.pretty $ prettySawName nm)

-- Alternative branches are implicit try-catches as long as the
-- thrown error is not committed (i.e. uncaught during a 'commit' action).
instance Alternative TT where
  empty = throwError $ TTError "" [] False
  f <|> g =
    catchError f $ \e -> case ttErrCommitted e of
      -- re-throw any committed errors from 'f', as they are considered non-recoverable
      True -> throwError e
      -- otherwise, attempt the alternative 'g'
      False -> catchError g $ \e2 -> case e2 of
        -- if the second error is from "empty" (i.e. no more alternatives in an msum), then
        -- re-throw the original error, as it is likely to be more informative
        TTError "" [] False -> throwError e
        _ -> throwError e2

instance MonadPlus TT

instance MonadFail TT where
  fail _ = empty

-- | Use this instead of 'fail', which drops the error message.
errMsg :: String -> TT a
errMsg msg = throwError $ TTError msg [] False

alts :: String -> Term -> [TT a] -> TT a
alts msg t ttfs = withTermContext msg t $ msum ttfs

runTT :: TTEnv -> TT a -> IO (Either TTError a)
runTT env f = runReaderT (fst <$> runWriterT (runExceptT (unTT f))) env

noLoc :: a -> Pos.Located a
noLoc = Pos.Located Pos.emptyRange

userT :: Name -> [Type] -> Type
userT nm ts = P.TUser (noLoc nm) ts

translateCached ::
  (TTEnv -> IORef (IntMap (CachedResult a))) ->
  (Term -> TT a) ->
  Term ->
  TT a
translateCached getref f t = do
  ref <- asks getref
  ecached <- liftIO $ readIORef ref
  case IntMap.lookup (termIndex t) ecached of
    Just (Right (a,tout)) -> tell tout >> return a
    Just (Left err) -> throwError err
    Nothing -> do
      me <- tryError (listen $ f t)
      liftIO $ modifyIORef' ref (IntMap.insert (termIndex t) me)
      case me of
        Left err -> throwError err
        Right (a,tout) -> tell tout >> return a

translateAsType :: Term -> TT Type
translateAsType =
  translateCached ttTypeCache translateAsType'

translateAsType' :: Term -> TT Type
translateAsType' t = alts "translateAsType" t
  [ translateAsInfixTypeApp t
  , do [n,a] <- mreturn $ asGlobalApply "Cryptol.seq" t
       commit $ do
         n' <- translateAsType n
         a' <- translateAsType a
         return $ P.TSeq n' a'
  , do [n] <- mreturn $ asGlobalApply "Cryptol.TCNum" t
       n' <- mreturn $ (asNat n <|> asPos n)
       return $ P.TNum (fromIntegral n')
  , do mreturn $ asBoolType t
       return $ P.TBit
    -- NOTE: this will intentionally fail if 'b' depends on 'a'
  , do (_, a, b) <- mreturn $ asPi t
       b' <- translateAsType b
       commit $ do
        a' <- translateAsType a
        return $ P.TFun a' b'
  , do (vn, _) <- mreturn $ asVariable t
       CryTParam nm <- lookupVar (SAW.vnIndex vn)
       return $ userT nm []
  , do (n,a) <- mreturn $ asVectorType t
       n' <- translateAsType n
       commit $ do
        a' <- translateAsType a
        return $ P.TSeq n' a'
  , do n <- mreturn $ (asNat t <|> asPos t)
       let i = fromIntegral n
       return $ P.TNum i
  , do ts@(_:_) <- mreturn $ asTupleType t
       commit $ do
         ts' <- mapM translateAsType ts
         return $ P.TTuple ts'
  , do flds@(_:_) <- mreturn $ asRecordType t
       commit $ do
          flds' <- forM flds $ \(fld,fldT) -> do
            fldT' <- translateAsType fldT
            return (C.mkIdent fld,(P.emptyRange, fldT'))
          return $ P.TRecord $ C.recordFromFields flds'
  , do (tc, nm, ts) <- translateAsTCon t
       case tc of
         C.TC _ -> return ()
         C.TF _ -> return ()
         _ -> errMsg $ "Unexpected type constructor: " ++ (show $ pp tc)
       commit $ do
         ts' <- mapM translateAsType ts
         return $ userT nm ts'
  ]

nameToTCon :: SAW.Name -> TT (C.TCon, Name)
nameToTCon nm = withNameContext "nameToTCon" nm $ msum
  [ do nm' <- constToName nm
       tc <- mreturn $ C.builtInType nm'
       pnm <- uncheckName nm'
       return $ (tc, pnm)
  , errMsg $ "Could not find Cryptol type for: " ++ prettySawName nm
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
  , mreturn $ asNatType t >> return P.KNum
  , do (TypeSort 0) <- mreturn $ asSort t
       return P.KType
  ]

nameUses :: C.Namespace -> Name -> TT Int
nameUses ns pn = do
  ne <- asks ttGlobalNamingEnv
  case C.lookupNS ns pn ne of
    Just (C.One{}) -> return 1
    Just (C.Ambig s) -> return $ Set.size s
    Nothing -> return 0

nameAliases :: C.Namespace -> Name -> TT Int
nameAliases ns nm = case nm of
  P.UnQual' ident _ -> do
    i <- nameUses ns (P.UnQual' ident C.SystemName)
    j <- nameUses ns (P.UnQual' ident C.UserName)
    return $ (i + j)
  _ -> nameUses ns nm

uncheckName :: C.Name -> TT Name
uncheckName nm = do
  let checkAmbig pn = do
        i <- nameAliases (C.nameNamespace nm) pn
        if i > 1 then empty else return pn
  pnm <- msum
    [ checkAmbig (C.nameToDefPName nm)
    , checkAmbig (C.nameToPNameWithQualifiers nm)
    , do C.GlobalName _ og <- return $ C.nameInfo nm
         let mnm = C.topModuleFor $ C.ogModule og
         pnm <- case C.nameToPNameWithQualifiers nm of
           P.UnQual' i _ -> return $ P.mkQual mnm i
           P.Qual ps i -> 
             let mnm' = C.packModName $ C.modNameChunksText mnm ++ C.modNameChunksText ps
             in return $ P.mkQual mnm' i
           _ -> empty
         checkAmbig pnm
    , commit $ errMsg $ "Could not disambiguate name: " ++ show (pp nm)
    ]
  addName pnm nm
  return pnm

termType :: Term -> TT Term
termType t = case termSortOrType t of
  Left s -> errMsg $ "termType: unexpected sort: " ++ show s
  Right tT -> return tT

translateApp :: Bool -> [Term] -> TT ([Type],[Expr])
translateApp _ [] = return ([],[])
translateApp useType (arg:args) = do
  (argTs,argEs) <- translateApp useType args
  alts "translateApp" arg
    [ do argT <- termType arg
         _ <- translateAsConstraint argT
         return (argTs, argEs)
    , do arg' <- if useType 
           then translateAsTypedExpr arg 
           else translateAsExpr arg
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

shouldMemoizeExpr :: Expr -> Bool
shouldMemoizeExpr = \case
  P.ETyped e _ -> shouldMemoizeExpr e
  P.ELocated e _ -> shouldMemoizeExpr e
  P.ELit{} -> False
  P.EVar{} -> False
  P.EParens e -> shouldMemoizeExpr e
  P.ETypeVal{} -> False
  _ -> True

withShared1 :: Term -> (Maybe (Name,Expr) -> TT a) -> TT a
withShared1 t f = do
  m <- asks ttBoundExprs
  case IntMap.member (termIndex t) m of
    True -> f Nothing
    False -> tryError (translateAsExpr t) >>= \case
      Right e | shouldMemoizeExpr e -> do
        nm <- mkFreshName "x"
        local (\env -> env 
          { ttBoundExprs = IntMap.insert (termIndex t) nm (ttBoundExprs env) 
          }) $ f (Just (nm,e))
      _ -> f Nothing

mkBind :: Name -> Expr -> P.Bind Name
mkBind nm e = P.Bind
  { P.bName = noLoc nm
  , P.bParams = P.noParams
  , P.bDef = noLoc (P.DImpl (P.DExpr e))
  , P.bSignature = Nothing
  , P.bInfix = False
  , P.bFixity = Nothing
  , P.bPragmas = []
  , P.bMono = True
  , P.bDoc = Nothing
  , P.bExport = P.Private
  }

-- | First extract any shared subterms (at this binding level) and generate
--   where-bindings. Then translate with the fresh bindings in scope, where
--   the bound name will be used in place of the shared term during
--   translation.
translateAsExprShared :: Term -> TT Expr
translateAsExprShared t = do
  let shared = map fst $ IntMap.elems $ 
        IntMap.filter (\(t',cnt) -> cnt >= 2 && SAW.shouldMemoizeTerm t') $
        SAW.scTermCount False t
  go shared []
  where
    go :: [Term] -> [(Name,Expr)] -> TT Expr
    go [] [] = translateAsExpr t
    go [] acc = do
      e <- translateAsExpr t
      return $ P.EWhere e $ map (\(nm,e') -> P.DBind $ mkBind nm e') acc
    go (t':ts) acc = withShared1 t' $ \case
      Nothing -> go ts acc
      Just (nm,e) -> go ts ((nm,e):acc)

translateLambda :: [(SAW.VarName, Term)] -> Term -> TT Expr
translateLambda vars fn = withVars vars $ do
  let asParam (vn,tT) =
        (do CryParam nm <- lookupVar (SAW.vnIndex vn)
            tT' <- translateAsType tT
            return $ Just $ P.PTyped (P.PVar (noLoc nm)) tT')
        <|> return Nothing
  vars' <- catMaybes <$> mapM asParam vars
  fn' <- translateAsExprShared fn
  case vars' of
    [] -> return fn'
    _ -> return $ P.EFun P.emptyFunDesc vars' fn'

lookupSAWConst :: Ident -> TT SAW.Name
lookupSAWConst i = do
  sc <- asks ttSc
  t <- liftIO $ scGlobalDef sc i
  mreturn $ asConstant t

asInfixExprOp :: Term -> TT (Name, C.Fixity)
asInfixExprOp t = alts "asInfixExprOp" t
  [ do nm <- mreturn $ asConstant t
       nm' <- constToName nm
       True <- return $ isValueName nm'
       fx <- mreturn $ C.nameFixity nm'
       pnm <- uncheckName nm'
       return (pnm, fx)
  , do mreturn $ isGlobalDef "Prelude.bvslt" t
       nm <- constToName =<< lookupSAWConst "Cryptol.ecSLt"
       fx <- mreturn $ C.nameFixity nm
       pnm <- uncheckName nm
       return (pnm, fx)
  ]

asInfixTypeOp :: Term -> TT (Name, C.Fixity)
asInfixTypeOp t = alts "asInfixTypeOp" t
  [ do nm <- mreturn $ asConstant t
       nm' <- constToName nm
       False <- return $ isValueName nm'
       fx <- mreturn $ C.nameFixity nm'
       pnm <- uncheckName nm'
       return (pnm, fx)
  , do mreturn $ isGlobalDef "Prelude.addNat" t
       nm <- constToName =<< lookupSAWConst "Cryptol.tcAdd"
       fx <- mreturn $ C.nameFixity nm
       pnm <- uncheckName nm
       return (pnm, fx)
  ]

-- Add type parentheses if needed to make presentation
-- unambiguous
tParens :: Type -> Type
tParens t = case t of
  P.TInfix{} -> P.TParens t Nothing
  P.TFun{} -> P.TParens t Nothing
  P.TLocated t' rng -> P.TLocated (tParens t') rng
  _ -> t

translateAsInfixTypeApp :: Term -> TT Type
translateAsInfixTypeApp t = do
  (fn, args@(_:_)) <- return $ asApplyAll t
  ([t1,t2],[]) <- translateApp False args
  (nm, fx) <- asInfixTypeOp fn
  tT <- termType t
  _ <- translateAsKind tT
  return $ P.TInfix (tParens t1) (noLoc nm) fx (tParens t2)

-- Add expr parentheses if needed to make presentation
-- unambiguous
eParens :: Expr -> Expr
eParens e = case e of
  P.EInfix{} -> pe
  P.EPrefix{} -> pe
  P.ELocated e' rng -> P.ELocated (eParens e') rng
  P.EIf{} -> pe
  P.EApp{} -> pe
  P.ECase{} -> pe
  P.ETyped{} -> pe
  P.EFun{} -> pe
  _ -> e
  where
    pe = P.EParens e

eTyped :: Expr -> Type -> Expr
eTyped e t = case e of
  P.ETyped{} -> e
  P.EVar{} -> e
  _ -> P.ETyped e t

translateAsInfixExprApp :: Term -> TT Expr
translateAsInfixExprApp t = do
  (fn, args@(_:_)) <- return $ asApplyAll t
  (_,[e1,e2]) <- translateApp True args
  (nm, fx) <- asInfixExprOp fn
  let t' = P.EInfix (eParens e1) (noLoc nm) fx (eParens e2)
  tT <- termType t
  tT' <- translateAsType tT
  return $ eTyped t' tT'

translateAsTypedExpr :: Term -> TT Expr
translateAsTypedExpr t = do
  t' <- translateAsExpr t
  case t' of
    P.ETyped{} -> return t'
    P.EVar{} -> return t'
    _ -> do
      tT <- termType t
      tT' <- translateAsType tT
      return $ eTyped t' tT'

stripTyped :: Expr -> Expr
stripTyped = \case
  P.ETyped e _ -> stripTyped e
  e -> e

unNumber :: Expr -> TT Expr
unNumber e = case e of
  P.EAppT (P.EVar nm) [P.PosInst val, P.PosInst rep] -> do
    number <- (uncheckName =<< constToName =<< lookupSAWConst "Cryptol.ecNumber")
    case nm == number of
      True -> unNumber (eTyped (P.ETypeVal val) rep)
      False -> return e
  P.ETyped (P.ETypeVal (P.TNum n)) rep -> do
    let i = fromIntegral n
    return $ eTyped (P.ELit (P.ECNum i (P.DecLit (Text.pack $ show i)))) rep
  _ -> return e

translateLetBound :: Term -> TT Expr
translateLetBound t = do
  m <- asks ttBoundExprs
  nm <- mreturn $ IntMap.lookup (termIndex t) m
  return $ P.EVar nm

translateAsExpr :: Term -> TT Expr
translateAsExpr =
  translateCached ttExprCache translateAsExpr'

translateAsExpr' :: Term -> TT Expr
translateAsExpr' t = unNumber =<< alts "translateAsExpr" t
  [ translateLetBound t
  , do n' <- mreturn $ (asNat t <|> asPos t)
       let i = fromIntegral n'
       return $ P.ELit (P.ECNum i (P.DecLit (Text.pack $ show i)))
  , do (recv,fld) <- mreturn $ asRecordSelector t
       commit $ do
         recv' <- translateAsExpr recv
         return $ P.ESel recv' (P.RecordSel (C.mkIdent fld) Nothing)
  , do [n,x] <- mreturn $ asGlobalApply "Prelude.bvNat" t
       n' <- translateAsType n
       x' <- translateAsType x
       return $ eTyped (P.ETypeVal x') (P.TSeq n' P.TBit)
  , do (fn, _) <- return $ asApplyAll t
       mreturn $ isGlobalDef "Prelude.headRecord" fn
       commit $ do
         (t1,t2) <- mreturn $ asApp t
         t1' <- translateAsExpr t1
         alts "headRecord" t2 [
            do t2' <- translateAsExpr t2
               return $ P.EApp t1' t2'
          , do t2' <- translateAsType t2
               return $ P.EAppT t1' [P.PosInst t2']
          ]
  , translateAsInfixExprApp t
  , do (fn, args@(_:_)) <- return $ asApplyAll t
       fn' <- translateAsExpr fn
       commit $ do
         (argTs,argEs) <- translateApp False args
         return $ eApps (P.EAppT fn' (map P.PosInst argTs)) argEs
  , do (vars@(_:_), fn) <- return $ asLambdaList t
       commit $ translateLambda vars fn
  , do (vn,_) <- mreturn $ asVariable t
       CryParam nm <- lookupVar (SAW.vnIndex vn)
       return $ P.EVar nm
  , do (tT :*: p :*: caseTrue :*: caseFalse) <- mreturn $ asMux t
       _ <- translateAsType tT
       commit $ do 
        caseTrue' <- translateAsExpr caseTrue
        caseFalse' <- translateAsExpr caseFalse
        p' <- translateAsExpr p
        return $ P.EIf (stripTyped p') caseTrue' caseFalse'
  , do ts <- mreturn $ asTupleValue t
       commit $ do
         ts' <- mapM translateAsExpr ts
         return $ P.ETuple ts'
  , do (tup, i) <- mreturn $ asTupleSelector t
       commit $ do
        tup' <- translateAsExpr tup
        return $ P.ESel tup' (P.TupleSel i Nothing)
  , do flds <- mreturn $ asRecordValue t
       commit $ do
          flds' <- forM flds $ \(fld,fldE) -> do
            fldE' <- translateAsExpr fldE
            return (C.mkIdent fld,(P.emptyRange, fldE'))
          return $ P.ERecord $ C.recordFromFields flds'
  , do nm <- mreturn $ asConstant t
       nm' <- constToName nm
       True <- return $ isValueName nm'
       pnm <- uncheckName nm'
       return $ P.EVar pnm
  ]

withVars :: [(SAW.VarName, Term)] -> TT a -> TT a
withVars [] f = f
withVars ((vn,t):vs) f = withVar vn t $ withVars vs $ f

withVar :: SAW.VarName -> Term -> TT a -> TT a
withVar vn t f = alts "withVar"  t
  [ do _ <- translateAsType t
       uncommitNat $ withFreshVar vn f
  , do _ <- translateAsConstraint t
       commit $ f
  , do _ <- translateAsKind t
       uncommitNat $ withFreshTVar vn f
  ]
  where
    -- Nat can be treated as both a value and a type, so
    -- we may need to attempt both translations, ignoring
    -- otherwise unrecoverable errors
    uncommitNat :: TT a -> TT a
    uncommitNat g = case asNatType t of
      Just () -> uncommit g
      Nothing -> commit g
