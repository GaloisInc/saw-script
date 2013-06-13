{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}

-- TODO: generate correct deBruijn indices
-- TODO: translate inferred types to explicit type parameters
module SAWScript.ToSAWCore
  ( {-translateModule
  , -}translateExprShared
  , translateExprMeta
  )
  where

import Control.Applicative
import Control.Monad.Error
import Control.Monad.Identity
import Control.Monad.Reader
import qualified Data.Foldable as F
import Data.List
import qualified Data.Map as M
import Data.Map (Map)
import Data.Maybe
import qualified Data.Vector as V
import Data.Traversable hiding ( mapM )

import qualified SAWScript.AST as SS
import SAWScript.Unify.Fix
import qualified Verifier.SAW.TypedAST as SC
import qualified Verifier.SAW.SharedTerm as SC

data Env = Env {
    modules :: [SC.Module]
  , depth :: Int
  , locals :: Map SS.Name Int
  , globals :: [SC.Ident]
  , localTs :: Map SS.Name Int
  }

emptyEnv :: Env
emptyEnv =
  Env { modules = []
      , depth = 0
      , locals = M.empty
      , globals = []
      , localTs = M.empty
      }

incVars :: Map a Int -> Map a Int
incVars = M.map (+1)

addLocal :: Monad m => SS.Name -> MT m a -> MT m a
addLocal x =
  local (\env -> env { locals = M.insert x 0 (incVars (locals env))
                     , localTs = incVars (localTs env) })

addLocalType :: Monad m => SS.Name -> MT m a -> MT m a
addLocalType x =
  local (\env -> env { locals = incVars (locals env)
                     , localTs = M.insert x 0 (incVars (localTs env)) })

addLocalTypes :: Monad m => [SS.Name] -> MT m a -> MT m a
addLocalTypes [] m = m
addLocalTypes (x : xs) m = addLocalTypes xs (addLocalType x m)

newtype MT m a = M (ReaderT Env (ErrorT String m) a)
  deriving (Applicative, Functor, Monad, MonadError String, MonadReader Env, MonadIO)

type M = MT Identity
type M' = MT IO

runTranslate :: Env -> M a -> Either String a
runTranslate env (M a) = runIdentity . runErrorT . runReaderT a $ env

type Expression = SS.Expr SS.ResolvedName SS.Type

translateIdent :: SS.ModuleName -> SS.Name -> SC.Ident
translateIdent m n = SC.mkIdent (translateModuleName m) n

translateModuleName :: SS.ModuleName -> SC.ModuleName
translateModuleName (SS.ModuleName xs x) = SC.mkModuleName (xs ++ [x])

{-FIXME
translateModule :: [SC.Module] -> SS.Module' SS.PType SS.Type -> Either String SC.Module
translateModule ms m = runTranslate env $ translateModule' m
    where ssGlobs = mapMaybe getTopBindName (SS.declarations m)
          getTopBindName (SS.TopBind name _) =
            Just $ SC.mkIdent (SC.mkModuleName [SS.modName m]) name
          getTopBindName _ = Nothing
          scGlobs = map SC.defIdent . SC.moduleDefs
          globs = ssGlobs ++ concatMap scGlobs ms
          env = (emptyEnv { modules = ms, globals = globs })
-}

{-FIXME
translateModule' :: SS.Module' SS.PType SS.Type -> M SC.Module
translateModule' (SS.Module mname tss main) = do
  body' <- translateExpr (return . translateType) main
  let mainBody = SC.DefEqn [] body'
      modName = SC.mkModuleName [mname]
      mainName = SC.mkIdent modName "main"
      mainDef = SC.Def mainName mainTy [mainBody]
      mainTy = translateType (SS.typeOf main)
  flip SC.insDef mainDef <$> foldM insertTopStmt (SC.emptyModule modName) tss
-}

{-FIXME
-- We assume @env@ already includes any modules imported by @m@.
insertTopStmt :: SC.Module -> SS.TopStmt SS.PType -> M SC.Module
insertTopStmt m s = do
  env <- ask
  let ms =  modules env
  case s of
    SS.Import mname _ _ ->
      case find (\m' -> SC.moduleName m' == SC.mkModuleName [mname]) ms of
        Just m' -> return $ SC.insImport m' m
        Nothing -> fail $ "can't find module " ++ mname

    -- Type synonyms are erased by this point, so we don't try to
    -- translate them.
    SS.TypeDef name _ -> fail $ "unexpected type synonym: " ++ name

    -- Types from signatures get propagated during type checking, so
    -- they don't need to be inserted into the module. They'll be
    -- re-created based on the inferred type of the declaration, so we
    -- don't need to care whether an explicit signature existed or
    -- not.
    SS.TopTypeDecl _ _ -> return m

    -- TODO: for each binding, introduce a type signature based on its inferred type
    SS.TopBind name e -> do
      e' <- translateExpr translatePType e
      t <- translatePType (SS.typeOf e)
      let mname = SC.moduleName m
          i = SC.mkIdent mname name
          d = SC.DefEqn [] e'
      return $ SC.insDef m (SC.Def i t [d])
-}

translateBlockStmts :: (a -> M SC.Term) -> [SS.BlockStmt SS.ResolvedName a]
                    -> M (SC.Term, SC.Term) -- (term, type)
translateBlockStmts _ []  = fail "can't translate empty block"
translateBlockStmts doType [SS.Bind Nothing _ e] =
  (,) <$> translateExpr doType e <*> doType (SS.typeOf e)
translateBlockStmts _ [_] = fail "invalid block ending statement"
translateBlockStmts doType (SS.Bind mx _ e:ss) = do
  e' <- translateExpr doType e
  ty <- doType (SS.typeOf e)
  let x = fromMaybe "_" mx
  (k, kty) <- addLocal x $ translateBlockStmts doType ss
  let f = SC.Term $ SC.Lambda (SC.PVar x 0 ty) (tfun ty kty) k
  return (bind e' f, kty)
translateBlockStmts doType (SS.BlockTypeDecl _ _:ss) =
  -- Type declarations are not translated directly. Any information
  -- they provide is taken from the annotations resulting from type
  -- checking.
  translateBlockStmts doType ss
translateBlockStmts doType (SS.BlockLet decls:ss) =
  fail "block-level let expressions not yet supported"
{-
  decls' <- mapM translateDecl decls
  return (SC.Term $ SC.Let decls' k, kty)
    where translateDecl (n, e) = do
            e' <- translateExpr doType e
            ty <- doType (SS.typeOf e)
            return $ SC.LocalFnDef n ty [SC.DefEqn [] e']
-}

translateExpr :: (a -> M SC.Term) -> SS.Expr SS.ResolvedName a -> M SC.Term
translateExpr doType e = go e
  where go (SS.Unit _) = return unitTerm
        go (SS.Bit True _) = return trueTerm
        go (SS.Bit False _) = return falseTerm
        go (SS.Quote _ _) = fail "string constants not yet translated"
        go (SS.Z i _) = return $ fterm $ SC.NatLit (fromIntegral i)
        go (SS.Array es ty) =
          fterm <$> (SC.ArrayValue <$> doType ty <*> (V.fromList <$> mapM go es))
        go (SS.Block ss _) = fst <$> translateBlockStmts doType ss
        go (SS.Tuple es _) = (fterm . SC.TupleValue) <$> mapM go es
        go (SS.Record flds _) =
          (fterm . SC.RecordValue . M.fromList) <$> mapM translateFld flds
            where translateFld (n, e') = (n,) <$> go e'
        go (SS.Index a ie ty) = do
          ne <- doType (SS.typeOf a)
          n'' <- case ne of
                   (vecSize -> Just n') -> return n'
                   _ -> fail "array size is not constant"
          aget n'' <$> doType ty <*> go a <*> go ie
        go (SS.Lookup re f _) =
          (fterm . flip SC.RecordSelector f) <$> go re
        go (SS.Var (SS.LocalName x) ty) = do
          ls <- locals <$> ask
          case M.lookup x ls of
            Just n -> (SC.Term . SC.LocalVar n) <$> doType ty
            Nothing -> fail $ "unbound variable: " ++ x
        go (SS.Var (SS.TopLevelName m x) ty) = do
          gs <- globals <$> ask
          let i = translateIdent m x
          if i `elem` gs
            then return . fterm . SC.GlobalDef $ i
            else fail $ "unknown global variable: " ++ show i
        go (SS.Function x ty body fty) = do
          pat <- SC.PVar x 0 <$> doType ty
          SC.Term <$> (SC.Lambda pat <$> doType fty <*> addLocal x (go body))
        go (SS.Application f arg ty) =
          -- TODO: include type parameters
          fterm <$> (SC.App <$> go f <*> go arg)
        go (SS.LetBlock decls body) = SC.Term <$> (SC.Let <$> decls' <*> go body)
          where decls' = mapM translateDecl decls
                translateDecl (n, de) = do
                  ty <- doType (SS.typeOf de)
                  e' <- go de
                  return $ SC.Def n ty [SC.DefEqn [] e']

-- | Toplevel SAWScript expressions may be polymorphic. Type
-- abstractions do not show up explicitly in the Expr datatype, but
-- they are represented in a top-level expression's type (using
-- TypAbs). If present, these must be translated into SAWCore as
-- explicit type abstractions.
translatePolyExprShared :: forall s. SC.SharedContext s -> (SS.Type -> M' (SC.SharedTerm s))
                        -> Expression -> M' (SC.SharedTerm s)
translatePolyExprShared sc doType expr =
    case SS.typeOf expr of
      SS.TypAbs ns _ -> do
        s0 <- liftIO $ SC.scSort sc (SC.mkSort 0)
        t <- addLocalTypes ns (translateExprShared sc doType expr)
        liftIO $ SC.scLambdaList sc [ (n, s0) | n <- ns ] t
      _ -> translateExprShared sc doType expr

-- | Directly builds an appropriately-typed SAWCore shared term.
translateExprShared :: forall s a. SC.SharedContext s -> (a -> M' (SC.SharedTerm s))
                    -> SS.Expr SS.ResolvedName a -> M' (SC.SharedTerm s)
translateExprShared sc doType = go
  where go :: SS.Expr SS.ResolvedName a -> M' (SC.SharedTerm s)
        go (SS.Unit _) = liftIO $ SC.scTuple sc []
        go (SS.Bit True _) = liftIO $ SC.scCtorApp sc (preludeIdent "True") []
        go (SS.Bit False _) = liftIO $ SC.scCtorApp sc (preludeIdent "False") []
        go (SS.Quote _ _) = fail "string constants not yet translated"
        go (SS.Z i _) = liftIO $ SC.scNat sc i
        go (SS.Array es ty) = do
          ty' <- doType ty
          es' <- mapM go es
          liftIO $ SC.scVector sc ty' es'
        go (SS.Block _ss _) = fail "block statements not supported"
        go (SS.Tuple es _) = traverse go es >>= (liftIO . SC.scTuple sc)
        go (SS.Record flds _) = traverse go (M.fromList flds) >>= (liftIO . SC.scMkRecord sc)
        go (SS.Index a ie _) = do
          ne <- doType (SS.typeOf a)
          (n, e) <- maybe (fail "not an array type") return (destVec ne)
          a' <- go a
          ie' <- go ie
          liftIO $ SC.scGet sc n e a' ie'
        go (SS.Lookup re f _) = do
          re' <- go re
          liftIO $ SC.scRecordSelect sc re' f
        go (SS.Var (SS.LocalName x) ty) = do
          ls <- locals <$> ask
          case M.lookup x ls of
            Just n -> (liftIO . SC.scLocalVar sc n) =<< doType ty
            Nothing -> fail $ "unbound variable: " ++ x
        go (SS.Var (SS.TopLevelName m x) ty) = do
          gs <- globals <$> ask
          let i = translateIdent m x
          if i `elem` gs
            then liftIO $ SC.scGlobalDef sc i
            else fail $ "unknown global variable: " ++ show i
        go (SS.Function x ty body _) = do
          ty' <- doType ty
          body' <- addLocal x (go body)
          liftIO $ SC.scLambda sc x ty' body'
        go (SS.Application f arg _) = do
          f' <- go f
          arg' <- go arg
          liftIO $ SC.scApply sc f' arg'
        go (SS.LetBlock _decls _body) = error "LetBlock unimplemented"
{-
        go (SS.LetBlock decls body) = SC.Term <$> (SC.Let <$> decls' <*> go body)
          where decls' = mapM translateDecl decls
                translateDecl (n, de) = do
                  ty <- doType (SS.typeOf de)
                  e' <- go de
                  return $ SC.Def n ty [SC.DefEqn [] e']
-}

-- | Returns a SAWCore term with (SAWCore) type "TopLevel Term". This
-- uses the SAWCore monadic operations from the SAWScriptPrelude
-- module. When executed, it should generate the same output as the
-- translateExprShared function does.
translateExprMeta :: forall a. (a -> M SC.Term) -> SS.Expr SS.ResolvedName a -> M SC.Term
translateExprMeta doType = go
  where go :: SS.Expr SS.ResolvedName a -> M SC.Term
        go (SS.Unit _) = return $ ssGlobalTerm "termUnit"
        go (SS.Bit True _) = return $ ssGlobalTerm "termTrue"
        go (SS.Bit False _) = return $ ssGlobalTerm "termFalse"
        go (SS.Quote _ _) = fail "string constants not yet translated"
        go (SS.Z i _) = return $ ssGlobalTerm "termNat" `app` natTerm i
        go (SS.Array es ty) = do
          let n = toInteger (length es)
          ty' <- doType ty
          es' <- mapM go es
          let topterm = ssGlobalTerm "TopLevel" `app` ssGlobalTerm "Term"
          return $ ssGlobalTerm "termVec'" `app` natTerm n `app` ty' `app` vecTerm topterm es'
        go (SS.Block _ss _) = fail "block statements not supported"
        go (SS.Tuple es _) = do
          let n = toInteger (length es)
          es' <- mapM go es
          let topterm = ssGlobalTerm "TopLevel" `app` ssGlobalTerm "Term"
          return $ ssGlobalTerm "termTuple'" `app` natTerm n `app` vecTerm topterm es'
        go (SS.Record flds _) = do
          let n = toInteger (length flds)
          let topterm = ssGlobalTerm "TopLevel" `app` ssGlobalTerm "Term"
          let fldT = tupleType [quoteType, topterm]
          let f (s, m) = fmap (\t -> tupleTerm [stringTerm s, t]) (go m)
          flds' <- traverse f flds
          return $ ssGlobalTerm "termRecord'" `app` natTerm n `app` vecTerm fldT flds'
{-
        go (SS.Index a ie _) = do
          ne <- doType (SS.typeOf a)
          (n, e) <- maybe (fail "not an array type") return (destVec ne)
          a' <- go a
          ie' <- go ie
          liftIO $ SC.scGet sc n e a' ie'
-}
        go (SS.Lookup re f _) = do
          re' <- go re
          return $ ssGlobalTerm "termSelect'" `app` re' `app` stringTerm f
        go (SS.Var (SS.LocalName x) ty) = do
          ls <- locals <$> ask
          case M.lookup x ls of
            Just n -> do
              ty' <- doType ty
              return $ ssGlobalTerm "termLocalVar'" `app` natTerm (toInteger n) `app` ty'
            Nothing -> fail $ "unbound variable: " ++ x
        go (SS.Var (SS.TopLevelName m x) ty) = do
          gs <- globals <$> ask
          let i = translateIdent m x
          if i `elem` gs
            then return $ ssGlobalTerm "termGlobal" `app` stringTerm (show i)
            else fail $ "unknown global variable: " ++ show i
        go (SS.Function x ty body _) = do
          ty' <- doType ty
          body' <- addLocal x (go body)
          return $ ssGlobalTerm "termLambda'" `app` stringTerm x `app` ty' `app` body'
        go (SS.Application f arg _) = do
          f' <- go f
          arg' <- go arg
          return $ ssGlobalTerm "termApp'" `app` f' `app` arg'
{-
        go (SS.LetBlock _decls _body) = error "LetBlock unimplemented"
        go (SS.LetBlock decls body) = SC.Term <$> (SC.Let <$> decls' <*> go body)
          where decls' = mapM translateDecl decls
                translateDecl (n, de) = do
                  ty <- doType (SS.typeOf de)
                  e' <- go de
                  return $ SC.Def n ty [SC.DefEqn [] e']
-}

--FIXME translatePType :: SS.PType -> M SC.Term
translatePType t = addParams ps <$> local polyEnv (translatePType' t)
    where ps = map unwrap $ getPolyTypes t
          unwrap (SS.PVar n) = n
          polyEnv env = env { locals = M.fromList (zip (reverse ps) [0..]) }
          addParams [] = id
          addParams (_:ns) =
            tfun (fterm (SC.Sort (SC.mkSort 0))) . addParams ns

--FIXME translatePType' :: SS.PType -> M SC.Term
translatePType' (In (Inl _)) = fail "polymorphic type is integer"
translatePType' (In (Inr (Inr (SS.PVar x)))) = do
  ls <- locals <$> ask
  case M.lookup x ls of
    Just n ->
      return . SC.Term . SC.LocalVar n $ fterm . SC.Sort . SC.mkSort $ 0
    Nothing -> fail $ "unbound type variable: " ++ x
translatePType' (In (Inr (Inl ty))) =
  case ty of
    SS.UnitF -> return unitType
    SS.BitF -> return bitType
    SS.ZF -> return intType
    SS.QuoteF -> return quoteType
    SS.ArrayF ety (In (Inl (SS.I n))) -> vec n <$> translatePType' ety
    SS.ArrayF _ _ -> fail "array dimension is not constant"
--FIXME    SS.BlockF ctx rty -> blockType ctx <$> translatePType' rty
    SS.TupleF tys ->
      (fterm . SC.TupleType) <$> mapM translatePType' tys
    SS.RecordF flds ->
      (fterm . SC.RecordType . M.fromList) <$> mapM translateField flds
        where translateField (fn, fty) = (fn,) <$> translatePType' fty
    SS.FunctionF aty rty ->
      tfun <$> translatePType' aty <*> translatePType' rty
--FIXME    SS.Syn name -> fail $ "unresolved type synonym: " ++ name

--FIXME getPolyTypes :: SS.PType -> [SS.Poly SS.PType]
getPolyTypes (In (Inl _)) = []
getPolyTypes (In (Inr (Inr p))) = [p]
getPolyTypes (In (Inr (Inl ty))) = F.concatMap getPolyTypes ty

translateType :: SS.Type -> SC.Term
translateType ty =
  case ty of
    SS.UnitT -> unitType
    SS.BitT -> bitType
    SS.ZT -> intType
    SS.QuoteT -> quoteType
    SS.ArrayT ety sz -> vec (fromIntegral sz) (translateType ety)
    SS.BlockT ctx rty ->  blockType ctx (translateType rty)
    SS.TupleT tys -> fterm . SC.TupleType . map translateType $ tys
    SS.RecordT flds ->
      fterm . SC.RecordType . M.fromList . map translateField $ flds
        where translateField (fn, fty) = (fn, translateType fty)
    SS.FunctionT aty rty ->
      tfun (translateType aty) (translateType rty)

-- SAWCore term and type constructors

preludeIdent :: String -> SC.Ident
preludeIdent = SC.mkIdent SC.preludeName

fterm :: SC.FlatTermF SC.Term -> SC.Term
fterm = SC.Term . SC.FTermF

tfun :: SC.Term -> SC.Term -> SC.Term
tfun d r = SC.Term $ SC.Pi "_" d r

unitType, bitType, intType, quoteType :: SC.Term
unitType = fterm $ SC.DataTypeApp (preludeIdent "TUnit") []
bitType = fterm $ SC.DataTypeApp (preludeIdent "Bool") []
intType = fterm $ SC.DataTypeApp (preludeIdent "Int") [] -- TODO: Nat?
quoteType = fterm $ SC.DataTypeApp (preludeIdent "String") [] -- TODO

tupleType :: [SC.Term] -> SC.Term
tupleType ts = fterm $ SC.TupleType ts

unitTerm, trueTerm, falseTerm :: SC.Term
unitTerm = fterm $ SC.CtorApp (preludeIdent "Unit") []
trueTerm = fterm $ SC.CtorApp (preludeIdent "True") []
falseTerm = fterm $ SC.CtorApp (preludeIdent "False") []

stringTerm :: String -> SC.Term
stringTerm s = fterm $ SC.StringLit s

natTerm :: Integer -> SC.Term
natTerm n = fterm $ SC.NatLit n

vecTerm :: SC.Term -> [SC.Term] -> SC.Term
vecTerm t es = fterm $ SC.ArrayValue t (V.fromList es)

tupleTerm :: [SC.Term] -> SC.Term
tupleTerm es = fterm $ SC.TupleValue es

globalTerm :: String -> SC.Term
globalTerm name = fterm $ SC.GlobalDef (SC.parseIdent name)

ssGlobalTerm :: String -> SC.Term
ssGlobalTerm s = fterm $ SC.GlobalDef (SC.mkIdent ssPreludeName s)

ssPreludeName :: SC.ModuleName
ssPreludeName = SC.mkModuleName ["SAWScriptPrelude"]
{-
cryptolName = SC.mkModuleName ["Cryptol"]
javaName = SC.mkModuleName ["Java"]
llvmName = SC.mkModuleName ["LLVM"]
-}

blockType :: SS.Context -> SC.Term -> SC.Term
blockType ctx rty = fterm $ SC.DataTypeApp cname [rty]
  where cname =
          case ctx of
            SS.CryptolSetup -> SC.mkIdent ssPreludeName "CryptolSetup"
            SS.JavaSetup -> SC.mkIdent ssPreludeName "JavaSetup"
            SS.LLVMSetup -> SC.mkIdent ssPreludeName "LLVMSetup"
            SS.ProofScript -> SC.mkIdent ssPreludeName "ProofScript"
            SS.TopLevel -> SC.mkIdent ssPreludeName "TopLevel"

vec :: Integer -> SC.Term -> SC.Term
vec n ty = fterm $ SC.DataTypeApp (preludeIdent "Vec") [nt, ty]
  where nt = fterm $ SC.NatLit n

getNat :: SC.Term -> Maybe Integer
getNat (SC.Term (SC.FTermF (SC.NatLit n))) = Just n
getNat _ = Nothing

vecSize :: SC.Term -> Maybe Integer
vecSize (SC.Term
         (SC.FTermF
          (SC.DataTypeApp (SC.identName -> "Vec") [getNat -> n]))) = n
vecSize _ = Nothing

destVec :: SC.SharedTerm s -> Maybe (SC.SharedTerm s, SC.SharedTerm s)
destVec (SC.unwrapTermF ->
         (SC.FTermF
          (SC.DataTypeApp (SC.identName -> "Vec") [n, e]))) = Just (n, e)
destVec _ = Nothing

app :: SC.Term -> SC.Term -> SC.Term
app l r = fterm (SC.App l r)

aget :: Integer -> SC.Term -> SC.Term -> SC.Term -> SC.Term
aget w ety ae ie = app (app (app (app getFn wt) ety) ae) ie
  where wt = fterm (SC.NatLit w)
        getFn = fterm (SC.GlobalDef (preludeIdent "get"))

-- TODO: include type parameters
bind :: SC.Term -> SC.Term -> SC.Term
bind l r = app (app bindFn l) r
  where bindFn = fterm (SC.GlobalDef (preludeIdent "bind"))
