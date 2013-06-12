{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TupleSections #-}

-- TODO: generate correct deBruijn indices
-- TODO: translate inferred types to explicit type parameters
module SAWScript.ToSAWCore
  ( translateModule
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

import qualified SAWScript.AST as SS
import SAWScript.Unify.Fix
import qualified Verifier.SAW.TypedAST as SC

data Env = Env {
    modules :: [SC.Module]
  , depth :: Int
  , locals :: Env Int
  , globals :: [SC.Ident]
  }

emptyEnv :: Env
emptyEnv =
  Env { modules = []
      , depth = 0
      , locals = M.empty
      , globals = []
      }

incVars :: Map a Int -> Map a Int
incVars = M.map (+1)

addLocal :: SS.Name -> M a -> M a
addLocal x =
  local (\env -> env { locals = M.insert x 0 (incVars (locals env)) })

newtype M a = M (ReaderT Env (ErrorT String Identity) a)
  deriving (Applicative, Functor, Monad, MonadError String, MonadReader Env)

runTranslate :: Env -> M a -> Either String a
runTranslate env (M a) = runIdentity . runErrorT . runReaderT a $ env

translateModule :: [SC.Module] -> SS.Module' SS.PType SS.Type -> Either String SC.Module
translateModule ms m = runTranslate env $ translateModule' m
    where ssGlobs = mapMaybe getTopBindName (SS.declarations m)
          getTopBindName (SS.TopBind name _) =
            Just $ SC.mkIdent (SC.mkModuleName [SS.modName m]) name
          getTopBindName _ = Nothing
          scGlobs = map SC.defIdent . SC.moduleDefs
          globs = ssGlobs ++ concatMap scGlobs ms
          env = (emptyEnv { modules = ms, globals = globs })

translateModule' :: SS.Module' SS.PType SS.Type -> M SC.Module
translateModule' (SS.Module mname tss main) = do
  body' <- translateExpr (return . translateType) main
  let mainBody = SC.DefEqn [] body'
      modName = SC.mkModuleName [mname]
      mainName = SC.mkIdent modName "main"
      mainDef = SC.Def mainName mainTy [mainBody]
      mainTy = translateType (SS.typeOf main)
  flip SC.insDef mainDef <$> foldM insertTopStmt (SC.emptyModule modName) tss

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

translateBlockStmts :: (a -> M SC.Term) -> [SS.BlockStmt a]
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

translateExpr :: (a -> M SC.Term) -> SS.Expr a -> M SC.Term
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
        go (SS.Var x ty) = do
          gs <- globals <$> ask
          -- TODO: this isn't the right name-matching logic. Fix once
          -- qualified names are fully implemented in SAWScript.
          let matches = find (\i -> SC.identName i == x) gs
          case matches of
            Nothing -> do
              ls <- locals <$> ask
              case M.lookup x ls of
                Just n -> (SC.Term . SC.LocalVar n) <$> doType ty
                Nothing -> fail $ "unbound variable: " ++ x
            Just i -> return . fterm . SC.GlobalDef $ i
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

translatePType :: SS.PType -> M SC.Term
translatePType t = addParams ps <$> local polyEnv (translatePType' t)
    where ps = map unwrap $ getPolyTypes t
          unwrap (SS.Poly n) = n
          polyEnv env = env { locals = M.fromList (zip (reverse ps) [0..]) }
          addParams [] = id
          addParams (_:ns) =
            tfun (fterm (SC.Sort (SC.mkSort 0))) . addParams ns

translatePType' :: SS.PType -> M SC.Term
translatePType' (In (Inl _)) = fail "polymorphic type is integer"
translatePType' (In (Inr (Inr (SS.Poly x)))) = do
  ls <- locals <$> ask
  case M.lookup x ls of
    Just n ->
      return . SC.Term . SC.LocalVar n $ fterm . SC.Sort . SC.mkSort $ 0
    Nothing -> fail $ "unbound type variable: " ++ x
translatePType' (In (Inr (Inl ty))) =
  case ty of
    SS.Unit' -> return unitType
    SS.Bit' -> return bitType
    SS.Z' -> return intType
    SS.Quote' -> return quoteType
    SS.Array' ety (In (Inl (SS.I n))) -> vec n <$> translatePType' ety
    SS.Array' _ _ -> fail "array dimension is not constant"
    SS.Block' ctx rty -> blockType ctx <$> translatePType' rty
    SS.Tuple' tys ->
      (fterm . SC.TupleType) <$> mapM translatePType' tys
    SS.Record' flds ->
      (fterm . SC.RecordType . M.fromList) <$> mapM translateField flds
        where translateField (fn, fty) = (fn,) <$> translatePType' fty
    SS.Function' aty rty ->
      tfun <$> translatePType' aty <*> translatePType' rty
    SS.Syn name -> fail $ "unresolved type synonym: " ++ name

getPolyTypes :: SS.PType -> [SS.Poly SS.PType]
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

unitTerm, trueTerm, falseTerm :: SC.Term
unitTerm = fterm $ SC.CtorApp (preludeIdent "Unit") []
trueTerm = fterm $ SC.CtorApp (preludeIdent "True") []
falseTerm = fterm $ SC.CtorApp (preludeIdent "False") []

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
            SS.CryptolSetupContext -> SC.mkIdent ssPreludeName "CryptolSetup"
            SS.JavaSetupContext -> SC.mkIdent ssPreludeName "JavaSetup"
            SS.LLVMSetupContext -> SC.mkIdent ssPreludeName "LLVMSetup"
            SS.ProofScriptContext -> SC.mkIdent ssPreludeName "ProofScript"
            SS.TopLevelContext -> SC.mkIdent ssPreludeName "TopLevel"

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
