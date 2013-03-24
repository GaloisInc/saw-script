{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module SAWScript.ToSAWCore
  ( translateModule
  )
  where

import Control.Applicative
import Control.Monad.Error
import Control.Monad.Identity
import Data.List
import qualified Data.Map as M
import qualified Data.Vector as V

import qualified SAWScript.AST as SS
import SAWScript.Unify.Fix
import qualified Verifier.SAW.TypedAST as SC

newtype M a = M (ErrorT String Identity a)
  deriving (Functor, Monad, MonadError String)

translateModule :: SS.Module' SS.PType SS.Type -> M SC.Module
translateModule (SS.Module mname tss main) =
  flip SC.insDef mainDef <$> foldM insertTopStmt (SC.emptyModule modName) tss
    where modName = SC.mkModuleName [mname]
          mainName = SC.mkIdent modName "main"
          mainDef = SC.Def mainName mainTy [mainBody]
          mainTy = translateType (SS.decor main)
          mainBody = SC.DefEqn [] (translateExpr translateType main)

insertTopStmt :: SC.Module -> SS.TopStmt SS.PType -> M SC.Module
insertTopStmt m s = return $
  case s of
    SS.Import mname dnames lname -> m -- TODO
    SS.TypeDef name ty -> m -- TODO

    -- Types from signatures get propagated during type checking, so
    -- they don't need to be inserted into the module.
    SS.TopTypeDecl name ty -> m

    SS.TopBind name e -> SC.insDef m (SC.Def i t [d])
      where mname = SC.moduleName m
            i = SC.mkIdent mname name
            t = translatePType (SS.decor e)
            d = SC.DefEqn [] (translateExpr translatePType e)

translateBlockStmts :: (a -> SC.Term) -> [SS.BlockStmt a] -> SC.Term
translateBlockStmts _ []  = error "can't translate empty block"
translateBlockStmts doType [SS.Bind Nothing ctx e] = translateExpr doType e
translateBlockStmts _ [s] = error "invalid block ending statement"
translateBlockStmts doType (s:ss) =
  translateBlockStmt doType s (translateBlockStmts doType ss)

translateBlockStmt :: (a -> SC.Term) -> SS.BlockStmt a -> SC.Term -> SC.Term
translateBlockStmt doType s k =
  case s of
    SS.Bind (Just x) ctx e -> fterm $ bind (translateExpr doType e) f
      where f = SC.Lambda (SC.PVar x i ty) fty k
            i = undefined
            ty = doType (SS.decor e)
            fty = undefined
    SS.BlockTypeDecl name ty -> undefined
    SS.BlockLet decls ->
      SC.Term $ SC.Let decls' k
      where decls' = map translateDecl decls
            translateDecl (n, e) =
              SC.LocalFnDef n ty [SC.DefEqn [] $ translateExpr doType e]
                where ty = doType (SS.decor e)

translateExpr :: (a -> SC.Term) -> SS.Expr a -> SC.Term
translateExpr doType e = go e
  where go (SS.Unit _) = unitTerm
        go (SS.Bit True _) = trueTerm
        go (SS.Bit False _) = falseTerm
        go (SS.Quote s _) = undefined
        go (SS.Z i _) = fterm $ SC.NatLit (fromIntegral i)
        go (SS.Array es ty) =
             fterm $ SC.ArrayValue (doType ty) es'
               where es' = V.fromList $ map go es
        go (SS.Block ss ty) = translateBlockStmts doType ss
        go (SS.Tuple es _) = fterm $ SC.TupleValue (map go es)
        go (SS.Record flds ty) =
             fterm $ SC.RecordValue (M.fromList $ map translateFld flds)
               where translateFld (n, e) = (n, go e)
        go (SS.Index a i ty) =
          aget n (doType ty) (go a) (go i)
            where n = case doType (SS.decor a) of
                        (vecSize -> Just i) -> i
                        _ -> error "array size is not constant"
        go (SS.Lookup e f ty) = fterm $ SC.RecordSelector (go e) f
        go (SS.Var x ty) = SC.Term . SC.LocalVar i . doType $ ty
             where i = undefined
        go (SS.Function x ty body fty) =
          SC.Term $ SC.Lambda pat (doType fty) (go body)
            where pat = SC.PVar x i (doType ty)
                  i = undefined
        go (SS.Application f e ty) =
             fterm $ SC.App (go f) (go e)
        go (SS.LetBlock decls e) = SC.Term . SC.Let decls' $ go e
             where decls' = map translateDecl decls
                   translateDecl (n, e) =
                     SC.LocalFnDef n ty [SC.DefEqn [] $ go e]
                   ty = undefined

translatePType :: SS.PType -> SC.Term
translatePType (In (Inl _)) = error "polymorphic type is integer"
translatePType (In (Inr (Inr _))) = undefined -- Type variable
translatePType (In (Inr (Inl ty))) =
  case ty of
    SS.Unit' -> unitType
    SS.Bit' -> bitType
    SS.Z' -> intType
    SS.Quote' -> quoteType
    SS.Array' ety (In (Inl (SS.I n))) -> vec n ety'
      where ety' = translatePType ety
    SS.Array' ety _ -> error "array dimension is not constant"
    SS.Block' ctx rty -> blockType ctx rty'
      where rty' = translatePType rty
    SS.Tuple' tys ->
      fterm . SC.TupleType . map translatePType $ tys
    SS.Record' flds ->
      fterm . SC.RecordType . M.fromList . map translateField $ flds
        where translateField (fn, fty) = (fn, translatePType fty)
    SS.Function' aty rty -> SC.Term $ SC.Pi aname aty' rty'
      where aname = undefined
            aty' = translatePType aty
            rty' = translatePType rty
    SS.Syn name -> error $ "unresolved type synonym: " ++ name

translateType :: SS.Type -> SC.Term
translateType ty =
  case ty of
    SS.UnitT -> unitType
    SS.BitT -> bitType
    SS.ZT -> intType
    SS.QuoteT -> quoteType
    SS.ArrayT ety sz -> vec (fromIntegral sz) ety'
      where ety' = translateType ety
    SS.BlockT ctx rty ->  blockType ctx rty'
      where rty' = translateType rty
    SS.TupleT tys -> fterm . SC.TupleType . map translateType $ tys
    SS.RecordT flds ->
      fterm . SC.RecordType . M.fromList . map translateField $ flds
        where translateField (fn, fty) = (fn, translateType fty)
    SS.FunctionT aty rty -> SC.Term $ SC.Pi aname aty' rty'
      where aname = undefined
            aty' = translateType aty
            rty' = translateType rty

bind = undefined

preludeIdent = SC.mkIdent SC.preludeName
fterm = SC.Term . SC.FTermF

unitType, bitType, intType, quoteType :: SC.Term
unitType = fterm $ SC.DataTypeApp (preludeIdent "TUnit") []
bitType = fterm $ SC.DataTypeApp (preludeIdent "Bool") []
intType = fterm $ SC.DataTypeApp (preludeIdent "Int") [] -- TODO: Nat?
quoteType = fterm $ SC.DataTypeApp (preludeIdent "String") [] -- TODO

unitTerm, trueTerm, falseTerm :: SC.Term
unitTerm = fterm $ SC.CtorApp (preludeIdent "Unit") []
trueTerm = fterm $ SC.CtorApp (preludeIdent "True") []
falseTerm = fterm $ SC.CtorApp (preludeIdent "False") []

ssPreludeName, cryptolName, javaName, llvmName :: SC.ModuleName
ssPreludeName = SC.mkModuleName ["SAWScriptPrelude"]
cryptolName = SC.mkModuleName ["Cryptol"]
javaName = SC.mkModuleName ["Java"]
llvmName = SC.mkModuleName ["LLVM"]

blockType :: SS.Context -> SC.Term -> SC.Term
blockType ctx rty = fterm $ SC.DataTypeApp cname [rty]
  where cname =
          case ctx of
            SS.CryptolSetupContext -> SC.mkIdent cryptolName "Setup"
            SS.JavaSetupContext -> SC.mkIdent javaName "Setup"
            SS.LLVMSetupContext -> SC.mkIdent llvmName "Setup"
            SS.VerifyScriptContext -> SC.mkIdent ssPreludeName "VerifyScript"
            SS.TopLevelContext -> SC.mkIdent ssPreludeName "TopLevel"

vec :: Integer -> SC.Term -> SC.Term
vec n ty = fterm $ SC.DataTypeApp (preludeIdent "Vec") [nt, ty]
  where nt = fterm $ SC.NatLit n

getNat (SC.Term (SC.FTermF (SC.NatLit n))) = Just n
getNat _ = Nothing

vecSize :: SC.Term -> Maybe Integer
vecSize (SC.Term
         (SC.FTermF
          (SC.DataTypeApp (SC.identName -> "Vec") [getNat -> n]))) = n
vecSize _ = Nothing

aget = undefined
