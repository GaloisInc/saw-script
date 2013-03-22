module SAWScript.ToSAWCore where

import Data.List
import qualified Data.Map as M
import qualified Data.Vector as V

import qualified SAWScript.AST as SS
import SAWScript.Unify.Fix
import qualified Verifier.SAW.TypedAST as SC

translateModule :: SS.Module' SS.PType SS.Type -> SC.Module
translateModule (SS.Module tss main) = SC.insDef m mainDef
    where m = foldl' insertTopStmt (SC.emptyModule mname) tss
          mainName = SC.mkIdent mname "main"
          mainDef = SC.Def mainName mainTy [mainBody]
          mname = undefined
          mainTy = undefined -- translatePType ty
          mainBody = SC.DefEqn [] (translateExpr translateType main)

insertTopStmt :: SC.Module -> SS.TopStmt SS.PType -> SC.Module
insertTopStmt m s =
  case s of
    SS.Import mname dnames lname -> m -- TODO
    SS.TypeDef name ty -> m -- TODO

    -- TODO: the following really need to be merged, so we get the
    -- type and body together, unless there is no body.
    SS.TopTypeDecl name ty ->
      SC.insDef m (SC.Def (SC.mkIdent mname name) (translatePType ty) [])
        where mname = undefined
    SS.TopBind name e -> SC.insDef m (SC.Def i t [d])
      where mname = undefined
            i = SC.mkIdent mname name
            t = undefined -- translatePType ty
            d = SC.DefEqn [] (translateExpr translatePType e)

translateBlockStmts :: (a -> SC.Term) -> [SS.BlockStmt a] -> SC.Term
translateBlockStmts _ []  = undefined
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
            ty = undefined
            fty = undefined
    SS.BlockTypeDecl name ty -> undefined
    SS.BlockLet decls ->
      SC.Term $ SC.Let decls' k
      where decls' = map translateDecl decls
            translateDecl (n, e) =
              SC.LocalFnDef n ty [SC.DefEqn [] $ translateExpr doType e]
            ty = undefined

translateExpr :: (a -> SC.Term) -> SS.Expr a -> SC.Term
translateExpr doType e = go e
  where go (SS.Unit _) = undefined
        go (SS.Bit True _) = undefined
        go (SS.Bit False _) = undefined
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
        go (SS.Index a i ty) = undefined
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
translatePType (In (Inl _)) = undefined
translatePType (In (Inr (Inr _))) = undefined
translatePType (In (Inr (Inl ty))) =
  case ty of
    SS.Unit' -> unitType
    SS.Bit' -> bitType
    SS.Z' -> intType
    SS.Quote' -> quoteType
    SS.Array' ety sz -> vec n ety'
      where ety' = translatePType ety
            n = undefined
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
    SS.Syn name -> undefined

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
unitType = fterm $ SC.DataTypeApp (preludeIdent "Unit") []
bitType = fterm $ SC.DataTypeApp (preludeIdent "Bool") []
intType = fterm $ SC.DataTypeApp (preludeIdent "Int") [] -- TODO: Nat?
quoteType = fterm $ SC.DataTypeApp (preludeIdent "String") [] -- TODO

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
