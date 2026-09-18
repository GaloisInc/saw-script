{- |
Module      : SAWCentral.ASTDump
Description : Dumper for SAWScript abstract syntax
License     : BSD3
Maintainer  : saw@galois.com
Stability   : provisional

This is a dumper (not prettyprinter) for the SAWScript abstract syntax.

For the moment it lives in SAWCentral so it's accessible from
SAWCentral.Value.

It mostly doesn't print source positions on the grounds that they're
generally not interesting and take up space. (It _does_ print type
provenance, though, including those positions, as that's less
straightforward.)
-}
{-# LANGUAGE OverloadedStrings #-}

module SAWCentral.ASTDump (
    dumpKind,
    dumpPosition,
    dumpTypeProvenance,
    dumpType,
    dumpSchema,
    dumpSchemaPattern,
    dumpExpr,
    dumpPattern,
    dumpStmt,
    dumpDecl,
    dumpDeclGroup
  ) where

import qualified Data.Text as Text
import qualified Data.Map as Map

import qualified Cryptol.Utils.Ident as Cry
import qualified Cryptol.Parser.AST as Cry

import SAWSupport.Position
import qualified SAWSupport.Dump as Dump
import SAWSupport.Dump (Dump)
import SAWCentral.Position (Pos)
import SAWCentral.AST


------------------------------------------------------------
-- Cryptol bits

-- Cryptol doesn't have dumps so far, so provide some pretend ones.
-- Unfortunately the guts of these things are mostly not exported...

dumpIdent :: Cry.Ident -> Dump
dumpIdent x = Dump.singleton $ Cry.identText x

dumpModName :: Cry.ModName -> Dump
dumpModName mn = Dump.singleton $ Cry.modNameToText mn

dumpImportSpec :: Cry.ImportSpec -> Dump
dumpImportSpec spec = case spec of
    Cry.Hiding names -> Dump.subelements "Hiding" $ map dumpIdent names
    Cry.Only names -> Dump.subelements "Only" $ map dumpIdent names


------------------------------------------------------------
-- SAWScript AST

dumpKind :: Kind -> Dump
dumpKind kind =
    Dump.singleton ("Kind " <> Text.pack (show $ kindNumArgs kind))

dumpPosition :: Pos -> Dump
dumpPosition pos =
    Dump.text $ ppPosition pos

dumpTypeProvenance :: TypeProvenance -> Dump
dumpTypeProvenance prov = case prov of
    TypeExplicit pos ->
        Dump.singleton ("Prov: Explicit at " <> ppPosition pos)
    TypeFresh pos ->
        Dump.singleton ("Prov: Fresh at " <> ppPosition pos)
    TypeFailed pos ->
        Dump.singleton ("Prov: Failed at " <> ppPosition pos)
    TypeFromForallNamed pos x f ->
        let pos' = ppPosition pos
            heading' = x <> " in " <> f
        in
        Dump.singleton ("Prov: Forall at " <> pos' <> ": named " <> heading')
    TypeFromForallFresh pos x f ->
        let pos' = ppPosition pos
            heading' = x <> " in " <> f
        in
        Dump.singleton ("Prov: Forall at " <> pos' <> ": fresh " <> heading')
    TypeFromElement pos tyctx ->
        let pos' = ppPosition pos
            tyctx' = ppTyCtx tyctx
        in
        Dump.singleton ("Prov: From element " <> tyctx' <> " at " <> pos')
    TypeFromContext pos tyctx ->
        let pos' = ppPosition pos
            tyctx' = ppTyCtx tyctx
        in
        Dump.singleton ("Prov: From context " <> tyctx' <> " at " <> pos')
    TypeFromFuncWithSig pos ->
        Dump.singleton ("Prov: From function header at " <> ppPosition pos)
    TypeFromFuncWithBody pos1 pos2 ->
        let pos1' = ppPosition pos1
            pos2' = ppPosition pos2
        in
        Dump.singleton ("Prov: From function header at " <> pos1' <>
                        " with body at " <> pos2')

-- The only place this is used identifies it (it's in a field value)
-- so it doesn't have to identify itself.
dumpNamedParamInfo :: NamedParamInfo -> Dump
dumpNamedParamInfo (NamedParamInfo n names) =
    let n' = Text.pack $ show n
        names' = Text.concat $ map (\name -> " " <> name) names
    in
    Dump.singleton (n' <> names')

dumpType :: Type -> Dump
dumpType ty0 = case ty0 of
    TyCon prov tycon args ->
        let prov' = dumpTypeProvenance prov in
        let tycon' = case tycon of
              TupleCon k -> "Tuple " <> Text.pack (show k)
              ArrayCon -> "Array"
              StringCon -> "String"
              TermCon -> "Term"
              TypeCon -> "Type"
              BoolCon -> "Bool"
              IntCon -> "Int"
              BlockCon -> "Block"
              AIGCon -> "AIG"
              CFGCon -> "CFG"
              JVMSpecCon -> "JVMSpec"
              LLVMSpecCon -> "LLVMSpec"
              MIRSpecCon -> "MIRSpec"
              ContextCon ProofScript -> "ProofScript"
              ContextCon TopLevel -> "TopLevel"
        in
        Dump.subelements ("TyCon " <> tycon') (prov' : map dumpType args)
    TyFunc prov npi params namedParams ret ->
        let prov' = dumpTypeProvenance prov in
        let dumpNamedParam (name, ty) =
                Dump.subelement ("named " <> name) $ dumpType ty
        in
        let namedParams' = map dumpNamedParam $ Map.toList namedParams in
        Dump.fields "TyFunc" [
            ("provenance", prov'),
            ("NamedParamInfo", dumpNamedParamInfo npi),
            ("params", Dump.list $ map dumpType params),
            ("namedParams", Dump.list namedParams'),
            ("ret", dumpType ret)
        ]
    TyRecord prov members ->
        let dumpMember (name, ty) = (name, dumpType ty) in
        let prov' = dumpTypeProvenance prov
            members' = map dumpMember $ Map.toList members
        in
        Dump.fields "TyRecord" (("(provenance", prov') : members')
    TyVar prov name ->
        let prov' = dumpTypeProvenance prov in
        Dump.subelement ("TyVar " <> name) prov'
    TyUnifyVar prov n ->
        let prov' = dumpTypeProvenance prov in
        Dump.subelement ("TyUnifyVar " <> Text.pack (show n)) prov'

dumpSchema :: Schema -> Dump
dumpSchema (Forall foralls ty) =
    let foralls' = Text.concat $ map (\(_prov, name) -> name) foralls in
    Dump.subelement ("Schema {" <> foralls' <> "}") $ dumpType ty

dumpSchemaPattern :: SchemaPattern -> Dump
dumpSchemaPattern (SchemaPattern foralls tys) =
    let foralls' = Text.concat $ map (\(_prov, name) -> name) foralls in
    Dump.subelements ("SchemaPattern {" <> foralls' <> "}") $ map dumpType tys

dumpExpr :: Expr -> Dump
dumpExpr e0 = case e0 of
    Bool _ b ->
        Dump.subelement "Bool" $ Dump.bool b
    String _ txt ->
        Dump.subelement "String" $ Dump.qstring txt
    Int _ k ->
        Dump.subelement "Int" $ Dump.int k
    Code _ txt ->
        Dump.subelement "Code" $ Dump.surroundText' "{{" txt "}}"
    CType _ txt ->
        Dump.subelement "CType" $ Dump.surroundText' "{{" txt "}}"
    Array _ es ->
        Dump.subelements "Array" $ map dumpExpr es
    Block _ (stmts, final) ->
        Dump.subelements "Block" $ map dumpStmt stmts ++ [dumpExpr final]
    Tuple _ es ->
        Dump.subelements "Tuple" $ map dumpExpr es
    Record _ tbl ->
        Dump.fields "Record" $ map (\(n, e) -> (n, dumpExpr e)) $ Map.toList tbl
    Index _ e1 e2 ->
        Dump.fields "Index" [("e1", dumpExpr e1), ("e2", dumpExpr e2)]
    Lookup _ e1 name ->
        Dump.subelement ("Lookup " <> name) $ dumpExpr e1
    TLookup _ e1 n ->
        Dump.subelement ("TLookup " <> (Text.pack $ show n)) $ dumpExpr e1
    Var _ x ->
        Dump.singleton ("Var " <> x)
    Lambda _ (mname) _ params namedParams body ->
        let dumpNamedParam (name, (_namepos, (_fullpos, def, pat))) =
                Dump.fields ("named " <> name) [
                    ("default", dumpExpr def),
                    ("pattern", dumpPattern pat)
                ]
        in
        let heading' = case mname of
              Nothing -> "Lambda"
              Just name -> "Lambda " <> name
            params' = map dumpPattern params
            namedParams' = map dumpNamedParam $ Map.toList namedParams
            body' = dumpExpr body
        in
        Dump.fields heading' [
            ("params", Dump.list (params' ++ namedParams')),
            ("body", body')
        ]
    Application _ f args ->
        let dumpArg (optname, e) = case optname of
              Nothing -> dumpExpr e
              Just (_, name) -> Dump.subelement ("named " <> name) $ dumpExpr e
        in
        Dump.fields "Application" [
            ("function", dumpExpr f),
            ("args", Dump.list $ map dumpArg args)
        ]
    Let _ dg e ->
        Dump.fields "Let" [
            ("decls", dumpDeclGroup dg),
            ("body", dumpExpr e)
        ]
    TSig _ e ty ->
        Dump.fields "TSig" [
            ("expr", dumpExpr e),
            ("type", dumpType ty)
        ]
    IfThenElse _ c t f ->
        Dump.fields "IfThenElse" [
            ("cond", dumpExpr c),
            ("true", dumpExpr t),
            ("false", dumpExpr f)
        ]

dumpPattern :: Pattern -> Dump
dumpPattern pat = case pat of
    PImplicit _ mty ->
        Dump.subelement "PImplicit" $ Dump.maybe dumpType mty
    PWild _ mty ->
        Dump.subelement "PWild" $ Dump.maybe dumpType mty
    PVar _pos _npos name mty ->
        Dump.subelement ("PVar " <> name) $ Dump.maybe dumpType mty
    PTuple _pos pats ->
        Dump.subelements "PTuple" $ map dumpPattern pats

dumpStmt :: Stmt -> Dump
dumpStmt s0 = case s0 of
    StmtBind _pos pat e ->
        Dump.fields "StmtBind" [
            ("pat", dumpPattern pat),
            ("expr", dumpExpr e)
        ]
    StmtLet _pos RebindableVar dg ->
        Dump.subelement "StmtLet rebindable" $ dumpDeclGroup dg
    StmtLet _pos ReadOnlyVar dg ->
        Dump.subelement "StmtLet nonrebindable" $ dumpDeclGroup dg
    StmtCode _pos _tpos txt ->
        Dump.subelement "StmtCode" $ Dump.surroundText' "{{" txt "}}"
    StmtImport _pos imp ->
        let module' = case iModule imp of
              Left fp -> Dump.qstring (Text.pack fp)
              Right modname -> dumpModName modname
        in
        Dump.fields "StmtImport" [
            ("iIsSubmodule", Dump.bool $ iIsSubmodule imp),
            ("iModule", module'),
            ("iIsBacktick", Dump.bool $ iIsBacktick imp),
            ("iAs", Dump.maybe dumpModName $ iAs imp),
            ("iSpec", Dump.maybe dumpImportSpec $ iSpec imp)
        ]
    StmtInclude _pos name once ->
        let once' = if once then "once" else "always" in
        Dump.subelement ("StmtInclude " <> once') $ Dump.qstring name
    StmtTypedef _pos _npos name ty ->
        Dump.subelement ("StmtTypedef " <> name) $ dumpType ty
    StmtPushdir _ path ->
        Dump.subelement "StmtPushdir" $ Dump.text (Text.pack path)
    StmtPopdir _ ->
        Dump.singleton "StmtPopdir"

dumpDecl :: Decl -> Dump
dumpDecl d =
    Dump.fields "Decl" [
        ("dPos", Dump.text $ ppPosition $ dPos d),
        ("dPat", dumpPattern $ dPat d),
        ("dType", Dump.maybe dumpSchema $ dType d),
        ("dDef", dumpExpr $ dDef d)
    ]

dumpDeclGroup :: DeclGroup -> Dump
dumpDeclGroup dg = case dg of
    Recursive ds ->
        Dump.subelements "Recursive decls:" $ map dumpDecl ds
    NonRecursive d ->
        Dump.prepend "NonRecursive" $ dumpDecl d
