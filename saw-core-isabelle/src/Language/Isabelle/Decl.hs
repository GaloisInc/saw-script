{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Language.Isabelle.Decl 
  (Decl(..)
  , Decls
  , toList
  , traverseImports
  , traverseDecls
  , singleton
  , filter
  , mapMaybe
  , dependencies
  , strip
  , recordName
  , asRecImpl
  , asRecSpec
  , localeName
  ) where

import           Prelude hiding (filter)

import qualified Data.List as List

import qualified Cryptol.TypeCheck.PP as Cry

import qualified Language.Isabelle.Binding as Binding
import           Language.Isabelle.Builtins
import qualified Language.Isabelle.Expr as Expr
import qualified Language.Isabelle.Name as Name
import qualified Language.Isabelle.Output as Output
import qualified Language.Isabelle.Syntax as Syntax
import qualified Language.Isabelle.Template as Template
import Numeric (showHex)
import qualified Data.Maybe as Maybe

data Decl = 
    Definition 
      Bool {- ^ qualified -}
      Binding.Binding {- ^ const name and type -}
      [Binding.Binding] {- ^ argument name/types -}
      Expr.Expr {- ^ body -}
      [Name.Name] {- ^ extra dependencies -}
  | ConstDecl Bool Binding.Binding
  | TypeSyn [Expr.Type] Name.Name Expr.Type
  | TypeDecl [Expr.Type] Name.Name
  | Import Name.TheoryName
  | RecordDecl [String]
  | DatatypeDecl [Expr.Type] Name.Name [(Name.Name,[Expr.Type])]
  | Commented String Decl
  | FixpointLocale [Name.Name]
  | HashDecl 
      Name.Name {- ^ const name -}
      Int {- ^ deep cryptol hash -}
  | NoDecl
  deriving (Eq, Ord, Show)

newtype Decls = Decls { toList :: [Decl] }
  deriving (Semigroup, Monoid, Eq, Ord)

traverseDecls:: Monad m =>  Decls -> (Decl -> m Decl) -> m Decls
traverseDecls (Decls ds) f = do
  ds' <- mapM f (List.nub ds)
  return $ Decls (List.nub ds')

traverseImports :: Monad m =>  Decls -> (Name.TheoryName -> m Name.TheoryName) -> m Decls
traverseImports ds f = do
  let (imports, Decls ds') = strip (\case Import{} -> True; _ -> False) ds
  imports' <- mapM (\case Import nm -> Import <$> f nm; _ -> undefined) (List.nub imports)
  return $ Decls (imports' ++ ds')

liftDeclPred :: (Decl -> Bool) -> Decl -> Bool
liftDeclPred f = \case
  Commented _ d -> liftDeclPred f d
  d -> f d

strip :: (Decl -> Bool) -> Decls -> ([Decl], Decls)
strip f (Decls ds) = let (ds_match, ds') = List.partition (liftDeclPred f) ds in (ds_match, Decls ds')

filter :: (Decl -> Bool) -> Decls -> [Decl]
filter f (Decls ds ) = List.filter (liftDeclPred f) ds

mapMaybe :: (Decl -> Maybe a) -> Decls -> [a]
mapMaybe f (Decls ds) = Maybe.mapMaybe f ds

singleton :: Decl -> Decls
singleton d = Decls [d]

maybeQualifyCmd :: Bool -> String -> String
maybeQualifyCmd True s = "qualified " ++ s
maybeQualifyCmd False s = s

definitionCmd :: Output.HasOutput => Bool -> Binding.Binding -> Maybe ([Binding.Binding], Expr.Expr) -> String
definitionCmd qualify b (Just (args,e)) = maybeQualifyCmd qualify $
  "cryptol_definition " ++ 
        Binding.prettyBindOuter b <> " where\n" ++
        (Output.quotes $ (Output.out (Binding.bindName b)) <> " "
          <> (Output.spaces (map (Output.out . Binding.bindName) args)) <> " \\<equiv> " <> 
                (Output.indent 1 $ (Output.out e)))
definitionCmd qualify b Nothing = maybeQualifyCmd qualify $
  "cryptol_definition " <> Binding.prettyBindOuter b

freshTs :: Int -> ([String], [String])
freshTs i = splitAt i (take (i*2) (map (\s -> "'" ++ s) (Cry.nameList [])))

recordName :: [String] -> Name.Name
recordName args =
  let 
    rawnm = List.intercalate "_" args ++ "_recordT"
    thynm = Name.TheoryName (Name.cleanName $ Name.SimpleName rawnm) True
  in Name.Name thynm rawnm Syntax.NoSyn Name.Typ


recordCmd :: Output.HasOutput => [String] -> Template.Template -> String
recordCmd args template =
  let
    nm = Name.cleanName $ recordName (map Output.out args)
    commas = List.intercalate ","
    sorts s = commas $ List.replicate (length args + 1) s
    (ts, ts') = freshTs (length args + 1)
    coercion = mapRecord nm args (\(_,x) -> coerceExpr x)
    fields = map (\(anm,t) -> Output.out anm ++ " :: " ++ t) (zip args ts)
    catom s = "(" ++ s ++ "::coercible_atom" ++ ")"
  in Output.out $ Template.apply template $ 
    [ nm
    , commas (map catom ts)
    , commas (map catom ts')
    , commas (take (length args) ts)
    , sorts "coercible_atom"
    , sorts "strip_type"
    , Output.indent 1 $ Output.lines $ fields
    , Output.out coercion
    , Output.out $ Output.spaces $ Output.addSep "," fields
    , sorts "zero"
    , Output.out $ recordCtr $ (map (\s -> (Name.SimpleName s, Expr.IntLit 0)) args) ++ [(dots, Expr.IntLit 0)]
    , sorts "_"
    , commas ts
    ]

collectDeps :: Expr.Expr -> [Name.Name]
collectDeps e = Expr.foldSubExprs (\case Expr.Ctr _ nm -> addNm nm; Expr.Var nm -> addNm nm; _ -> id) e []
  where
    addNm :: Name.Name -> [Name.Name] -> [Name.Name]
    addNm nm nms = (nm:nms)

dependencies :: Decl -> [Name.Name]
dependencies = \case
  Definition _ _ _ e extra -> extra ++ collectDeps e
  ConstDecl{} -> []
  Commented _ d -> dependencies d
  TypeDecl{} -> []
  TypeSyn _ _ rhs -> collectDeps rhs
  RecordDecl{} -> []
  DatatypeDecl targs _ flds -> concat $ map collectDeps $ ((concat $ map (\(_,ts) -> ts) flds) List.\\ targs)
  Import{} -> []
  FixpointLocale nms -> (map asRecImpl nms ++ map asRecSpec nms)
  HashDecl nm _ -> [nm]
  NoDecl -> []

tyHeader :: Output.HasOutput => [Expr.Expr] -> Name.Name -> String
tyHeader [] nm = Output.out nm
tyHeader es nm = Output.brackets (List.intercalate "," (map Output.out es)) ++ " " ++ Output.out nm

lcp2 :: Eq a => [a] -> [a] -> [a]
lcp2 xs ys = map fst (takeWhile (\(x,y) -> x == y) (zip xs ys))

lcp :: Eq a => [[a]]-> [a]
lcp [] = []
lcp (x:xs) = foldl lcp2 x xs

asRecImpl :: Name.HasIdent t => t -> t
asRecImpl = Name.mapIdent (\ident -> ident <> "_impl")

asRecSpec :: Name.HasIdent t => t -> t
asRecSpec = Name.mapIdent (\ident -> ident <> "_spec")

fixPointLocale :: 
 Output.HasOutput => 
 [Name.Name] -> 
 Template.Template ->
 String
fixPointLocale baseNames template = 
  let 
    impls = map asRecImpl baseNames
    specs = map asRecSpec baseNames
    asms = map (\(lhs,rhs) -> eqExpr (Expr.Var lhs) (Expr.Var rhs)) (zip specs impls)
    defs = map (\(lhs,rhs) -> eqExpr (Expr.Var lhs) (Expr.Var rhs)) (zip baseNames impls)
    def_template = (Output.getTemplate "Fixpoint_Locale_Def")

    def_cmds = map (\(nm,e) -> 
         Output.out $ Template.apply def_template [Output.out nm, Output.out e])
         (zip impls defs)

    locale_name = localeName baseNames
    aliases = 
      map (\nm -> "alias " ++ Output.out nm ++ " = " 
                 ++ locale_name ++ "." ++ Output.out nm) baseNames
    hides = 
      map (\nm -> "hide_fact " ++ locale_name ++ "." ++ Output.out nm ++ "_def") baseNames
  in Output.out $ Template.apply template $ 
     [ locale_name
     , Output.spaces (Output.addSep "and" (map (\e -> Output.quotes (Output.out e)) asms))
     , Output.lines def_cmds
     , Output.lines aliases
     , Output.lines hides
     ]

localeName :: [Name.Name] -> String
localeName bs = lcp (map Name.identOf bs) ++ "_rec_spec"

isTNum :: Expr.Type -> Bool
isTNum t = case t of
  Expr.Var tnm | Name.TNum <- Name.nmKind tnm -> True
  _ -> False

nameIdx :: Name.Name -> Int -> Name.Name
nameIdx nm 0 = nm
nameIdx nm i = Name.mapIdent (\x -> x ++ show i) nm

freshVars :: [Expr.Type] -> [Expr.Type]
freshVars = go [] 0
  where
    go acc i = \case
      ts@(Expr.Var nm:ts') -> 
        let t' = Expr.Var (nameIdx nm i)
        in case elem t' (ts ++ acc) of
          True -> go acc (i+1) (t':ts')
          False -> go (t':acc) 0 ts'
      (t':ts) -> go (t':acc) 0 ts
      [] -> reverse acc

mkSameType :: Output.HasOutput => (Expr.Type, Expr.Type) -> String
mkSameType (t1, t2) = Output.brackets $ case isTNum t1 of
  True -> "LEN" ++ Output.brackets (Output.out t1) ++ " = " ++ "LEN" ++ Output.brackets (Output.out t2)
  False -> "same_type TYPE" ++ Output.brackets (Output.out t1) ++ " TYPE" ++ Output.brackets (Output.out t2)

datatypeDecl :: 
 Output.HasOutput => 
 [Expr.Type] -> 
 Name.Name ->
 [(Name.Name,[Expr.Type])] ->
 Template.Template ->
 String
datatypeDecl targs nm flds template =
  let targs' = freshVars targs
      defs = map (\(fnm,fts) -> Name.cleanName fnm ++ " " ++ List.intercalate " " (map (Output.quotes . Output.out) fts)) flds
      sorts s = List.intercalate "," $ map (\t -> if isTNum t then "_" else s) targs
      commas xs = List.intercalate "," (map Output.out xs)
      shownat n = Output.brackets $ show n ++ "::nat"
      natcase n = case n of
        0 -> "0"
        _ -> "Suc (" ++ natcase (n-1) ++ ")"
      catom s = case isTNum s of
        True -> Output.out s
        False -> "(" ++ Output.out s ++ "::coercible_atom" ++ ")"
      mk_comp f n = Output.brackets $ List.intercalate " o " (replicate n f)
      mk_strip (n,(_,fts)) = Output.brackets $ case length fts of
        0 -> "strip (" ++ shownat n ++ ",())"
        1 -> "curry strip " ++ shownat n
        _ -> mk_comp "curry" (length fts - 1) ++ (Output.brackets $ "curry strip " ++ shownat n)
      mk_unstrip_rhs (fnm,fts) = case length fts of
        0 -> "\\<lambda> _. " ++ Output.out fnm
        1 -> Output.out fnm ++ " o unstrip"
        _ -> mk_comp "uncurry" (length fts - 1) ++ " "
                ++ Output.out fnm ++ " o unstrip"
      mk_unstrip (n,r) = natcase n ++ " \\<Rightarrow> " ++ mk_unstrip_rhs r
      mk_strip_type tp = case tp of
        Expr.Var tnm | Name.TNum <- Name.nmKind tnm -> 
          "Tn LEN(" ++ Output.out tnm ++ ")"
        _ -> "strip_type TYPE(" ++ Output.out tp ++ ")"
      mk_coerce (fnm,fts) = Output.brackets $ case length fts of
        0 -> Output.out fnm
        1 -> Output.out fnm ++ " o coerce"
        _ -> let s = mk_comp "uncurry" (length fts - 1) ++ " " ++ Output.out fnm ++ " o coerce"
          in  mk_comp "curry" (length fts - 1) ++ " " ++ Output.brackets s

  in Output.out $ Template.apply template $ 
    [ Name.cleanName nm
    , commas targs
    , List.intercalate " | " defs
    , commas $ map mk_strip_type targs
    , commas targs'
    , sorts "coercible_atom"
    , List.intercalate " " (map mk_strip (zip [0::Integer ..] flds))
    , List.intercalate " | " (map mk_unstrip (zip [0::Integer ..] flds))
    , sorts "_"
    , sorts "strip_type"
    , commas $ map catom targs
    , commas $ map catom targs'
    , List.intercalate " \\<and> " $ map mkSameType (zip targs targs')
    , ""
    , List.intercalate " " $ map mk_coerce flds
    ]

instance Output.Output Decl where
  out = \case
    Definition q b args e _ -> definitionCmd q b (Just (args,e))
    ConstDecl q b -> definitionCmd q b Nothing
    Import i -> Output.out (Name.thyNm i)
    TypeSyn targs nm rhs -> 
        "type_synonym " ++ tyHeader targs nm ++ " = " ++ Output.quotes (Output.out rhs)
    TypeDecl targs nm -> "typedecl " ++ tyHeader targs nm
    RecordDecl args -> recordCmd args (Output.getTemplate "Coercible_Record")
    DatatypeDecl targs nm flds -> datatypeDecl targs nm flds (Output.getTemplate "Coercible_Datatype")
    FixpointLocale args -> fixPointLocale args (Output.getTemplate "Fixpoint_Locale")
    Commented msg d -> "(* " ++ msg ++ "*)\n" ++ Output.out d
    HashDecl nm h -> "declare [[set_const_hash " ++ Output.out nm ++ " 0x" ++ showHex (fromIntegral h :: Word) "" ++ "]]"
    NoDecl -> ""