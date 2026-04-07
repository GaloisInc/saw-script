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


instance Output.Output Decl where
  out = \case
    Definition q b args e _ -> definitionCmd q b (Just (args,e))
    ConstDecl q b -> definitionCmd q b Nothing
    Import i -> Output.out (Name.thyNm i)
    TypeSyn targs nm rhs -> 
        "type_synonym " ++ tyHeader targs nm ++ " = " ++ Output.quotes (Output.out rhs)
    TypeDecl targs nm -> "typedecl " ++ tyHeader targs nm
    RecordDecl args -> recordCmd args (Output.getTemplate "Coercible_Record")
    FixpointLocale args -> fixPointLocale args (Output.getTemplate "Fixpoint_Locale")
    Commented msg d -> "(* " ++ msg ++ "*)\n" ++ Output.out d
    HashDecl nm h -> "declare [[set_const_hash " ++ Output.out nm ++ " 0x" ++ showHex (fromIntegral h :: Word) "" ++ "]]"
    NoDecl -> ""