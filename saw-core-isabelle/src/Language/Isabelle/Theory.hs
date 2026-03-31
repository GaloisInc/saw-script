{-# LANGUAGE LambdaCase #-}
module Language.Isabelle.Theory
 ( Theory(..)
 , thyImports
 , Theories
 , singleton
 , forTheories
 , freshTheory
 , mkTheory
 , addDecl
 , addDecls
 , drop
 , lookup
 , update
 , adjust
 , adjustDecls
 , null
 ) where

import           Prelude hiding (drop, lookup, null)

import           Data.Foldable hiding (null)
import qualified Data.Graph as Graph
import           Data.List (intercalate, nub, sort)
import qualified Data.Map as Map
import           Data.Maybe (fromMaybe, mapMaybe)
import qualified Data.Map.Merge.Strict as Map


import qualified Language.Isabelle.Binding as Binding
import qualified Language.Isabelle.Decl as Decl
import qualified Language.Isabelle.Name as Name
import qualified Language.Isabelle.Output as Output
import qualified Language.Isabelle.Panic as Panic
import qualified Data.List as List

data Theory = Theory { thyNm :: Name.TheoryName, thyDecls :: Decl.Decls }
  deriving (Eq, Ord)

mergeThys :: Theory -> Theory -> Theory
mergeThys thy1 thy2 = case thyNm thy1 == thyNm thy2 of
  True -> Theory (thyNm thy1) $ (thyDecls thy1) <> (thyDecls thy2)
  False -> Panic.panic "mergeThys: Theory name clash" [show (thyNm thy1), show (thyNm thy2)]

data Theories = Theories { thyMap :: Map.Map Name.TheoryName Theory }

null :: Theories -> Bool
null thys = Map.null (thyMap thys)

instance Semigroup Theories where
  (Theories thys1) <> (Theories thys2) = Theories
    (Map.merge Map.preserveMissing Map.preserveMissing (Map.zipWithMatched (\_ -> mergeThys)) thys1 thys2)


instance Monoid Theories where
  mempty = Theories Map.empty

singleton :: Theory -> Theories
singleton thy = Theories (Map.singleton (thyNm thy) thy)

-- | Create a theory with a variant of the given name that
--   does not clash with any existing theories.
freshTheory :: Theories -> Name.TheoryName -> Theory
freshTheory (Theories thys) nm =
  let
      nms = map Name.thyNm $ Map.keys thys
      freshNm = Name.freshIdent nms (Name.thyNm nm)
  in  mkTheory (nm { Name.thyNm = freshNm })

mkTheory :: Name.TheoryName -> Theory
mkTheory nm = Theory nm mempty

adjustDecls :: (Decl.Decls -> Decl.Decls) -> Theory -> Theory
adjustDecls f thy = thy { thyDecls = f (thyDecls thy) }

addDecl :: Decl.Decl -> Theory -> Theory
addDecl d = adjustDecls (\ds -> Decl.singleton d <> ds)

addDecls :: Name.TheoryName -> Decl.Decls -> Theories -> Theories
addDecls nm ds thys = thys {thyMap =  Map.insertWith mergeThys nm (Theory nm ds) (thyMap thys)}

lookup :: Name.TheoryName -> Theories -> Theory
lookup nm thys = fromMaybe (mkTheory nm) $ Map.lookup nm (thyMap thys)

adjust :: Name.TheoryName -> (Decl.Decls -> Decl.Decls) -> Theories -> Theories
adjust nm f thys = thys { thyMap = Map.adjust (\thy -> thy { thyDecls = f (thyDecls thy) }) nm (thyMap thys) }

update :: Theory -> Theories -> Theories
update thy = addDecls (thyNm thy) (thyDecls thy)

-- | Drop the theory with the given name and return it, along with the
--   modified 'Theories'.
--   Resulting 'Theory' is empty if it is not in the map.
drop :: Name.TheoryName -> Theories -> (Theory, Theories)
drop nm thys =
  let
    upd k _thy1 _thy2 = mkTheory k
    (res, thys') = Map.insertLookupWithKey upd nm (mkTheory nm) (thyMap thys)
  in (fromMaybe (mkTheory nm) res, Theories thys')

forTheories :: Monad m => Theories -> a -> (Theory -> a -> m a) -> m a
forTheories thys a f = foldrM f a (thyMap thys)


defGraph :: [Decl.Decl] ->
   (Graph.Graph
  , Graph.Vertex -> (Decl.Decl, Name.Name, [Name.Name])
  , Name.Name -> Maybe Graph.Vertex)
defGraph decls =
  let
    go d = case d of
      Decl.Definition _ b _args _ _ -> [(d, Binding.bindName b, deps)]
      Decl.ConstDecl _ b -> [(d, Binding.bindName b, [])]
      Decl.Commented _ d' ->
        map (\(_,nm,deps') -> (d,nm,deps')) (go d')
      Decl.TypeSyn _ nm _ -> [(d, nm, deps)]
      Decl.FixpointLocale nms ->
        let locale_name = Name.SimpleName (Decl.localeName nms)
        in [(d,locale_name, deps)] ++ map (\nm -> (Decl.NoDecl,nm, [locale_name])) nms
      {- Decl.TypeArgSyntax b _ _ _ -> Just (d, syntaxName (Binding.bindName b), [Binding.bindName b]) -}
      _ -> []
      where
        deps = Decl.dependencies d
    raw_graph = concat $ map go decls
  in Graph.graphFromEdges raw_graph



orderDecls :: Theory -> (Decl.Decl -> Bool) -> [Decl.Decl]
orderDecls thy f =
  let (graph, nodeFromVertex, _) = defGraph (nub $ Decl.filter f (thyDecls thy))
  in map (\v -> let (d, _, _) = nodeFromVertex v in d) (Graph.reverseTopSort graph)

isDef :: Decl.Decl -> Bool
isDef = \case
  Decl.Definition{} -> True
  Decl.ConstDecl{} -> True
  Decl.FixpointLocale{} -> True
  _ -> False


thyImports :: Theory -> [Decl.Decl]
thyImports thy = nub $ Decl.filter (\case Decl.Import{} -> True; _ -> False) (thyDecls thy)

instance Output.Output Theory where
  out thy =
    let
      is = thyImports thy
      defs = orderDecls thy isDef
      recordDecls = nub $ Decl.filter (\case Decl.RecordDecl{} -> True; _ -> False) (thyDecls thy)
      tdecls = nub $ Decl.filter (\case Decl.TypeDecl{} -> True;  _ -> False) (thyDecls thy)
      hdecls = nub $ Decl.filter (\case Decl.HashDecl{} -> True;  _ -> False) (thyDecls thy)


      tsyns = orderDecls thy (\case Decl.TypeSyn{} -> True; _ -> False)
      declLine d = case d of
        Decl.NoDecl{} -> Nothing
        _ -> Just (Output.out d <> "\n")
      declLines ds = mapMaybe declLine ds

      noDecls = List.null tdecls && List.null tsyns && List.null defs && List.null comments
      -- Un-associated comments
      comments = Decl.filter (\case Decl.NoDecl{} -> True; _ -> False) (thyDecls thy)
    in
      unlines $
        [ "theory " ++ Output.quotes (Output.out (Name.thyNm (thyNm thy)))
        , "imports " ++ intercalate " " (sort (map Output.out is))
        , "begin"
        , ""
        ]
        ++ declLines recordDecls
        ++ (if noDecls then ["end"] else
          ["context includes cryptol_translation_syntax begin"]
          ++ declLines tdecls
          ++ []
          ++ declLines tsyns
          ++ []
          ++ declLines defs
          ++ []
          ++ declLines hdecls
          ++ []
          ++ declLines comments
          ++ []
          ++ [ "end", "end" ])
