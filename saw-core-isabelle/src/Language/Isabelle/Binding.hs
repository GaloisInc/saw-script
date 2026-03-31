module Language.Isabelle.Binding where

import           Language.Isabelle.Expr (Type)

import qualified Language.Isabelle.Name as Name
import           Language.Isabelle.Name (Name)

import qualified Language.Isabelle.Output as Output
import           Language.Isabelle.Output (Output,out)

data Binding = Binding { bindName :: Name, bindType :: Type }
  deriving (Eq, Ord, Show)

instance Name.HasName Binding where
  nameOf = bindName
  mapName f b = b { bindName = f (Name.nameOf b) }

instance Name.HasIdent Binding

prettyBindOuter :: Output.HasOutput => Binding -> String
prettyBindOuter b = out (bindName b) ++ " :: " ++ Output.quotes (out (bindType b))

instance Output Binding where
  out b = out (bindName b) ++ " :: " ++ (out (bindType b))