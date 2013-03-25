module Verifier.SAW.Prelude.Constants where

import Verifier.SAW.TypedAST

preludeModuleName :: ModuleName
preludeModuleName = mkModuleName ["Prelude"]

preludeNatIdent :: Ident
preludeNatIdent =  mkIdent preludeModuleName "Nat"

preludeZeroIdent :: Ident
preludeZeroIdent =  mkIdent preludeModuleName "Zero"

preludeSuccIdent :: Ident
preludeSuccIdent =  mkIdent preludeModuleName "Succ"

preludeVecIdent :: Ident
preludeVecIdent =  mkIdent preludeModuleName "Vec"

preludeFloatIdent :: Ident
preludeFloatIdent =  mkIdent preludeModuleName "Float"

preludeDoubleIdent :: Ident
preludeDoubleIdent =  mkIdent preludeModuleName "Double"