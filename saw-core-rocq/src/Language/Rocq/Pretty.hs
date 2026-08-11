{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

{- |
Module      : Language.Rocq.Pretty
Description : Printer for Rocq AST
License     : BSD3
Maintainer  : atomb@galois.com

Converts Rocq AST to prettyprinter documents.
-}

module Language.Rocq.Pretty (prettyDecl) where

import Data.Word
import Data.Text (Text)
import qualified Data.Text as Text
import Numeric (showHex)

import qualified Prettyprinter as PP
import Prettyprinter ((<+>))

import Language.Rocq.AST


------------------------------------------------------------
-- Support

-- | Mark the last entry in a list.
markLast :: [a] -> [(Bool, a)]
markLast xs =
    let once x results = (null results, x) : results in
    foldr once [] xs

-- | Replace all occurrences of the double quote character @"@ with
--   the string @""@, i.e., two copies of it, as this is how Rocq
--   escapes double quote characters.
escapeStringLit :: Text -> Text
escapeStringLit str =
    let oneChar c = if c == '"' then "\"\"" else Text.singleton c in
    Text.concatMap oneChar str

-- | Wrapper for printing arbitrary text
text :: Text -> PP.Doc ann
text s = PP.pretty s

-- | Wrapper for printing integers
integer :: Integer -> PP.Doc ann
integer n = PP.pretty n

-- | Common code to print some names with a type
prettyNamesAndType :: [Ident] -> Type -> PP.Doc ann
prettyNamesAndType names ty =
    let names' = PP.hsep $ map prettyIdent names
        ty' = prettyTerm PrecNone ty
        long = PP.nest 3 $ names' <> ":" <+> ty'
        short = PP.group $ names' <> ":" <+> ty'
    in
    PP.flatAlt long short

-- | Insert parens based on the first argument
parensIf :: Bool -> PP.Doc ann -> PP.Doc ann
parensIf p d = if p then PP.parens d else d


------------------------------------------------------------
-- AST tools

-- | Check if two terms are the \"same\". This is used to fold together
--   forall entries (like @forall (x y: nat)@) and so can be
--   conservative. It does only as much work as needed to make real
--   occurrences work, and calls everything else false. In particular
--   we make no attempt to handle alpha-equivalence.
sameTerm :: Term -> Term -> Bool
sameTerm e1 e2 =
    case (e1, e2) of
        -- Cases we do not handle
        (Lambda{}, _) -> False
        (_, Lambda{}) -> False
        (Fix{}, _) -> False
        (_, Fix{}) -> False
        (Pi{}, _) -> False
        (_, Pi{}) -> False
        (Let{}, _) -> False
        (_, Let{}) -> False
        (Ltac{}, _) -> False
        (_, Ltac{}) -> False

        -- Matching cases we do handle
        (If c1 t1 f1, If c2 t2 f2) ->
            sameTerm c1 c2 && sameTerm t1 t2 && sameTerm f1 f2
        (App f1 args1, App f2 args2) ->
            sameTerm f1 f2 && length args1 == length args2 &&
                and (zipWith sameTerm args1 args2)
        (Sort s1, Sort s2) ->
            s1 == s2
        (Var x1, Var x2) ->
            x1 == x2
        (ExplVar x1, ExplVar x2) ->
            x1 == x2
        (Ascription e1' t1, Ascription e2' t2) ->
            sameTerm e1' e2' && sameTerm t1 t2
        (NatLit n1, NatLit n2) ->
            n1 == n2
        (ZLit n1, ZLit n2) ->
            n1 == n2
        (List xs1, List xs2) ->
            length xs1 == length xs2 && and (zipWith sameTerm xs1 xs2)
        (StringLit s1, StringLit s2) ->
            s1 == s2
        (Scope e1' s1, Scope e2' s2) ->
            s1 == s2 && sameTerm e1' e2'

        -- Fill out the cases so if a new constructor appears the
        -- compiler reminds us to handle it.
        (If{}, _) -> False
        (App{}, _) -> False
        (Sort{}, _) -> False
        (Var{}, _) -> False
        (ExplVar{}, _) -> False
        (Ascription{}, _) -> False
        (NatLit{}, _) -> False
        (ZLit{}, _) -> False
        (List{}, _) -> False
        (StringLit{}, _) -> False
        (Scope{}, _) -> False

-- | Maybe wrapper for sameTerm
sameMaybeTerm :: Maybe Term -> Maybe Term -> Bool
sameMaybeTerm me1 me2 = case (me1, me2) of
    (Nothing, Nothing) -> True
    (Nothing, Just _) -> False
    (Just _, Nothing) -> False
    (Just e1, Just e2) -> sameTerm e1 e2


------------------------------------------------------------
-- AST sugaring

-- | Contracted regular binder.
--
--   Explicit parameters with no type are printed loose: "x"
--   Explicit parameters with a type are grouped by type: "(x y: a)"
--   Implicit parameters are grouped by maybe-type: "{x y}", "{x y: a}".
--
data Binders'
    = ExplicitUntypedBinder' Ident
    | ExplicitTypedBinders' [Ident] Type
    | ImplicitBinders' [Ident] (Maybe Type)

-- | Contracted pi-binder.
--
--   Anonymous pi "binders" are just type names and are printed loose,
--   with or without braces.
--
--   Named pi binders are grouped first by type, and then all together
--   with a single "forall" keyword: "forall (x y: a) {z: b}, ..."
--
data PiBinders'
    = AnonPiBinder' BinderImplicity Type
    | NamedPiBinders' [(BinderImplicity, [Ident], Type)]

-- | Fold together adjacent binders as allowed by the concrete syntax.
contractBinders :: [Binder] -> [Binders']
contractBinders bs0 =
    -- state frobs for when we're looking at implicit binders
    -- (Just $ Left s in the state)
    let newImplicit x mty = ([x], mty)
        addImplicit x mty (prevnames, prevmty) =
            if sameMaybeTerm mty prevmty then
                Just (x : prevnames, prevmty)
            else
                Nothing
        popImplicit (names, mty) =
            ImplicitBinders' (reverse names) mty
    in
    -- state frobs for when we're looking at explicit binders
    -- with types (Just $ right s in the state)
    let newExplicit x ty = ([x], ty)
        addExplicit x ty (prevnames, prevty) =
            if sameTerm ty prevty then
                Just (x : prevnames, prevty)
            else
                Nothing
        popExplicit (names, ty) =
            ExplicitTypedBinders' (reverse names) ty
    in

    -- fold function to do the contraction
    let once (results, state) b = case state of
          Nothing -> case b of
              Binder Implicit x mty ->
                  (results, Just $ Left $ newImplicit x mty)
              Binder Explicit x Nothing ->
                  let here = ExplicitUntypedBinder' x in
                  (here : results, Nothing)
              Binder Explicit x (Just ty) ->
                  (results, Just $ Right $ newExplicit x ty)
          Just (Left s) -> case b of
              Binder Implicit x mty ->
                  case addImplicit x mty s of
                      Nothing ->
                          let prev = popImplicit s in
                          (prev : results, Just $ Left $ newImplicit x mty)
                      Just s' ->
                          (results, Just $ Left s')
              Binder Explicit x Nothing ->
                  let prev = popImplicit s
                      here = ExplicitUntypedBinder' x
                  in
                  (here : prev : results, Nothing)
              Binder Explicit x (Just ty) ->
                  let prev = popImplicit s in
                  (prev : results, Just $ Right $ newExplicit x ty)
          Just (Right s) -> case b of
              Binder Implicit x mty ->
                  let prev = popExplicit s in
                  (prev : results, Just $ Left $ newImplicit x mty)
              Binder Explicit x Nothing ->
                  let prev = popExplicit s
                      here = ExplicitUntypedBinder' x
                  in
                  (here : prev : results, Nothing)
              Binder Explicit x (Just ty) ->
                  case addExplicit x ty s of
                      Nothing ->
                          let prev = popExplicit s in
                          (prev : results, Just $ Right $ newExplicit x ty)
                      Just s' ->
                          (results, Just $ Right s')
    in
    let (results, state) = foldl once ([], Nothing) bs0
        results' = case state of
            Nothing -> results
            Just (Left s) -> popImplicit s : results
            Just (Right s) -> popExplicit s : results
    in
    reverse results'

-- | Type belonging to the internals of `contractPiBinders`.
--
--   (is there no way to put this inside the function?)
type State = ([(BinderImplicity, [Ident], Type)], BinderImplicity, [Ident], Type)

-- | Fold together adjacent pi-binders as allowed by the concrete
--   syntax.
--
--   "Binders" without names can't be folded together, but names that
--   share the same type can be, and a chain of named binders requires
--   only one "forall" token.
contractPiBinders :: [PiBinder] -> [PiBinders']
contractPiBinders bs0 =
    -- State frobs.
    let newstate :: BinderImplicity -> Ident -> Type -> State
        newstate imp x ty = ([], imp, [x], ty)

        addstate :: BinderImplicity -> Ident -> Type -> State -> State
        addstate imp x ty (others, previmp, prevnames, prevty) =
            if imp == previmp && sameTerm ty prevty then
                (others, previmp, x : prevnames, prevty)
            else
                ((previmp, reverse prevnames, prevty) : others, imp, [x], ty)

        popstate :: State -> PiBinders'
        popstate (others, imp, names, ty) =
            let others' = (imp, reverse names, ty) : others in
            NamedPiBinders' $ reverse others'
    in

    -- fold function to do the contraction
    let once :: ([PiBinders'], Maybe State) -> PiBinder -> ([PiBinders'], Maybe State)
        once (results, state) b = case state of
          Nothing -> case b of
              PiBinder imp Nothing ty ->
                  let here = AnonPiBinder' imp ty in
                  (here : results, Nothing)
              PiBinder imp (Just x) ty ->
                  (results, Just $ newstate imp x ty)
          Just s -> case b of
              PiBinder imp Nothing ty ->
                  let prev = popstate s
                      here = AnonPiBinder' imp ty
                  in
                  (here : prev : results, Nothing)
              PiBinder imp (Just x) ty ->
                  let s' = addstate imp x ty s in
                  (results, Just s')
    in
    let (results, state) = foldl once ([], Nothing) bs0
        results' :: [PiBinders']
        results' = case state of
            Nothing -> results
            Just s -> popstate s : results
    in
    reverse results'


------------------------------------------------------------
-- Printers for AST elements

-- | Type to hold the current expression precedence while printing
data Prec
    = PrecNone
    | PrecLambda
    | PrecApp
    | PrecAtom
    deriving (Eq, Ord)

-- | Print an `Ident`
prettyIdent :: Ident -> PP.Doc ann
prettyIdent (Ident s) = text s

-- | Print a `sort`
prettySort :: Sort -> PP.Doc ann
prettySort s = case s of
    Prop -> "Prop"
    Set -> "Set"
    Type -> "Type"

-- | Print an ordinary (lambda/let) binder (group)
prettyBinder' :: Binders' -> PP.Doc ann
prettyBinder' b = case b of
    ExplicitUntypedBinder' x ->
        prettyIdent x
    ExplicitTypedBinders' names ty ->
        PP.group $ PP.parens $ prettyNamesAndType names ty
    ImplicitBinders' names Nothing ->
        let names' = PP.hsep $ map prettyIdent names
            long = PP.nest 3 names'
            short = PP.group names'
            entry = PP.flatAlt long short
        in
        PP.group $ PP.parens entry
    ImplicitBinders' names (Just ty) ->
        PP.group $ PP.braces $ prettyNamesAndType names ty

-- | Print a pi (forall) binder
--   (we don't seem to have a representation for @exists@)
prettyPiBinder' :: PiBinders' -> [PP.Doc ann]
prettyPiBinder' b = case b of
    AnonPiBinder' Explicit ty ->
        [PP.group $ prettyTerm PrecApp ty <+> "->"]
    AnonPiBinder' Implicit ty ->
        [PP.group $ PP.braces (prettyTerm PrecApp ty) <+> "->"]
    NamedPiBinders' entries ->
        let prettyEntry (isLast, (imp, names, ty)) =
              let entry = prettyNamesAndType names ty
                  entry' = case imp of
                      Explicit -> PP.parens entry
                      Implicit -> PP.braces entry
                  entry'' = if isLast then entry' <> "," else entry'
              in
              PP.group entry''
        in
        -- FUTURE: it won't matter for the current downstream uses but
        -- we might want to graft the "forall" keyword to the first
        -- entry instead of letting it float loose.
        let entries' = map prettyEntry $ markLast entries in
        "forall" : entries'

-- | Print a chain of bindings. Contract the chain where syntactically
--   possible, because it's a lot more readable that way.
--
--   The return value is one doc for each contracted group so they can
--   be laid out as desired.
--
prettyBinders :: [Binder] -> [PP.Doc ann]
prettyBinders binders =
    map prettyBinder' $ contractBinders binders

-- | Print a chain of foralls. Contract the chain where syntactically
--   possible, because it's a lot more readable that way.
--
--   The return value is one doc for each contracted group, meaning
--   that each entry under a "forall" keyword is sent back separately,
--   so they can be laid out as desired.
--
prettyPiBinders :: [PiBinder] -> [PP.Doc ann]
prettyPiBinders binders =
    concatMap prettyPiBinder' $ contractPiBinders binders

-- | Common code for printing things shaped like function headers
--
prettyFnHeader ::
    PP.Doc ann -> [PP.Doc ann] -> Maybe (PP.Doc ann) -> PP.Doc ann ->
    PP.Doc ann
prettyFnHeader intro bindings mbRet sep =
    -- Long form
    --    fun x y z ...
    --         a b c ...
    --         : ty
    --       =>
    -- Short form:
    --    fun x : ty =>
    --
    -- (the above where intro is "fun", sep is "=>")
    --
    let firstpieces = intro : bindings
        shortHeader = case mbRet of
            Nothing -> PP.group $ PP.hsep firstpieces <+> sep
            Just ret -> PP.group $ PP.hsep firstpieces <+> ":" <+> ret <+> sep
        longBindings = case mbRet of
            Nothing -> PP.fillSep firstpieces
            Just ret -> PP.fillSep firstpieces <> PP.line <> ":" <+> ret
        longHeader = PP.nest 5 longBindings <> PP.line <> PP.indent 3 sep
    in
    PP.flatAlt longHeader shortHeader

-- | Common code for printing things shaped like functions
--   (@header@ will normally be the result of `prettyFnHeader`)
prettyFunction :: PP.Doc ann -> PP.Doc ann -> PP.Doc ann
prettyFunction header body =
    -- Long form with long argument list and long body:
    --    fun x y z ...
    --         a b c ...
    --       =>
    --       ...
    --       x + 1
    -- Long form with short argument list and long body:
    --    fun x =>
    --       ...
    --       x + 1
    -- Long form with long argument list and short body:
    --    fun x y z ...
    --         a b c ...
    --       => x + 1
    -- Short form:
    --    fun x => x + 1
    --
    let longbody = PP.line <> PP.indent 3 body <> PP.line
        shortbody = PP.group body
        body' = PP.flatAlt longbody shortbody
        long = header <> body'
        short = PP.group $ header <+> body
    in
    PP.flatAlt long short

-- | Print a term
prettyTerm :: Prec -> Term -> PP.Doc ann
prettyTerm p e0 =
  case e0 of
    Lambda binders e1 ->
        let binders' = prettyBinders binders
            e1' = prettyTerm PrecLambda e1
            header = prettyFnHeader "fun" binders' Nothing "=>"
        in
        parensIf (p > PrecLambda) $ prettyFunction header e1'
    Fix ident binders returnType body ->
        let ident' = prettyIdent ident
            binders' = prettyBinders binders
            returnType' = Just $ prettyTerm PrecNone returnType
            body' = prettyTerm PrecLambda body
            intro = "fix" <+> ident'
            header = prettyFnHeader intro binders' returnType' ":="
        in
        parensIf (p > PrecLambda) $ prettyFunction header body'
    Pi binders t ->
        let binders' = prettyPiBinders binders
            t' = prettyTerm PrecLambda t
            longbs = PP.nest 5 $ PP.fillSep binders'
            shortbs = PP.group $ PP.hsep binders'
            finalbs = PP.flatAlt longbs shortbs
            long = finalbs <> PP.line <> PP.indent 5 t'
            short = PP.group $ finalbs <+> t'
        in
        parensIf (p > PrecLambda) $ PP.flatAlt long short
    Let x binders mty t body ->
        let x' = prettyIdent x
            binders' = prettyBinders binders
            mty' = prettyTerm PrecNone <$> mty
            t' = prettyTerm PrecNone t
            body' = prettyTerm PrecLambda body
            intro = "let" <+> x'
            header = prettyFnHeader intro binders' mty' ":="
            longest = PP.vsep [header, PP.indent 3 t', "in", body']
            second = PP.vsep [PP.group (header <+> t' <+> "in"), body']
            shortest = PP.group (header <+> t' <+> "in" <+> body')
            shorter = PP.flatAlt second shortest
        in
        parensIf (p > PrecLambda) $ PP.flatAlt longest shorter
    If c t f ->
        let c' = prettyTerm PrecNone c
            t' = prettyTerm PrecNone t
            f' = prettyTerm PrecLambda f
            first = "if" <+> c' <+> "then"
            long = PP.vsep [first, PP.indent 3 t', "else", PP.indent 3 f']
            short = PP.group (first <+> t' <+> "else" <+> f')
        in
        parensIf (p > PrecLambda) $ PP.flatAlt long short
    App f [] ->
        prettyTerm p f
    App f args ->
        --
        -- The short form of this is obviously "f arg arg arg".
        --
        -- For longer forms, I'd like it to pick either
        --    blahblah
        --    blah f arg arg
        --           arg arg
        -- or
        --    blahblah
        --    blahblah blub blub blub
        --       f arg arg arg
        --         arg
        --
        -- for short f, or
        --    blahblah
        --    blah fffff arg arg
        --            arg arg
        -- or
        --    blahblah
        --    blahblah blub blub blub
        --       fffff arg arg arg
        --          arg
        --
        -- depending on how far off to the right it is. This is
        -- complicated by the fact that PP.width doesn't let you
        -- examine the width of a subdocument without emitting it,
        -- which is annoying and silly of it. (That is, the null
        -- usage of PP.width is "PP.width doc $ \_ -> PP.empty",
        -- not "PP.width doc $ \_ -> doc". The latter prints doc
        -- twice.)
        --
        -- The logic below does the following:
        --    - either indents by the width of f' (and a space) or by 3
        --      (this is in long_a)
        --    - inserts PP.line before f' if we'll be indenting the
        --      args by more than 6 spaces
        --      (this is in long)
        --
        let f' = prettyTerm PrecApp f
            args' = map (\a -> PP.group $ prettyTerm PrecAtom a) args

            short_a = PP.group $ PP.hsep (f' : args')
            short = parensIf (p > PrecApp) short_a

            long_a = PP.width f' $ \w ->
                let w' = if w <= 5 then w + 1 else 3 in
                " " <> PP.nest w' (PP.fillSep args')
            -- This must go here or the line break comes after the
            -- parens, and that's one thing for C but very weird here.
            long_b = parensIf (p > PrecApp) long_a
            long = PP.nesting $ \nest -> PP.column $ \col ->
                if col < nest + 6 then long_b
                else PP.line <> long_b
        in
        PP.flatAlt long short
    Sort s ->
        prettySort s
    Var x ->
        prettyIdent x
    ExplVar x ->
        let x' = prettyIdent x in
        parensIf (p > PrecApp) $ "@" <> x'
    Ascription tm tp ->
        let tm' = prettyTerm PrecApp tm
            tp' = prettyTerm PrecApp tp
            long = PP.nest 5 $ PP.fillSep [tm' <> ":", tp']
            short = PP.group $ tm' <> ":" <+> tp'
        in
        parensIf (p > PrecLambda) $ PP.flatAlt long short
    NatLit i ->
        if i > 1000 then
            -- Explicitly convert from Z if an integer is too big
            parensIf (p > PrecLambda) ("Z.to_nat" <+> integer i <> "%Z")
        else
            integer i
    ZLit i ->
        -- we use hex unless our integer is a positive or negative digit
        -- XXX: this cannot possibly work as intended for negative values
        if abs i > 9 then
            let ui = toInteger (fromInteger i :: Word64)
                ui' = showHex ui []
            in
            text ("0x" <> Text.pack ui' <> "%Z")
        else if i < 0 then
            text ("(" <> Text.pack (show i) <> ")%Z")
        else
            text (Text.pack (show i) <> "%Z")
    List ts ->
        let ts' = PP.punctuate ";" $ map (prettyTerm PrecNone) ts
            long = PP.brackets (PP.line <> PP.indent 3 (PP.vsep ts') <> PP.line)
            short = PP.group $ PP.brackets $ PP.hsep ts'
        in
        PP.flatAlt long short
    StringLit s ->
        PP.dquotes (text $ escapeStringLit s)
    Scope term scope ->
        let term' = prettyTerm PrecAtom term
            scope' = text scope
        in
        term' <> "%" <> scope'
    Ltac s ->
        "ltac:" <> PP.parens (text s)

-- | Print a single constructor
prettyConstructor :: Constructor -> PP.Doc ann
prettyConstructor (Constructor {..}) =
    let name' = prettyIdent constructorName
        ty' = prettyTerm PrecNone constructorType
    in
    PP.nest 5 $ "|" <+> PP.group (name' <> ":" <+> ty')

-- | Print an inductive type declaration
prettyInductive :: Inductive -> PP.Doc ann
prettyInductive (Inductive {..}) =
    let name' = prettyIdent inductiveName
        params' = prettyBinders inductiveParameters
        indices' = prettyPiBinders inductiveIndices
        sort' = prettySort inductiveSort
        ctors' = map prettyConstructor inductiveConstructors
        intro' = "Inductive" <+> name'
        lhs' = case params' of
          [] -> intro' <> ":"
          _ ->
              let short = PP.group $ intro' <+> PP.hsep params' <+> ":"
                  longparams = PP.indent 5 (PP.vsep params')
                  long = PP.vsep [intro', longparams, PP.indent 3 ":"]
              in
              PP.flatAlt long short
        rhs' = case indices' of
          [] -> sort' <+> ":="
          _ ->
              let short = PP.group $ PP.hsep indices' <+> sort' <+> ":="
                  long = PP.nest 5 $ PP.fillSep $ indices' ++ [sort' <+> ":="]
              in
              PP.flatAlt long short
        header = PP.group (lhs' <+> rhs')
    in
    PP.vsep ([header] ++ ctors' ++ ["."])

-- | Common code for the simple declarations
prettyBasicDecl :: PP.Doc ann -> Ident -> Type -> PP.Doc ann
prettyBasicDecl what nm ty =
    let nm' = prettyIdent nm
        ty' = prettyTerm PrecNone ty
        lhs' = PP.group $ what <+> nm' <> ":"
        long = PP.nest 3 $ lhs' <+> ty' <> "."
        short = PP.group $ lhs' <+> ty' <> "."
    in
    PP.flatAlt long short

-- | Print a Definition
prettyDefinition :: Ident -> [Binder] -> Maybe Type -> Term -> PP.Doc ann
prettyDefinition nm params mty body =
    let nm' = prettyIdent nm
        params' = prettyBinders params
        mty' = prettyTerm PrecNone <$> mty
        body' = prettyTerm PrecNone body
        intro' = "Definition" <+> nm'
        lhs' = case params' of
          [] -> intro' <> ":"
          _ ->
              let short = PP.group $ intro' <+> PP.hsep params' <+> ":"
                  longparams = PP.indent 5 (PP.vsep params')
                  long = PP.vsep [intro', longparams, PP.indent 3 ":"]
              in
              PP.flatAlt long short
        rhs' = case mty' of
          Nothing -> ":="
          Just ty' -> ty' <+> ":="
        header = PP.group (lhs' <+> rhs')
    in
    let short = PP.group $ header <+> body' <> "."
        long = PP.nest 3 $ PP.vsep [header, body' <> "."]
    in
    PP.flatAlt long short

-- | Print a top-level declaration
prettyDecl :: Decl -> PP.Doc ann
prettyDecl decl = case decl of
    Axiom nm ty ->
        prettyBasicDecl "Axiom" nm ty <> PP.hardline
    Parameter nm ty ->
        prettyBasicDecl "Parameter" nm ty <> PP.hardline
    Variable nm ty ->
        prettyBasicDecl "Variable" nm ty <> PP.hardline
    Comment s ->
        -- None of the comments we generate are multiline. If that ever
        -- changes, we'll need more logic here to print them properly.
        "(*" <+> text s <+> "*)" <> PP.hardline
    Definition nm binders mty body ->
        prettyDefinition nm binders mty body <> PP.hardline
    InductiveDecl ind ->
        prettyInductive ind <> PP.hardline
    Section nm ds ->
        let nm' = prettyIdent nm
            header = "Section" <+> nm' <> "." <> PP.hardline
            ds' = map prettyDecl ds
            footer = "End" <+> nm' <> "." <> PP.hardline
        in
        -- Note that because every declaration ends with PP.hardline (or
        -- at least PP.line, which we don't group away), we don't need
        -- another one after ds'. Except, without one, the indent for the
        -- declarations bleeds into the footer. (wut?)
        header <> PP.indent 3 (PP.vsep ds') <> PP.hardline <> footer
    Snippet s ->
        -- This assumes all the text snippets we have are multi-line blocks
        -- that include newlines, including at the end.
        --
        -- FUTURE: nothing above this code should ever call PP.group, but if
        -- that changes, we may need to go through the string and manually
        -- replace each \n with PP.hardline.
        text s
