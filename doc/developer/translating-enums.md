# Translating Cryptol Enum Types into SAWCore.

## Finding the code

The translation of Cryptol to SAWCore is in the [cryptol-saw-core package](../../cryptol-saw-core);
and the core work of translation is in [this module](../../cryptol-saw-core/src/Verifier/SAW/Cryptol.hs).

The recent addition of translating Cryptol enum types into SAWCore is
implemented in that file, two functions in particular:

  * When an enum declaration is seen, the function `genCodeForNominalTypes` is called which
    then calls `genCodeForEnum`.

  * When importing (translating) expressions with the function
    `importExpr` when a case expression is seen, the function `importCase` is called.

Snippits of these are here:

```
-- | genCodeForEnum ... - called when we see an "enum" definition in the Cryptol module.
--    - This action does two things
--       1. Returns the names & definitions of the constructors of the enum.
--          This fit with the code for other nominals, needed because
--          the "rest" of cryptol code to be translated needs to see the
--          onstructors in the Cryptol environments.
--
--       2. It adds many other definitions to the SAWCore environment
--          (in the sc :: SharedContext).  These definitions are only
--          used by other generated sawcore code, so we don't need to
--          return this information back to the Cryptol environment(s).
genCodeForEnum ::
  SharedContext -> Env -> NominalType -> [C.EnumCon] -> IO [(C.Name,Term)]
```

```
-- | importCase - translates a Cryptol case expr to SAWCore: an application
--   of the generated SAWCore ENUMNAME__case function to appropriate arguments.
importCase ::
  SharedContext -> Env ->
  C.Type -> C.Expr -> Map C.Ident C.CaseAlt -> Maybe C.CaseAlt -> IO Term
```

## Design Decisions

Here we capture the design principles and design decisions that the implementation follows.
  * Enums are represented by generic sums (i.e., nested Eithers) in
    SAWCore.
    - It was originally felt that it could result in faster
      development time than the approach of mapping to a SAWCore
      datatype definition.  In hindsight, it was merely trading
      understanding one part of the codebase with another.  We are not
      sure if we gained or lost time with this decision.
    - Mapping to SAWCore datatype defitions would be a future
      improvement, as it gives us injective types (we won't have the
      possibility of two distinct enum types mapping to the same
      SAWCore representation).

  * We prefer 1. over 2. over 3:
    1. Using code in the SAWCore prelude.
    2. Generating (type-correct, type-checked) code that is added to
       the SAWCore environment when we see enum declarations.
    3. Generating code when we see case expressions.

  * When possible we want to be generating common SAWCore abstractions
    and generating code that is generic over the SAWCore `ListSort`
    structure: a (type level) list of types.

## Useful Definitions from the SAWCore Prelude

We will be making heavy use of `ListSort` in the SAWCore prelude:

```
-- A list of types, i.e. `List (sort 0)` if `List` was universe polymorphic
data ListSort : sort 1
  where {
    LS_Nil : ListSort;
    LS_Cons : sort 0 -> ListSort -> ListSort;
  }

```

For which we also make use of

```
listSortGet : ListSort -> Nat -> sort 0;
listSortDrop : ListSort -> Nat -> ListSort;
```

We also use this generic N-ary Sum, `EithersV`

```
-- EithersV (a simpler version of Eithers): A right-nested sequence of
-- Either types, defined as
--   EithersV [] = Void
--   EithersV (tp:tps) = Either tp (EithersV tps)
EithersV : ListSort -> sort 0;
EithersV = ListSort__rec
            (\ (_:ListSort) -> sort 0)
            Void
            (\ (tp:sort 0) (_:ListSort) (rec:sort 0) ->
               (Either tp rec));
```

The eliminator for `EithersV` (the case for this N-Sum) is

```
-- An eliminator for the EithersV type
eithersV : (a:sort 0) -> (es:FunsTo a) -> EithersV (FunsToIns a es) -> a;
```

We will also need this from the prelude:

```
-- Form the multiple arrow type a1 -> ... -> an -> b
arrowsType : ListSort -> sort 0 -> sort 0;
arrowsType as b =
  ListSort__rec (\ (_:ListSort) -> sort 0) b
    (\ (a:sort 0) (_:ListSort) (rec:sort 0) -> a -> rec)
    as;
```

## Translating Enums, by Example.

### NOTE: Representing Products: Abstraction and Representation

In this document, we attempt to focus on the higher level view and not focus
on the SAWCore API details.  However,
 - In the SAWCore prelude, there is no representation for (sort 0
   level) nested (n-ary) products (Tuples are represented as nested
   pairs and are handled by the parser and primitives.)
 - We have some abstractions for this in the SAWCore API (e.g.,
   [SharedTerm.hs](../../saw-core/src/Verifier/SAW/SharedTerm.hs)):
   - `scTuple`
   - `scTupleType`
   - `scTupleSelector` (represents the `tuple . 1` in the concrete syntax)

So as to ignore the details  and allow us to write textual SAWCore in
what follows, we act as if the following is defined for us.

```
TupleType : ListSort -> sort 0;
TupleType = ListSort__rec
          (\ (_:ListSort) -> sort 0)
          UnitType
          (\ (tp:sort 0) (_:ListSort) (rec:sort 0) ->
               (tp * rec));
```

(In the implementation, it's more complicated, and it is inline, not added to the environment.)

### Representing Enums

Here we show the translation, part by part.  We will display the
SAWCore in its textual form.

Here is the cryptol code for the `ETT` (Enum Test Type);

```
enum ETT ts = C1
            | C2 Nat
            | C3 Bool ts
```

We want an example with constructors of 0, 1, and 2+ arity; we also
want it to be polymorphic.  `ETT` is similar to the example [here](../../intTests/test_cryptol_enums/Test2.cry).

Because `ETT` is polymorphic over `ts`, every definition here will
also be polymorphic over `ts`.  We will be representing the enumerated
type as---surprise, surprise---a sum of products.  So, first we define
the three product types for the three constructors:


```
ETT__ArgType_C1_LS (ts : sort 0) : ListSort = LS_Nil;
ETT__ArgType_C2_LS (ts : sort 0) : ListSort = LS_Cons Nat LS_Nil;
ETT__ArgType_C3_LS (ts : sort 0) : ListSort = LS_Cons Bool (LS_Cons ts LS_Nil);
```

Note that we don't distinguish constructors, every constructor is
polymorphic on all the type variables in the *enum* definition. Thus
you see the `(ts : sort 0)` argument in **all** the above definitions.

Next, the representation for each element of the sum will be a product:

```
ETT__ArgType_C1 (ts : sort 0) : sort 0 = TupleType (ETT__ArgType_C1_LS ts);
ETT__ArgType_C2 (ts : sort 0) : sort 0 = TupleType (ETT__ArgType_C2_LS ts);
ETT__ArgType_C3 (ts : sort 0) : sort 0 = TupleType (ETT__ArgType_C3_LS ts);
```

Now we can put the above representations into a list of types (`ListSort`):

```
ETT__LS : sort 0 -> ListSort;
ETT__LS ts = LS_Cons    (ETT__ArgType_C1 ts)
              (LS_Cons  (ETT__ArgType_C2 ts)
               (LS_Cons (ETT__ArgType_C3 ts)
                 LS_Nil));
```

Now, we can define the SAWCore representation of `ETT` as a
polymorphic Sum of Products thus:

```
ETT : (ts : sort 0) -> sort 0;
ETT ts = EithersV (ETT__LS ts);
```

### Constructing Constructors

`Left` and `Right` (with type `Either`) are in the SAWCore prelude,
but it's still very tedious creating all the type arguments to pass.
Note the structure of our three constructors:

```
C1 : (ts : sort 0) -> listSortGet (ETT__LS ts) 0 -> ETT ts;
C1 ts x = Left (listSortGet (ETT__LS ts) 0) (EithersV (listSortDrop (ETT__LS ts) 1))
               x;

C2 : (ts : sort 0) -> listSortGet (ETT__LS ts) 1 -> ETT ts;
C2 ts x =
  Right (listSortGet (ETT__LS ts) 0) (EithersV (listSortDrop (ETT__LS ts) 1))
  (Left (listSortGet (ETT__LS ts) 1) (EithersV (listSortDrop (ETT__LS ts) 2))
   x);

C3 : (ts : sort 0) -> listSortGet (ETT__LS ts) 2 -> ETT ts;
C3 ts x =
 Right   (listSortGet (ETT__LS ts) 0) (EithersV (listSortDrop (ETT__LS ts) 1))
  (Right (listSortGet (ETT__LS ts) 1) (EithersV (listSortDrop (ETT__LS ts) 2))
   (Left (listSortGet (ETT__LS ts) 2) (EithersV (listSortDrop (ETT__LS ts) 3))
   x));
```

### Constructing `case` for `ETT`

Here is the definition of our function that implements `case` for `ETT`:

```
ETT_case  : (ts : sort 0)
         -> (b: sort 0)
         -> (arrowsType (ETT__ArgType_C1_LS ts) b)
         -> (arrowsType (ETT__ArgType_C2_LS ts) b)
         -> (arrowsType (ETT__ArgType_C3_LS ts) b)
         -> ETT ts
         -> b;

ETT_case ts b f1 f2 f3 =
  eithersV b
    (FunsTo_Cons b (ETT__ArgType_C1 ts) (\(x: ETT__ArgType_C1 ts) -> f1)
    (FunsTo_Cons b (ETT__ArgType_C2 ts) (\(x: ETT__ArgType_C2 ts) -> f2 x.1)
    (FunsTo_Cons b (ETT__ArgType_C3 ts) (\(x: ETT__ArgType_C3 ts) -> f3 x.1 x.2)
    (FunsTo_Nil b))));
```

See the prelude for details of `FunsTo(FunsTo_Cons,FunsTo_Nil)`.  But
hopefully this is generally clear from the above defininition.
Note that this definition is polymorphic on `b`, the result of the
case expression, as well as on `ts` the type arguments of `ETT`.

### Translating Crytpol `case` expressions to SAWCore `ETT_case` applications

For a given case in an Expression,
```
  case scrutinee  of
     C1     -> RHS1
     C2 ... -> RHS2
     C3 ... -> RHS3
```
We create an application of `ETT_case` to the proper arguments.
See the code for the gory details, but a couple key things to note are
  * We must determine the type of the `scrutinee`: `ETT T1`
  * We must determine the type of the whole expression, that is `B`

This allows us to apply the type arguments for `ETT_case` giving the following:

```
  ETT_case T1 B (FunsToCons B ...) scrutinee
```

Handling defaults like

```
  case scrutinee  of
     C1     -> RHS1
     _      -> DFLT
```

is a little tricky, we can view the translation of the above, as first translating
away the defaults to the following:

```
  case scrutinee  of
     C1     -> RHS1
     C2 _   -> DFLT
     C3 _ _ -> DFLT
```

And now we would translate the above into a SAWCore `ETT_Case` application that looks like:

```
  ETT_case
    T1                          -- type application, the instantiation of 'a1'
    B                           -- type application, the result of the whole case
    RHS1                        -- deconstructor for C1
    (\(_: Nat)         -> DFLT) -- deconstructor for C2
    (\(_: Bool) (_:T1) -> DFLT) -- deconstructor for C3
                                --  - note the 'a1' has been instantiated to T1
    scrutinee

```

So, without some form of "case defaults" in SAWCore itself, it appears
that we need to be duplicating code (not duplicating work) for `DFLT` in the various
deconstructor functions that use `DFLT`.

For further deatails, refer to the `importCase` function defined
[here](../../cryptol-saw-core/src/Verifier/SAW/Cryptol.hs).
