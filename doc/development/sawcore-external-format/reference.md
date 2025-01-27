# Reference

This section summarizes the built-in types, boolean functions, and bit
vector functions defined in the SAWCore prelude. These types and
functions will apppear in `extcore` files in the form
`Prelude.<name>`, but are listed below in the form `<name>`, without
the `Prelude` prefix, for brevity and readability.

## Prelude types

| Name        | Kind                  | Comments                      |
| ----------- | --------------------- | ----------------------------- |
| `Bool`      | `Type`                |                               |
| `Nat`       | `Type`                |                               |
| `bitvector` | `Nat -> Type`         | Abbreviation for `Vec n Bool` |
| `Vec`       | `Nat -> Type -> Type` |                               |
| `String`    | `Type`                |                               |

## Prelude boolean functions

| Name     | Type                              |
| -------- | --------------------------------- |
| `and`    | `Bool -> Bool -> Bool`            |
| `or`     | `Bool -> Bool -> Bool`            |
| `xor`    | `Bool -> Bool -> Bool`            |
| `boolEq` | `Bool -> Bool -> Bool`            |
| `not`    | `Bool -> Bool`                    |
| `ite`    | `(a:Type) -> Bool -> a -> a -> a` |

## Prelude bit vector functions

| Name      | Type                                                                     |
| --------- | ------------------------------------------------------------------------ |
| `msb`     | `(n:Nat) -> bitvector (n + 1) -> Bool`                                   |
| `bvNat`   | `(n:Nat) -> Nat -> bitvector n`                                          |
| `bvToNat` | `(n:Nat) -> bitvector n -> Nat`                                          |
| `bvAdd`   | `(n:Nat) -> bitvector n -> bitvector n -> bitvector n`                   |
| `bvSub`   | `(n:Nat) -> bitvector n -> bitvector n -> bitvector n`                   |
| `bvMul`   | `(n:Nat) -> bitvector n -> bitvector n -> bitvector n`                   |
| `bvUDiv`  | `(n:Nat) -> bitvector n -> bitvector n -> bitvector n`                   |
| `bvURem`  | `(n:Nat) -> bitvector n -> bitvector n -> bitvector n`                   |
| `bvSDiv`  | `(n:Nat) -> bitvector (n + 1) -> bitvector (n + 1) -> bitvector (n + 1)` |
| `bvSRem`  | `(n:Nat) -> bitvector (n + 1) -> bitvector (n + 1) -> bitvector (n + 1)` |
| `bvAnd`   | `(n:Nat) -> bitvector n -> bitvector n -> bitvector n`                   |
| `bvOr`    | `(n:Nat) -> bitvector n -> bitvector n -> bitvector n`                   |
| `bvXor`   | `(n:Nat) -> bitvector n -> bitvector n -> bitvector n`                   |
| `bvNot`   | `(n:Nat) -> bitvector n -> bitvector n`                                  |
| `bvShl`   | `(n:Nat) -> bitvector n -> Nat -> bitvector n`                           |
| `bvShr`   | `(n:Nat) -> bitvector n -> Nat -> bitvector n`                           |
| `bvSShr`  | `(n:Nat) -> bitvector (n + 1) -> bitvector n -> bitvector (n + 1)`       |
