(Look at the structs in `test.c` and `tmp/test.ll` to make sense of
this discussion)

In this example we verify a trivial computation on a tagged union, to
answer the question: how do smaller union elements embed into the
union representation (the union is represented by the largest element
in the union; I don't know how ties are resolved)?

Conclusion: the the smaller union element embeds into the beginning
(earlier indices) of the union representation.

The LLVM representation is

```
%struct.st = type { i32, %union.anon }
%union.anon = type { %struct.inc_2_st }
%struct.inc_2_st = type { i32, i32 }
%struct.inc_1_st = type { i32 }
```

and this test concludes that the `i32` in `%struct.inc_1_st` embeds
into the *first* `i32` in `%struct.inc_2_st`.
