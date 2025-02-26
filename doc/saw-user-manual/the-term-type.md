# The Term Type

Perhaps the most important type in SAWScript, and the one most unlike
the built-in types of most other languages, is the `Term` type.
Essentially, a value of type `Term` precisely describes all
possible computations performed by some program. In particular, if
two `Term` values are *equivalent*, then the programs that they
represent will always compute the same results given the same inputs. We
will say more later about exactly what it means for two terms to be
equivalent, and how to determine whether two terms are equivalent.

Before exploring the `Term` type more deeply, it is important to
understand the role of the Cryptol language in SAW -- make sure to read
[that section of the manual](./cryptol-and-its-role-in-saw) before continuing.
