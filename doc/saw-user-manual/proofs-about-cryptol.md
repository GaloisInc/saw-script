# Proofs about Cryptol Models

:::{warning}
This section is under construction!
:::

## Cryptol and its Role in SAW

Cryptol is a domain-specific modeling and specification language.
It is integrated into SAW and used for a broad range of tasks.
Use of SAW for essentially any purpose requires use of Cryptol.
<!-- XXX Update the Cryptol repository to publish a canonical link for this. -->
Thus, the
[Cryptol manual](https://cdn.prod.website-files.com/673b407e535dbf3b547179dd/677c422f88a92701db5a834d_ProgrammingCryptol.pdf)
is an important additional resource for SAW users.

Cryptol is a pure functional language that was originally developed
for specification of cryptographic algorithms and protocols.
It is 
particularly applicable to describing computations that operate on
streams of data of some fixed size.
It is general enough, however, to describe a wide variety of programs.

Typically, complex or nontrivial models will be written as one or more
external Cryptol modules and imported into SAW.
However, Cryptol fragments can also be included directly into SAWScript
via quasiquotation.
<!-- describe how you do this in the python interface -->

However provided, Cryptol code loaded into SAW is translated into
SAWCore.
This makes it possible to combine Cryptol models with other SAW
facilities, and to reason jointly about Cryptol models and other
things at the same time.
For this reason, the most common proof methodology in SAW is to
relate imported code to a Cryptol model.
(The second most common proof methodology is probably to use SAW
to construct proofs _about_ Cryptol models that Cryptol's own proof
facilities cannot handle.)
