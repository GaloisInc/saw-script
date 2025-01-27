# Booleans and Bit Vectors

The previous section gave an example of a bit vector operation. The
SAWCore prelude contains a number of built-in operations on both bit
vectors and booleans.

Th `bvNat` function constructs a constant bit vector, of a given size,
from the given natural number. Conversely, the `bvToNat` function
takes a bit vector length, a vector of this length, and returns the
corresponding natural number.

The usual bit vector operators work on one or more bit vectors of a
single vector size. These functions take a natural number as their
first argument, indicating the size of the following bit vectors.

There are a few exceptions to this general pattern. The unsigned bit
vector shifting operations take a natural number as their second
operand. All signed bit vector operations take a natural number one
smaller than the size of their remaining arguments (to ensure that
their arguments have non-zero size). The `bvAppend` operator takes two
natural numbers, corresponding to the lengths of its two bit vector
arguments, and returns a bit vector with length correponding to the
sum of the lengths of its arguments.

The complete collection of bit vector operations appears in the
Reference section at the end of this document.
