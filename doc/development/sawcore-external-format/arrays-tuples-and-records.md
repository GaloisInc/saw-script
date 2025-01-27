# Arrays, Tuples and Records

SAWCore allows aggregation of arbitrary data types into composite
types: arrays, tuples, and records. Arrays are collections, of known
size, containing multiple values of the same type. Tuples contain a
list of values that match, in order, a given list of types. Records
are like tuples with named rather than numbered fields.

For each of these composite forms, SAWCore includes constructs for
building both types and values.

To construct an array type, apply the builtin `prelude.Vec` to the
desired size followed by the type of its elements. To construct an
array value, use the keyword `Array` followed by the node index of its
type, and then all of the node indices of its elements. Bit vectors in
SAWCore are actually just arrays of boolean values.

To construct a tuple type, use the `TupleT` keyword followed by the
indices of the individual element types. To construct a tuple value,
use the `Tuple` keyword followed by the indices of the individual
element values. Finally, to select an element from a tuple value, use
the `TupleSel` keyword followed by the index of the tuple value and
then the element number to extract.

Record types and values are like tuple types and values, except that
each type or value index is preceded by a field name. Record field
selection is identical to tuple element selection except that it uses
a field name instead of an element index.
