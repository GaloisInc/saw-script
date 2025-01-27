# Custom Data Types

Several built-in data types, such as records and tuples, have
dedicated syntax within the language. Other data types, however,
including vectors and booleans, are defined as a set of type
constructors and data constructors.

Type constructors, including `Vec` and `Bool`, take zero or more
arguments inline (i.e., they are not applied with the `App` form), and
create a node corresponding to a data type. The `Bool` type
constructor takes no arguments, while the `Vec` constructor takes two,
a natural number representing its size followed by the type index of
its elements.

To create a value of a type specified by one of these type
constructors, apply one of the zero or more data constructors
associated with the type. Each data constructor may take zero or more
arguments.

Boolean values (corresponding to type constructor `Bool`) can be
constructed with the two data constructors `True` and `False`, both of
which take zero arguments.

Values of vector type can be constructed in two ways. The built-in form
`Array` takes a type index (corresponding to the element type) as its
first argument, followed by a sequence of element expression indices.

Alternatively, vector values can be constructed piece-by-piece using
the two data constructors:

- `EmptyVec` which takes a type as an argument and produces a vector
  with zero elements of that type, and

- `ConsVec` which takes a type, a value, a size, and an existing
  vector of that given size, and produces a new vector of size one
  larger, with the given element value at the beginning.

Other type and data constructors exist in the SAWCore prelude, but
they rarely occur in terms exported for analysis by third-party tools.
