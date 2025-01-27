# Inputs and Scalar Constants

The simplest terms in `extcore` refer to external inputs and constant
values. Two types of external inputs exist.

The `ExtCns` keyword indicates an input identified by index, with a
declared type, and a name that exists primarily as a comment. Inputs
of this type are most appropriate when thinking of the term as a
representation of a circuit.

The `Global` keyword indicates a global term identified by name. This
keyword is primarily used to refer to built-in operators, such as
prelude functions that operate on bit vectors.

Constants can be written with one of the keywords `Nat`, `Float`,
`Double`, or `String`, followed by the value of the constant. Bit
vector constants can be created by applying the function described in
the "Bit Vectors" section that converts a natural number to a bit
vector. Later sections describe how to write aggregated or structured
constants.
