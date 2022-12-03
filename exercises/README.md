# SAW Exercises #

This directory contains exercises to help SAW learners gain confidence in their
proof writing abilities by working on simple, well-defined proofs.  Each
exercise folder contains a well-commented `exercise.saw` file containing
problems to work on, as well as a `solutions.saw` file with a sample solution.
Some exercises have more than one valid solution, though the `solutions.saw`
file will only list one.  We designed the exercises to be completed in
following order:

1. `memory-safety/popcount`
2. `memory-safety/swap`
3. `memory-safety/u128`
4. `memory-safety/point`
5. `functional-correctness/popcount`
6. `functional-correctness/u128`
7. `functional-correctness/point`
8. `functional-correctness/swap`
9. `sha512`

You'll also find a `salsa20` exercise in the `memory-safety` and
`functional-correctness` folders.  Unlike the other exercises, these exercises
lack an `exercise.saw` file.  It is an opportunity to test what you've learned
to write a proof from scratch.  The `salsa20` proofs are simpler than the
`sha512` proof, but the challenge comes from writing a proof without any
signposting or helper functions.

## Continuous Integration (CI) ##

To ensure these exercises stay up to date, we have integrated them with our
CI system.  Our CI runs the `ci-entrypoint.sh` script, which in term runs SAW
over all of the exercises and solutions.  This script is not intended to be
used outside of a CI system.
