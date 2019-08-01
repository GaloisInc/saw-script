Building instructions
=====================

The building process is two-step:

1. One should generate Coq files from their SAWCore/Cryptol counterparts.  This
   can be done in the `saw/` directory, by running the scripts there with an
   appropriate version of the `saw` executable.  The output of such files are
   currently being version-controlled, as a way of keeping track of their
   evolution.

```
/path/to/saw generate_scaffolding.saw
```

2. One can then try and build the Coq files, in the `coq/` directory.  The
   easiest way to do so is to make sure the `_CoqProject` file is up to date,
   and invoke:

```
make clean
coq_makefile -f _CoqProject -o Makefile
make
```

NOTE: `coq_makefile` will fail silently whenever a package listed in it does not
exist!  If you get error messages about missing libraries, double-check the
contents of the file for missing files or typos.

Directory structure
===================

* `coq/` contains handwritten Coq files in `handwritten/` and generated ones in
  `generated/`, as well as some files needed to build the Coq files.

* `cryptol/` contains some Cryptol files that we care about extracting.

* `saw/` contains SAW scripts that generate the Coq files.

Coq files organization
======================

The Coq files have a somewhat complex organization.  We demonstrate the current
dependencies, ignoring transitive dependencies for clarity:

```
                      SAWCoreScaffolding (H)
                          /           \
SAWCoreVectorsAsCoqVectors (H)   SAWCoreVectorsAsCoqLists (H)
                          \           /
  CoqVectorsExtra (H)    SAWCorePrelude (G)
             \            /            \
   CryptolPrimitivesForSAWCore (G)     SAWCorePreludeExtra (H)
                         \               /
               CryptolPrimitivesForSAWCoreExtra (H)

```

(G) stands for generated files, while (H) stands for handwritten files.

* `SAWCoreScaffolding` defines some of SAW core primitive types and values.

* `SAWCoreVectorsAsCoqVectors` and `SAWCoreVectorsAsCoqLists` are two
  realizations of the vector type, the latter ignoring the type index. In
  practice, we have found that the latter is a no-go for proofs unless
  values are packaged with a proof that their length is equal to the index.

* `SAWCorePrelude` is generated from `Prelude.sawcore`, available in the
  `saw-core` project.

* `CoqVectorsExtra` contains facts about vectors that the Coq standard library
  does not provide.

* `CryptolPrimitivesForSAWCore` is generated from `Cryptol.sawcore`, available
  in the `cryptol-verifier` project.

* `SAWCorePreludeExtra` defines useful functions for
  `CryptolPrimitivesForSAWCoreExtra` to use.

* `CryptolPrimitivesForSAWCoreExtra` contains some additional useful
  definitions.
