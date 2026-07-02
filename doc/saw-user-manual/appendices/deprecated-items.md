# Deprecated Items

This appendix attempts to document the things in SAW that have been
deprecated and removed over recent releases, in more detail than will
fit in the change log and release notes.

## Upcoming

The following elements are expected to be deprecated in SAW 1.6 such
that they will warn when used, but have not yet been tagged:

- The type `SetupValue` (an old name for `LLVMValue`)

- The type `CrucibleMethodSpec` (an old name for `LLVMSpec`)

- The type `CrucibleSetup` (an old name for `LLVMSetup`)

The following experimental element is expected to be deprecated in SAW
1.6 such that it will be hidden by default, but has not yet been
tagged:

- The experimental builtin `crucible_llvm_verify_x86` (an old name for
  `llvm_verify_x86`), which was left in place in SAW 1.5 due to some
  downstream uses that needed to be migrated first.

Migration for all of these is as simple as updating the name.

## Warning When Used

The following elements are currently deprecated and warn when used;
this has happened since SAW 1.5 was released, so they will be that way
in SAW 1.6.
They are expected to be hidden by default in SAW 1.7.

- The `prove_extcore` builtin; you can just use `prove_print` instead
  now.

- The `add_prelude_eqs` and `add_cryptol_eqs` builtins; use
  `add_core_thms` instead.

- The `assume_unsat` builtin, which was informally deprecated years
  ago; use `admit` instead.
  `admit` takes an extra string argument that's supposed to state why
  you're admitting the theorem without proof.

The following elements were deprecated as of SAW 1.5, and currently
warn.
They will be hidden by default when we remove Boolector from
what4-solvers, which will not happen _before_ SAW 1.6; after that
point the time frame depends mostly on the maintenance burden.

- The commands related to the Boolector solver, which has been
  replaced upstream with Bitwuzla.
  All `boolector` commands have equivalent `bitwuzla` commands.

The following elements were deprecated as of SAW 1.5 (or earlier),
currently warn, but are expected to be hidden by default in SAW 1.6:

- The commands related to the CVC4 solver; proofs should be migrated
  to CVC5.
  Each `cvc4` builtin has a corresponding `cvc5` builtin.
  If you have proofs that work with `cvc4` but time out in `cvc5`, and
  you cannot find another solver that can handle them instead, please
  file an issue (with us or CVC5 upstream as seems best).

- The `external_aig_solver` builtin, which was renamed to `arbitrary_aig`.

- The `external_cnf_solver` builtin, which was renamed to `arbitrary_cnf`.

- The `w4_offline_smtlib2` builtin, which was renamed to
  `offline_w4_smtlib2` for consistency.

- The `llvm_struct` builtin; the current name for it is `llvm_alias`,
  because it looks up typedef names.
  If you are trying to create an LLVM struct type from its contents,
  as many historical callers were found to be, you want `llvm_struct_type`
  instead.

- The old `coq` names of the Rocq backend; change `coq` to `rocq`.

- The many old `crucible` names of LLVM backend functions; e.g.
  `crucible_null` is now `llvm_null`.
  Most of these names have been outdated for years.

- Similarly, the `crucible_java_extract` builtin, which is an old
  name for `jvm_extract`.

## Hidden by Default

There are no elements that were deprecated as of SAW 1.5 (or earlier)
and are now hidden by default, with the expectation that they will
be hidden by default in SAW 1.6 and removed in SAW 1.7.

The following elements were deprecated as of SAW 1.4 (or earlier), are
now hidden by default, and will be removed in SAW 1.6:

- The `env` builtin (use the `:env` REPL command instead)

- Certain old `crucible` names for LLVM backend functions that never
  made it past "experimental":
  - `crucible_fresh_cryptol_var`
  - `crucible_alloc_with_size`
  - `crucible_points_to_array_prefix`
  - `crucible_llvm_compositional_extract`
  - `crucible_llvm_array_size_profile`

## Removed

The following elements have been removed entirely:

- The `addsimp'` and `addsimps'` builtins, which added unproven rewrite
  rules to a `Simpset`.
  Don't do that; it's borrowing trouble.
  If you can't prove your rewrite rules, for whatever, reason, use `admit`
  explicitly and then use the ordinary `addsimp` and/or `addsimps` bulitins
  to add them to `Simpset`s.

- The `crucible_setup_val_to_term` builtin.
  This was a partial inverse for `llvm_term`; that is, it turned an
  `LLVMValue` value back to a `Term` if it was one that could be
  represented.
  In general LLVM specs should be written so they lift values from
  `Term` to `LLVMValue` and not the other way around.

- The unused type `JavaSetup`; any stray references to it should be
  changed to `JVMSetup`.

- The `extract_uninterp` builtin.
  This was a way to rewrite a `Term` to make functions uninterpreted
  (generalize it over all functions that are functions in place of
  specific functions with definitions) and also extract the uses of
  those functions for further processing.
  This depended on problematic internal functionality, and also relied
  on being able to identify which applications of a given function are
  actually the same, which is difficult in general and not the right
  approach.

- The Heapster, MRSolver, and Monadify features, which proved
  unmaintainable and inconsistent with efforts to build SAW an
  assurance case.

- The `sbv_uninterpreted` and `read_sbv` builtins and their `Uninterp`
  type.
  This was code for importing from an obsolete file format.

- The `callcc` builtin, whose behavior was erratic, whose internal
  implementation was insupportable, and which had only one known use
  that was itself better done some other way.

Also, the following SAWScript language-level behavior has been removed:

- It used to be possible to update top-level variable bindings by just
  binding the same variable again.
  This would update some uses and not others depending on the
  then-very-dodgy evaluation semantics of SAWScript.
  Now if you bind the same variable again, it just shadows the old
  variable in the namespace and does not replace it.

  For uses that really need the mutability behavior, you can now, at
  the top level only, do `let rebindable ...`, which lets you bind a
  variable that you can update with another `let rebindable ...`, and
  the semantics of the update are predictable.
