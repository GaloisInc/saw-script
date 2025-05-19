# next -- TBA

The way git information gets compiled in (so it can be reported with
e.g. saw --version) has been changed.
You must build with build.sh after git changes for those changes to
show through; builds done directly with cabal will not update the git
info.
(If you really want you can run the update script by hand instead, of
course.)
Note that build.sh is in any case the recommended way to build.

## New Features

* SAW now supports importing Cryptol code that uses enums.

  - One missing feature is supporting case default alternatives where we
    bind the whole scrutinee, such as this example:

        case s of
           C1 ... -> EXP1
           y      -> EXP2 -- 'y' is free in EXP2

    This, more conventional default alternative, *is* supported:

        case s of
           C1 ... -> EXP1
           _      -> EXP2 -- '_' is not used.

    And case expressions that don't need a default case are supported.

* SAW now ships with a `hie.yaml` file for haskell-language-server.

* Add new SAWScript commands `term_eval` and `term_eval_unint`.
  These are like `goal_eval` and `goal_eval_unint` proof tactics
  but work on arbitrary terms rather than proof goals.

* Support `bmux` gates in exported Yosys directly to avoid reliance on `bmuxmap`

* Vacuity checking (`--detect-vacuity`) now correctly reports contradictions in specifications
  for all Crucible backends: LLVM, MIR, and JVM. Previously, vacuous proofs in MIR and JVM
  code could go undetected.


## Bug fixes

* The `head` and `tail` primitives are now implemented in the SAW-Core
  evaluator (#2312).

* Functions imported with `yosys_import` now use a non-reversed bit
  ordering. All bit indices in Yosys JSON files are now treated as
  indexing from the right. Arithmetic operations treat the right-most
  bit (Yosys index 0) as the least significant, and are translated
  without using `reverse`.

* Invoking the Cryptol `error` function in SAW now preserves the error message
  instead of throwing it away.

* Fixed inconsistent type checking of llvm_assert, mir_assert, and jvm_assert
  statements. Previously, the LLVM backend implicitly rejected predicates with
  non-Bit type due to evaluation failures, while MIR and JVM backends allowed
  them through, resulting in confusing errors that differed across backends.

* Fixed inconsistent type checking of `llvm_assert`, `mir_assert`, and
  `jvm_assert` statements. Previously, the LLVM backend implicitly rejected
  predicates of non-Bit type due to evaluation failures, while MIR and JVM
  backends accepted them, leading to backend-specific errors.

## Deprecations

* `llvm_struct` has been marked deprecated.
It is the same as `llvm_alias` and you should use this instead.
(If you were looking for a function to create a struct type from its
contents, that's `llvm_struct_type`.)

# Version 1.3 -- 2025-03-21

This release supports [version
1](https://github.com/GaloisInc/mir-json/blob/master/SCHEMA_CHANGELOG.md#1) of
`mir-json`'s schema.

## New Features

* SAW documentation is now built and deployed as part of CI.
  In the future, this will only happen for the `master` branch and version tags,
  but for the time being also occurs for PR source branches.

* SAW documentation is now under a single Sphinx umbrella, resulting in a
  complete overhaul of the `doc/` directory (#1723). Generally speaking, all
  _content_ has stayed the same, and only organization has changed. Most
  importantly for users, the PDF artifacts included in CI-generated releases
  have different names and render with Sphinx styling.

* The contributor docs have been improved and modernized.

* The saw executable now accepts a -B or --batch option to run a file of
  REPL commands, similar to the -b option in Cryptol.

* Add a `bitwuzla` family of proof scripts that use the Bitwuzla SMT solver.

* Add a `:search` REPL command, which searches the value environment by type.
  For example, to find everything involving the LLVMSetup monad you can do
  `:search (LLVMSetup _)`.

* Add a `:tenv` REPL command, which is like `:env` but prints the type
  environment instead of the variable environment. `:t` is still short
  for `:type`.

* Add `mir_equal` and `jvm_equal` commands, which mirror the `llvm_equal`
  command for the MIR and JVM backends, respectively.

* Explicitly check that the `mir-json` schema version is supported when parsing
  a MIR JSON file. If the version is not supported, it will be rejected. This
  helps ensure that unsupported `mir-json` files do not cause unintended
  results.

* Emit a warning when parsing an LLVM bitcode metadata record that SAW
  does not support. (Previously, SAW would throw a fatal error if this
  occurred, so this change makes SAW more permissive with respect to
  unsupported LLVM versions.)

* The modified copies of the Rust standard libraries that `mir-json` depends on
  (and SAW therefore ingests when performing MIR verification) now live in the
  `mir-json` repo rather than in the `crucible` repo. See the [`mir-json`
  README](https://github.com/GaloisInc/mir-json/blob/master/README.md) for
  details.

## Bug fixes

* An off-by-one error in `listSortDrop` in the SAWCore prelude has
  been fixed (#2241).

* git submodule update --init --recursive no longer causes an infinite
  checkout loop. (However, using --recursive clones a considerable
  number of unnecessary trees and is still not recommended.)

* The saw executable's usage message now fits into a terminal. (#405)

* Invalid verbosity level specifications passed to the saw
  executable's -v (SAWScript verbosity) and -d (simulator verbosity)
  options are now rejected.
  (The previous behavior for -v was to select maximum debug output.
  It is unclear what effect negative verbosity levels might have had
  with -d.)

* SAW now accepts Unicode input beyond characters 0..255, including in
  embedded Cryptol fragments and saw-core modules, and allows the same
  Unicode code points in identifiers as Cryptol.
  It is thus now possible to refer to Cryptol objects whose names
  include extended characters.
  (#2042)

* Function types in records no longer require gratuitous parentheses.
  (#1994)

* Unexpected special-case type behavior of monad binds in the
  syntactic top level has been removed.
  (This was _not_ specifically associated with the TopLevel monad, so
  top-level binds and binds in functions in TopLevel, or in nested
  do-blocks, would behave differently.)
  See issue #2162.

  There are three primary visible consequences.
  The first is that the REPL no longer accepts
  non-monadic expressions.
  These can still be evaluated and printed; just prefix them with
  ```return```.
  (Affordances specifically for the REPL so this is not required there
  may be restored in the future.)

  The second is that statements of the form ```x <- e;``` where ```e```
  is a pure (non-monadic) term used to be (improperly) accepted at the
  top level of scripts.
  These statements now generate a warning.
  This will become an error in a future release and such statements
  should be rewritten as ```let x = e;```.
  For example, ```t <- unfold_term ["reverse"] {{ reverse 0b01 }};```
  should be changed to ```let t = unfold_term ["reverse"] {{ reverse 0b01 }};```.

  The third is that statements of the form ```x <- s;``` or just ```s;```
  where ```s``` is a term in the _wrong_ monad also used to be
  improperly accepted at the top level of scripts.
  These statements silently did nothing.
  They will now generate a warning.
  This will become an error in a future release.
  Such statements should be removed or rewritten.
  For example, it used to be possible to write ```llvm_assert {{ False }};```
  at the top level (outside any specification) and it would be ignored.
  ```llvm_assert``` is only meaningful within an LLVM specification.

* A number of SAWScript type checking problems have been fixed,
  including issues #2077 and #2105.
  Some previously accepted scripts and specs may be rejected and need
  (generally minor) adjustment.
  Prior to these changes the typechecker allowed unbound type variables
  in a number of places (such as on the right-hand side of typedefs, and
  in function signatures), so for example type names contaning typos
  would not necessarily have been caught and will now fail.
  ```typedef t = nonexistent``` was previously accepted and now is not.
  These problems could trigger panics, but there does not appear to have
  been any way to produce unsoundness in the sense of false
  verifications.

* Counterexamples including SMT arrays are now printed with the array
  contents instead of placeholder text.

* Due to the regressions seen in issues #1946 and #1944, the experimental compositional hardware verification work has been reverted.

* Fix a bug in which an LLVM override would fail to apply when matching an
  argument against a string constant.

* Assorted other minor bugs and annoyances have been fixed, and a
  number of error messages have been improved, particularly type errors.

# Version 1.2 -- 2024-08-30

## New Features

* Add `mir_str_slice_value` and `mir_str_slice_range_value` functions, which
  allow taking `&str` slices. For more information, see the documentation in the
  [SAW manual](https://github.com/GaloisInc/saw-script/blob/master/doc/manual/manual.md#string-slices).

* Add `mir_mux_values` command for muxing two MIR values.

* Add support for GHC 9.8.

## Bug fixes

* Fix bug that caused MIR to incorrectly reject overrides with multiple const slice arguments

* Error messages have been improved such that the locations printed with type errors and other diagnostics now have a much stronger connection with reality.

# Version 1.1 -- 2024-02-05

## New Features
* SAW now supports loading and reasoning about Cryptol declarations that make use of numeric constraint guards.  For more information on numeric constraint guards, see the [relavent section of the Cryptol reference manual](https://galoisinc.github.io/cryptol/master/BasicSyntax.html#numeric-constraint-guards).

* Add an experimental `mir_verify` command, along with related utilities for
  constructing specifications for MIR/Rust programs. For more information, see
  the `mir_*` commands documented in the [SAW
  manual](https://github.com/GaloisInc/saw-script/blob/master/doc/manual/manual.md).

* SAW now supports importing Cryptol modules containing [`foreign`
  declarations](https://galoisinc.github.io/cryptol/master/FFI.html). For more
  information, see the
  [manual](https://github.com/GaloisInc/saw-script/blob/master/doc/manual/manual.md#cryptol-and-its-role-in-saw).

* Building on the above feature, SAW now supports automatically
  generating LLVM setup scripts for Cryptol FFI functions with the
  `llvm_ffi_setup` command. For more information, see the [manual](https://github.com/GaloisInc/saw-script/blob/master/doc/manual/manual.md#verifying-cryptol-ffi-functions).

* Ghost state is now supported with the JVM and MIR language backends:
  * The `llvm_declare_ghost_state` command is now deprecated in favor of the
    new `declare_ghost_state` command, as nothing about this command is
    LLVM-specific.
  * Add `jvm_ghost_value` and `mir_ghost_value` commands in addition to the
    existing `llvm_ghost_value` command.

* SAW now includes an experimental `set_solver_cache_path` command, which
  caches the results of tactics which call out to automated provers. This can
  save a considerable amount of time when repeatedly running proof scripts. For
  more information, see the
  [manual](https://github.com/GaloisInc/saw-script/blob/master/doc/manual/manual.md#caching-solver-results).

* Add experimental support for verifying hardware circuits via VHDL and Yosys.
  There is now a family of experimental `yosys_*` commands that support this.
  For more information, see the
  [manual](https://github.com/GaloisInc/saw-script/blob/master/doc/manual/manual.md#analyzing-hardware-circuits-using-yosys).

* Extend `llvm_verify_x86` in order to handle x86 functions that spill arguments
  to the stack.

## Bug fixes

* Fix a bug in which SAW failed to expand type synonyms used in the definition
  of another type synonym.

* Fix a bug in which SAW would fail to load LLVM bitcode files produced by Apple
  Clang on macOS.

* Overall, closed issues #1818, #1822, #1824, #1828, #1834, #1839, #1842,
  #1843, #1847, #1852, #1854, #1856, 1857, #1859, #1864, #1870, #1875, #1883,
  #1884, #1888, #1892, #1894, #1897, #1900, #1909, #1914, #1917, #1923, #1927,
  #1929, #1932, #1938, #1942, #1945, #1961, #1968, #1970, #1973, #1985, #2003,
  and #2005.

* Overall, merged pull requests #1882, #1885, #1889, #1890, #1891, #1893,
  #1898, #1899, #1904, #1905, #1907, #1908, #1911, #1913, #1915, #1916, #1919,
  #1920, #1921, #1922, #1924, #1925, #1928, #1930, #1931, #1933, #1934, #1935,
  #1936, #1937, #1939, #1940, #1941, #1943, #1947, #1948, #1949, #1950, #1951,
  #1952, #1955, #1958, #1959, #1962, #1963, #1969, #1971, #1972, #1974, #1986,
  #1986, #1987, #1991, #1992, #1993, #2001, #2004, #2006, #2007, #2008, #2009,
  #2010, #2011, #2012, #2013, #2014, #2015, #2020, #2021, #2022, and #2024.

# Version 1.0 -- 2023-06-26

## New Features
* SAW now implements Heapster, which allows extracting functional specifications
  of memory-safe C programs to Coq. There is now a family of experimental
  `heapster_*` commands that support this. For more information, refer to the
  [Heapster README](heapster/README.md).

* New commands `enable_what4_eval` and `disable_what4_eval` to enable or
  disable What4 translation for SAWCore expressions during Crucible symbolic
  execution.

* New command `llvm_alloc_sym_init` like `llvm_alloc`, but assume that the
  allocation is initialized with symbolic bytes.  New commands
  `disable_alloc_sym_init_check` and `enable_alloc_sym_init_check` to
  disable or enable the allocation initialization check associated with
  `llvm_alloc_sym_init` during override application.

* New command `set_crucible_timeout` to set the timeout for the SMT solver
  during the LLVM and X86 Crucible symbolic execution. This is used for
  path-sat checks, and sat checks when applying overrides.

* New command `w4_unint_z3_using` like `w4_unint_z3`, but use the given Z3
  tactic.

* A new `llvm_points_to_bitfield` command has been introduced, providing a
  version of `llvm_points_to` that is specifically tailored for structs
  containing bitfields. In order to use `llvm_points_to_bitfield`, one must
  also use the new `enable_lax_loads_and_stores` command, which relaxes some
  of Crucible's assumptions about reading from uninitialized memory. (This
  command also comes with a corresponding `disable_lax_loads_and_stores`
  command.) For more details on how each of these commands should be used,
  consult the "Bitfields" section of the SAW manual.

* A new `llvm_cast_pointer` function has been added that allows users
  to directly specify that a pointer should be treated as pointing to
  a particular type. This mainly affects the results of subsequent
  `llvm_field` and `llvm_elem` calls.  This is especially useful for
  dealing with C `union` types, as the type information provided by
  LLVM is imprecise in these cases.

* A new `llvm_union` function has been added that uses debug
  information to allow users to select fields from `union` types by
  name. This automates the process of manually applying
  `llvm_cast_pointer` with the type of the selected union field. Just
  as with `llvm_field`, debug symbols are required for `llvm_union` to
  work correctly.

* A new highly experimental `llvm_verify_fixpoint_x86` function that
  allows partial correctness verification of loops using loop
  invariants instead of full symbolic unrolling. Only certain very simple
  styles of loops can currently be accommodated, and the user is
  required to provide a term that describes how the live variables in
  the loop evolve over an iteration.

* A new experimental facility for "tagging" proof obligations in
  specifications and later using those tags to make decisions
  in proof tactics. See the new `llvm_setup_with_tag`,
  `goal_has_tags`, and `goal_has_some_tag` commands.

* A new experimental option (toggled via
  `enable_single_override_special_case` and
  `disable_single_override_special_case`) which changes the handling
  for cases where an overriden function has only one override that
  could possibly apply. When the special case handling is enabled,
  preconditions for the override are asserted separately, maintaining
  their individual metadata instead of being combined into a single
  precondition for the entire override. This may be advantageous if
  proving the individual goals is easier than the conjunction of all
  of them, or if different tactics are needed for different subgoals.
  Currently, this option only applies to LLVM verifications.

* Experimental interactive features. Using the new `subshell`
  and `proof_subshell` commands, a user can regain a command-line
  interface in the middle of a running script for experimentation
  and exploration purposes. In addition `callcc` and `checkpoint`
  allow the user to have more flexibility with restoring prior states
  and executing the remaining context of a proof in such an
  interactive session.

* A new experimental `llvm_verify_x86_with_invariant` command that
  allows verification certain kinds of simple loops by using a
  user-provided loop invariant.

* Add a `cvc5` family of proof scripts that use the CVC5 SMT solver.
  (Note that the `sbv_cvc5` and `sbv_unint_cvc5` are non-functional
  on Windows at this time due to a downstream issue with CVC5 1.0.4 and
  earlier.)

* Add experimental support for verifying Rust programs. For more information,
  see the `mir_*` commands documented in the
  [SAW manual](https://github.com/GaloisInc/saw-script/blob/master/doc/manual/manual.md).

## Changes

* A significant overhaul of the SAW proof and tactics system.  Under
  the hood, tactics now manipulate _sequents_ instead of just
  propositions. This allows more the user to specify more precise goal
  rearrangements, and provides a much nicer interface for proof
  exploration (especially with the new `proof_subshell`). There are a
  variety of new tactics that provide the user with control over proof
  steps that is similar to that found in an interactive theorem prover.
  Proofs that do not make use of the new experimental tactics should
  see no substantive changes, so this is expected to be a highly
  backward-compatible change.

* The experimental and rarely-used `goal_assume` tactic has been
  removed. The use case it was targeting is better solved via sequents.

* Support LLVM versions up to 16.

## Bug fixes

* Overall, closed issues #288, #300, #372, #415, #695, #705, #718, #722, #736,
  #737, #738, #739, #740, #1037, #1155, #1259, #1316, #1358, #1409, #1412,
  #1460, #1461, #1462, #1472, #1493, #1494, #1502, #1507, #1520, #1533, #1537,
  #1558, #1561, #1562, #1565, #1566, #1567, #1579, #1584, #1588, #1591, #1601,
  #1618, #1619, #1632, #1635, #1644, #1647, #1662, #1668, #1669, #1678, #1680,
  #1684, #1691, #1702, #1703, #1726, #1741, #1742, #1744, #1748, #1767, #1768,
  #1780, #1784, #1785, #1794, #1801, #1813, #1822, #1824, #1828, #1834, #1839,
  #1847, #1852, #1854, #1856, #1857, #1864, #1870, and #1875.

* Overall, merged pull requests #378, #630, #651, #710, #712, #725, #753, #795,
  #802, #857, #859, #984, #1000, #1002, #1095, #1110, #1117, #1150, #1172,
  #1194, #1273, #1297, #1313, #1359, #1374, #1385, #1386, #1422, #1452, #1467,
  #1469, #1470, #1473, #1474, #1475, #1477, #1478, #1480, #1481, #1482, #1483,
  #1484, #1485, #1486, #1487, #1488, #1489, #1490, #1491, #1495, #1496, #1497,
  #1501, #1503, #1504, #1505, #1506, #1509, #1510, #1511, #1512, #1513, #1514,
  #1515, #1518, #1519, #1521, #1523, #1524, #1525, #1527, #1528, #1529, #1530,
  #1531, #1534, #1535, #1536, #1538, #1539, #1543, #1544, #1545, #1546, #1547,
  #1549, #1550, #1552, #1553, #1554, #1555, #1557, #1559, #1564, #1568, #1574,
  #1576, #1582, #1583, #1587, #1589, #1590, #1592, #1593, #1594, #1596, #1597,
  #1598, #1599, #1600, #1602, #1604, #1605, #1609, #1610, #1614, #1615, #1617,
  #1622, #1624, #1625, #1626, #1627, #1628, #1629, #1630, #1631, #1633, #1634,
  #1636, #1637, #1645, #1648, #1649, #1650, #1651, #1652, #1654, #1655, #1656,
  #1657, #1658, #1659, #1660, #1661, #1666, #1667, #1670, #1671, #1672, #1673,
  #1675, #1679, #1682, #1686, #1687, #1688, #1689, #1690, #1692, #1693, #1694,
  #1695, #1696, #1697, #1698, #1700, #1705, #1708, #1710, #1711, #1712, #1713,
  #1717, #1718, #1722, #1724, #1725, #1727, #1736, #1738, #1739, #1743, #1746,
  #1749, #1750, #1752, #1755, #1756, #1757, #1769, #1770, #1771, #1773, #1774,
  #1775, #1776, #1777, #1778, #1786, #1790, #1792, #1795, #1796, #1797, #1798,
  #1802, #1804, #1806, #1809, #1811, #1815, #1817, #1821, #1829, #1830, #1832,
  #1833, #1835, #1838, #1840, #1841, #1844, #1846, #1849, #1850, #1853, #1855,
  #1858, #1860, #1861, #1862, #1863, #1866, #1871, #1872, #1874, and #1878.

# Version 0.9

## New Features

Several improvements have been made to JVM verification:

* For method specs that do not specify a final value for a field or
  array element, it is now enforced that the method must leave that
  field or element unmodified. This ensures soundness of the resulting
  override for use in compositional verification.

* New JVM setup commands have been introduced for writing partial
  specifications: `jvm_modifies_field`, `jvm_modifies_static_field`,
  `jvm_modifies_elem`, and `jvm_modifies_array`. Used in the
  post-condition section of a spec, these declare that the field or
  array in question may be modified by the method in an unspecified
  manner.

* All `jvm_` functions have all been promoted from "experimental" to
  "current" status, so that `enable_experimental` is no longer
  necessary for JVM verification.

* The RPC API now includes methods for Java verification, as described [here](https://github.com/GaloisInc/saw-script/blob/master/saw-server/docs/SAW.rst#sawjvmload-class-command).

A new `enable_lax_pointer_ordering` function exists, which relaxes the
restrictions that Crucible imposes on comparisons between pointers from
different allocation blocks.

A SAW value of type `Bool` can now be brought into scope in Cryptol expressions
as a value of type `Bit`.

A new `hoist_ifs_in_goal` proof tactic works like `hoist_ifs` but on the
current goal in a proof script.

The verification summaries produced when specifying the `-s` flag now
contain much more detailed information. When producing JSON output (`-f
json`), the tool in the `verif-viewer` directory can be used to
translate it to GraphViz format.

Two new experimental functions can evaluate SAWCore terms into simpler
forms. The `normalize_term` function simplifies the given term by fully
evaluating it with the SAWCore symbolic simulator but keeping it in
SAWCore format. The `extract_uninterp` function allows certain
uninterpreted functions to be replaced with extra inputs and constraints
on those inputs, allowing propositional solvers to prove goals involving
uninterpreted functions.

## Changes

* The linked-in version of ABC (based on the Haskell `abcBridge`
  library) has been removed. During the original planning for this
  removal, we marked commands based on this library as deprecated. In
  the end, we replaced all of them except `cec` with Haskell
  implementations, so no other commands have been removed, and the
  following commands are now "current" again:

    * `abc` (which now is the same as `w4_abc_verilog`)
    * `load_aig`
    * `save_aig`
    * `save_aig_as_cnf`
    * `bitblast`
    * `write_aiger`
    * `write_cnf`

  We have also implemented a `w4_abc_aiger` command that writes a `Term`
  in AIGER format and invokes ABC on it as an external process. This
  should be very similar to the original `abc` command. Note that the
  pure Haskell AIGER and CNF generation code has not been heavily tuned
  for performance, and could likely be made more efficient. Please file
  [issues](https://github.com/galoisinc/saw-script/issues) for
  performance regressions you encounter!

  The removal of the linked-in ABC version means that the `abc` tactic
  now requires an external `abc` executable. You can get this by
  downloading a `with-solvers` package from the releases page, by
  downloading a solver package from the [`what4-solvers`
  repository](https://github.com/GaloisInc/what4-solvers), or by
  building it yourself from the [ABC
  repository](https://github.com/berkeley-abc/abc).

* The LLVM bitcode reader now should support files from any LLVM version
  between 3.6 and 12.

## Bug Fixes

* Overall, closed issues #109, #120, #128, #156, #233, #316, #320, #324,
  #523, #561, #624, #689, #722, #727, #746, #869, #872, #900, #975,
  #982, #1033, #1035, #1045, #1066, #1098, #1120, #1135, #1140, #1144,
  #1147, #1148, #1152, #1166, #1171, #1175, #1182, #1184, #1186, #1211,
  #1224, #1226, #1230, #1256, #1260, #1263, #1269, #1280, #1285, #1299,
  #1307, #1308, #1311, #1318, #1341, #1355, #1367, #1375, #1381, #1388,
  #1389, #1390, #1404, #1411, #1420, #1430, and #1438.

* Overall, merged pull requests #942, #1117, #1185, #1191, #1204, #1205,
  #1206, #1207, #1208, #1209, #1212, #1213, #1214, #1216, #1218, #1219,
  #1267, #1270, #1272, #1274, #1275, #1276, #1278, #1279, #1281, #1282,
  #1283, #1284, #1286, #1288, #1289, #1290, #1292, #1293, #1294, #1295,
  #1297, #1298, #1300, #1309, #1310, #1313, #1315, #1317, #1319, #1320,
  #1321, #1323, #1325, #1327, #1328, #1329, #1330, #1331, #1332, #1334,
  #1335, #1336, #1337, #1342, #1343, #1345, #1346, #1349, #1351, #1356,
  #1357, #1364, #1365, #1366, #1368, #1369, #1370, #1371, #1373, #1374,
  #1378, #1379, #1380, #1384, #1385, #1391, #1392, #1393, #1394, #1396,
  #1397, #1398, #1399, #1401, #1402, #1403, #1405, #1406, #1410, #1413,
  #1414, #1415, #1416, #1422, #1423, #1424, #1426, #1427, #1428, #1429,
  #1431, #1432, #1433, #1434, #1435, #1437, #1439, #1440, #1441, #1443,
  #1444, #1445, #1446, #1448, #1449, #1450, #1451, #1453, #1454, #1455,
  #1456, #1457, #1458, #1459, #1463, #1464, #1465, #1466, and #1468.

# Version 0.8

## New Features

SAW now includes experimental support for verifying Java code using JDK 9 or
later. Verifying Java code that only uses primitive data types is known to work
well, but code that imports certain classes (e.g., `String`) is known to suffer
from issues documented
[here](https://github.com/GaloisInc/crucible/issues/641).

When verifying Java code, the path to Java can be specified with the new
`--java-bin-dirs`/`-b` command-line option. Alternatively, if
`--java-bin-dirs` is not set, then SAW searches the `PATH` to find Java.
When the path to Java is known, SAW can automatically add system-related
JAR files to the JAR path, which eliminates the need to manually specify
these files with `-j`.

The Crucible-based interface to Java verification is now strictly an
improvement over the older code base, with the addition of several
features:

* Performance of JVM verification is significantly better, as a result
  of removing some unnecessary instances of rewriting. This improves
  performance of LLVM verification, as well.

* The new `jvm_static_field_is` function allows describing the contents
  of static variables in method specifications.

* The verification code initializes all JVM classes at the start so that
  initializers don't run at arbitrary intermediate points and clobber
  static field values specified in preconditions. This means, however,
  that any proofs about Java code are under the assumption that all
  class initializers have run before the method under analysis executes.

Now that the Crucible-based verification infrastructure is sufficiently
expressive and performant, we have removed all dependencies on the old
`jvm-verifier` library.

On the LLVM side, SAWScript includes a variety of new functions for
writing specification blocks:

* The `llvm_struct_type` and `llvm_packed_struct_type` functions each
  construct an LLVM struct type from a list of other LLVM types. This is
  not to be confused with the existing `llvm_struct` function, which
  takes a string as an argument and returns the corresponding alias type
  (which is often, but not necessarily, defined as a struct type).

* To avoid confusion, a new `llvm_alias` function now exists, and
  `llvm_struct` is now a synonym for `llvm_alias`. The `llvm_struct`
  function continues to be available for now.

* The `llvm_pointer : LLVMType -> LLVMType` function allows construction
  of arbitrary LLVM pointer types.

* Two new functions, `llvm_points_to_at_type` and
  `llvm_conditional_points_to_at_type`, mirror `llvm_points_to` and
  `llvm_conditional_points_to`, but cast the pointer to a different
  type. This may be useful when reading or writing a prefix of a larger
  array, for example.

* Support for using ABC as an external process is more complete:

    * SAW can now generate Verilog with multiple outputs (from `Term`
      values that have tuple or vector result types, for example).

    * The new commands `write_aig_external` and `write_cnf_external`
      generate AIG and CNF files, respectively, by first writing Verilog
      and then using the available `abc` executable to bit-blast to the
      lower-level representation. Corresponding proof tactics,
      `offline_aig_external` and `offline_cnf_external` also exist.

These changes are in preparation for removing the linked-in copy of ABC
in a future release.

The `saw-remote-api` RPC server and associated Python client now have
more complete support for LLVM verification, including:

* More complete points-to declarations, matching what is currently
  available in SAWScript.

* Support for more provers, including the full range of SBV-based and
  What4-based provers available in SAWScript.

* Support for ghost variables.

* Support for assuming LLVM contracts directly (rather than the previous
  behavior which would temporarily assume that failed verifications
  succeeded to determine whether higher-level verifications would still
  succeed).

* Support for global variables and initializers.

* Support for null pointers.

* Support for array value literals.

* Support for specifying the value of individual struct fields and array
  elements.

* Support for specifying the alignment of allocations.

Docker images for SAW are now located on
[GitHub](https://github.com/orgs/galoisinc/packages/container/package/saw)
instead of [DockerHub](https://hub.docker.com/r/galoisinc/saw/).

## Changes

The proof management infrastructure in SAWScript is simpler and more
consistent than before. Many of these changes are internal, to make the
code less error-prone and easier to maintain in the future. Several are
user-facing, though:

* The `caseProofResult` command now passes a `Theorem` argument to the
  first function argument, allowing its use as a rewrite rule, for
  example.

* A new `admit` tactic exists, which takes a `String` argument
  describing why the user has decided omit proof of the goal. This
  replaces the `assume_unsat` and `assume_valid` tactics, which we now
  recommend against. They will be officially deprecated in a future
  release, and removed after that.

* Prover tactics (e.g., `yices`) now return `ProofScript ()` instead of
  `ProofScript SatResult`.

* `Simpset`s can now contain "permutative" rewrite rules, where a rule
  is permutative if each side of the equality could represent the same
  set of terms and therefore the rule could repeatedly apply forever. A
  term ordering is used to prevent looping when these rules are applied.

## Bug Fixes

* Verilog generated from rotation operations is now in correct Verilog
  syntax.

* Closed issues #9, #25, #39, #41, #54, #55, #69, #81, #90, #92, #124,
  #136, #144, #149, #152, #159, #271, #285, #323, #353, #377, #382,
  #431, #446, #631, #652, #739, #740, #861, #901, #908, #924, #930,
  #951, #962, #971, #985, #991, #993, #994, #995, #996, #1003, #1006,
  #1009, #1021, #1022, #1023, #1031, #1032, #1050, #1051, #1052, #1055,
  #1056, #1058, #1061, #1062, #1067, #1073, #1083, #1085, #1090, #1091,
  #1096, #1099, #1101, #1119, #1122, #1123, #1127, #1128, #1132, #1163,
  and #1164.

# Version 0.7

## New Features

SAW can now use the ABC prover as an external process in addition to the
linked-in version. This change is in preparation for removing the
linked-in version in a future release. This change has several parts:

* The new proof tactics `w4_abc_verilog` and `w4_abc_smtlib2` allow
  using ABC to discharge proof goals using either Verilog or SMT-Lib2 as
  the intermediate file format, respectively.
* The new `offline_verilog` tactic writes a proof goal in the subset of
  Verilog supported by ABC, which can allow the use of custom ABC
  commands to discharge it.
* The new `w4_offline_smtlib2` writes a proof goal in SMT-Lib2 syntax
  using What4 instead of SBV.
* The new `write_verilog` command will write a `Term` to a file in
  Verilog syntax from the top level of a script.
* The new `write_smtlib2_w4` command will write a `Term` to a file in
  SMT-Lib2 syntax from the top level of a script, using What4 instead of
  SBV.
* The new proof tactics `sbv_abc`, `sbv_boolector`, `sbv_cvc4`,
  `sbv_mathsat`, `sbv_yices`, `sbv_z3`, `sbv_unint_cvc4`,
  `sbv_unint_yices`, and `sbv_unint_z3` are now aliases for the same
  tactics without the `sbv_` prefixes in preparation for making the
  unprefixed tactics refer to the What4 versions of the same
  functionality.

Java verification using the Crucible symbolic execution engine is now
more flexible and performant.

* The new `jvm_array_is` command specifies the entire contents of an
  array together.
* The new `jvm_field_is` command allows disambiguation by type for
  fields of the same name but different types.
* JVM method names can be disambiguated using type descriptors.
* JVM constructors can be referred to by the name `<init>`.
* Error messages in JVM verification are significantly more helpful.

These changes, and various internal performance improvements, mean that
the ECDSA verification example included with SAW now runs in around 5
minutes on a modern laptop.

New features exist to summarize any verifications performed with SAW.
The `summarize_verification` command will print a list of all functions
or methods verified or assumed, and all lemmas proved with commands such
as `prove`. These summaries include the status (verified or assumed) of
each item along with the provers used to complete the proof. The `-s
<filename>` flag will instruct SAW to automatically write a summary to
the given file, and the `-f <format>` flag will instruct SAW to use
either a human-readable (`pretty`) format or JSON (`json`) for
consumption by other tools.

An experimental RPC server for SAW now exists, which provides an
alternative to SAWScript for controlling SAW execution. A client library
for interacting with the server from Python exists
[here](https://github.com/GaloisInc/argo/tree/master/python).

Verification of x86 code called from LLVM is now more flexible. The
`add_x86_preserved_reg` command can add a specific register to the set
that is assumed to be callee-saved, and path satisfiability checking is
now performed when passing `True` as the fifth argument to
`crucible_llvm_verify_x86`.

The new `cryptol_add_path` command adds a directory to the search path
used when loading Cryptol modules (and following imports within
explicitly-loaded modules).

New, shorter names are available for all LLVM commands starting with
the `crucible_` prefix. The new names use the `llvm_` prefix instead.
The top-level function `crucible_llvm_verify` is now `llvm_verify`,
and `crucible_llvm_unsafe_assume_spec` is `llvm_unsafe_assume_spec`.
The old names are still supported for now. The in-REPL documentation
(`:? <command>`) gives the new name for each command.

Shorter names are available for some saw-script types: `CrucibleSetup`
is now `LLVMSetup`, `CrucibleMethodSpec` is now simply `LLVMSpec`, and
`JVMMethodSpec` is `JVMSpec`. The old type names are still supported
for backward compatibility.


## Bug Fixes

* Catch more exceptions at the REPL (issues #138, #560, #745, and #814).
* Ensure global memory is immutable in x86 verification.
* Fix path sat checking (issues #683 and #723).

* Closed issues #61, #138, #158, #162, #212, #215, #265, #314, #319,
  #399, #412, #422, #439, #456, #544, #560, #562, #683, #686, #719,
  #723, #745, #814, #844, #845, #856, #866, #874, #888, #901, #902,
  #904, #911, #920, #936, #937, #945, and #957.

# Version 0.6

## New Features

* Adedd experimental support for _compositional extraction_.
  Previously, `crucible_llvm_extract` and similar functions could
  translate very simple imperative functions into `Term` models but
  analysis of more complex programs typically required verification of
  equivalence to Cryptol specifications. Now, the
  `crucible_llvm_compositional_extract` function allows extraction of
  any function that can be specified using a `CrucibleSetup` block of the
  sort used for `crucible_llvm_verify`. In addition, this extraction can
  be _compositional_, preserving the call structure that exists in the
  original program instead of inlining everything.

* Added experimental support for interactive offline proofs using Coq.
  The `write_coq_term` function and `offline_coq` tactic will export the
  associated `Term` to a file in Gallina syntax. This file can be
  imported into a Coq file that can do arbitrarily complex interactive
  proofs.

* Added experimental support for arrays of symbolic size. The new
  `crucible_array_alloc` function specifies the existence of an
  allocated array where the size is given by its `Term` argument. The
  new `crucible_points_to_array_prefix` function specifies that the
  given pointer points to (the prefix of) a symbolic array value of
  a given symbolic size.

* Improved x86 verification capabilities. Verification scripts for x86
  functions can now process functions with mutable globals and function
  calls (which are currently inlined), and can use proof scripts to
  discharge proof obligations.

* Added a new `llvm_sizeof` primitive, which works similarly to the
  `sizeof` operator in C.

* Added support for the `llvm.fshl.i32` funnel shift intrinsic.

* Added experimental support for _verification summaries_. These
  summaries list all verifications performed within a script in a
  concise way that can track arbitrarily complex proof orchestrations.
  Future releases will include more information in these summaries, and
  more textual explanation of the assumptions made during each proof.

## Other Changes

* Made small improvements to documentation and error messages
  throughout.

* Improved the performance of expression hashing (closing #674).

* Updated to include Cryptol 2.9.1 and all the associated changes.

## Bug Fixes

* Fixed handling of jumps in x86 verification.

* Fixed matching for points-to and return values for x86.

* Closed issues #140, #195, #225, #226, #387, #538, #542, #543, #556,
  #635, #640, #642, #674, #691, #693, #698, #699, #700, #701, #702,
  #704, #706, #707, #709, #720, #721, #730, #742, #744, #763, #768,
  #773, #783, #785, #789, #782, #803, #807, and #815.

# Version 0.5

## New Features

* Added experimental support for basic, non-compositional verification
  of x86 machine code for use in conjunction with LLVM verification.

        crucible_llvm_verify_x86 :
          LLVMModule -> String -> String ->
          [(String, Int)] -> Bool -> CrucibleSetup () ->
          TopLevel CrucibleMethodSpec

  The first argument specifies the LLVM module containing the _caller_.
  The second and third specify the ELF file name and symbol name of the
  function to be verifier. The fourth specifies the names and sizes (in
  bytes) of global variables to initialize, and the fifth whether to
  perform path satisfiability checking. The last argument is the LLVM
  specification of the calling context against which to verify the
  function.

* Added support for using the SMT theory of arrays in the LLVM memory
  model. In some cases, this can significantly improve performance.

        enable_smt_array_memory_model : TopLevel ()
        disable_smt_array_memory_model : TopLevel ()

* Added support for specifying alignment in LLVM allocations. The
  `crucible_alloc_aligned` and `crucible_alloc_readonly_aligned`
  functions allocate read-write and read-only memory regions,
  respectively, with the specified alignment (in bytes).

* Added a conditional points-to function,
  `crucible_conditional_points_to`, that allows an LLVM function to
  conditionally modify memory, leaving it in its previous state
  (potentially uninitialized) when the condition is false.

* Added several new options:

    * New functions `enable_what4_hash_consing` and
      `disable_what4_hash_consing` to enable or disable hash consing to
      increase sub-formula sharing during symbolic execution.

    * New functions `enable_crucible_assert_then_assume` and
      `disable_crucible_assert_then_assume` to control whether
      predicates are assumed after asserting them during symbolic
      execution. The default is now to not assume them, whereas
      previously they were assumed.

    * New command-line option `--no-color` to print an ASCII logo
      without ANSI color or Unicode.

## Performance Improvements

* Improved performance of the LLVM memory model.

* Improved performance of bitvector operations during symbolic execution.

* Improved performance of rewriting SAWCore terms.

## Bug Fixes

* Fixed SBV interface to fail more gracefully when it cannot find the
  solver executable.

* Fixed SMT-Lib export negation issues.

Fixes issues #286, #489, #491, #564, #580, #583, #585, #586, #587, #590,
 #592, #594, #597, #598, #602, #603, #612, #613, #622, #626, #633, #638,
 #639, and #647.

# Version 0.4

* Fixed a long-standing soundness issue (#30) in compositional
  verification of LLVM programs. Previously, a specification for a
  function that neglected to mention an effect that the function in fact
  caused could be successfully verified. When verifying a caller of that
  function, only the effects mentioned in the specification would be
  used. The fix for this issue may break some proof scripts: any pointer
  mentioned using `crucible_points_to` in the initial state of a
  specification but not in the final state will be assigned a final
  value of "invalid", and any subsequent reads from the pointer will
  fail. To fix this issue, make sure that every specification you use
  provides a final value for every pointer it touches (which in many
  cases will be the same as its initial value).

* Added an experimental command, `llvm_boilerplate`, that emits skeleton
  function specifications for every function defined in an LLVM module.
  The additional `crucible_llvm_array_size_profile` command can be used
  to refine the results of `llvm_boilerplate` based on the array sizes
  used by calls that arise from a call to the named top-level function.

* Added support for using the symbolic execution profiler available in
  Crucible. The `enable_crucible_profiling` command causes profiling
  information to be written to the given directory. This can then be
  visualized using the rendering code available
  [here](https://github.com/GaloisInc/sympro-ui).

* Added proof tactics to use Yices (`w4_unint_yices`) and CVC4
  (`w4_unint_cvc4`) through the What4 backend instead of SBV.

* Modified the messages emitted for failed points-to assertions to be in
  terms of LLVM values.

* Added support for using the SMT array memory model to reason about the
  LLVM heap. The `enable_smt_array_memory_model` command enables it for
  all future proofs.

* LLVM bitcode format support is improved. Versions 3.5 to 9.0
  are known to be mostly well-supported. We consider parsing failures
  with any version newer than 3.5 to be a bug, so please report them on
  [GitHub](https://github.com/GaloisInc/saw-script/issues/new).

* New experimental model counting commands `sharpSAT` and `approxmc`
  bind to the external tools of the same name. These were mistakenly
  listed as included in 0.3.

* Built against Cryptol 2.8.0.

* Improved error messages in general.

* Fixed various additional bugs, including #211, #455, #479, #484, #493,
  #496, #511, #521, #522, #534, #563

# Version 0.3

* Java and LLVM verification has been overhauled to use the new Crucible
  symbolic execution engine. Highlights include:

    * New `crucible_llvm_verify` and `crucible_llvm_extract` commands
      replace `llvm_verify` and `llvm_extract`, with a different
      structure for specification blocks.

    * LLVM verification tracks undefined behavior more carefully and has
      a more sophisicated memory model. See the
      [manual](https://github.com/GaloisInc/saw-script/blob/master/doc/manual/manual.md#specification-based-verification)
      for more.

    * New, experimental `crucible_jvm_verify` and
      `crucible_java_extract` commands will eventually replace
      `java_verify` and `java_extract`. For the moment, the former two
      are enabled with the `enable_experimental` command and the latter
      two are enabled with `enable_deprecated`.

    * More flexible specification language allows convenient description
      of functions that allocate memory, return arbitrary values, expect
      explicit aliasing, work with NULL pointers, cast between pointers
      and integers, or work with opaque pointers.

    * Ghost state is supported in LLVM verification, allowing reasoning
      about certain complex or unavailable code.

    * Verification of LLVM works for a larger subset of the language,
      which particularly improves support for C++.

* LLVM bitcode format support is greatly improved. Versions 3.5 to 7.0
  are known to be mostly well-supported. We consider parsing failures
  with any version newer than 3.5 to be a bug, so please report them on
  [GitHub](https://github.com/GaloisInc/saw-script/issues/new).

* Greatly improved error messages throughout.

* Built against Cryptol 2.7.0.

* New model counting commands `sharpSAT` and `approxmc` bind to the
  external tools of the same name.

* New proof script commands allow multiple goals and related proof
  tactics. See the
  [manual](https://github.com/GaloisInc/saw-script/blob/master/doc/manual/manual.md#multiple-goals).

* Can be built with Docker, and will be available on DockerHub.

* Includes an Emacs mode.

# Version 0.2-dev

* Released under the 3-clause BSD license

* Major improvements to the Java and LLVM verification infrastructure,
  as described in more detail [here](doc/java-llvm/java-llvm.md):
    * Major refactoring and polish to `java_verify` and `java_symexec`
    * Major refactoring and polish to `llvm_verify` and `llvm_symexec`
    * Fixed soundness bug in `llvm_verify` treatment of heap
      modifications
    * Fixed soundness bug related to `java_assert` and `llvm_assert`
    * Support for branch satisfiability checking to be configured
    * Support for some types of allocation in `java_verify`, enabled
      with `java_allow_alloc`
    * Improved support for LLVM structs (including the `llvm_struct`
      type for `llvm_verify`)
    * Support for non-scalar return values in `java_verify` and
      `java_symexec`
    * Support for using `java_ensure_eq` on fields of return value
    * Access to safety conditions in `java_symexec` and `llvm_symexec`
    * New primitives `llvm_assert_eq` and `java_assert_eq`

* Some changes to the SAWScript language:
    * Conditional expressions including the keywords `if`, `then`, and
      `else`, and the new constants `true` and `false`
    * New `eval_int` and `eval_bool` functions to expose Cryptol bit
      vectors and `Bit` values as `Int` and `Bool` values in SAWScript
    * Pattern matching for tuples
    * Improvements to pretty printing, including: `set_base` and
      `set_ascii` commands to control the formatting of values; a `show`
      function to convert a value to a string without printing it; and
      the ability to use `print` or `show` instead of
      `llvm_browse_module` and `java_browse_class`
    * New built-in functions for processing lists

* New proof backends:
    * A new `rme` proof tactic, based on the
      [Reed-Muller Expansion](https://en.wikipedia.org/wiki/Reed%E2%80%93Muller_expansion)
      normal form for propositional formulas. This tactic is
      particularly efficient for dealing with polynomials over Galois
      fields, as used in AES, for instance.

* Linked against the latest Cryptol code, which includes the following
  changes since release 2.3.0:
    * An extended prelude with more Haskell-like functions
    * Better, more portable seeding for `random`
    * Performance improvements for symbolically executing tables of
      constant values
    * Performance improvements for type checking large constants

* Internal improvements:
    * Simplified Cryptol to SAWCore translation
    * Improved performance of Cryptol to SAWCore translation for
      recursive functions
    * Updated bitcode parser to support some of the changes in LLVM 3.7
    * Many bug fixes
    * Many code cleanups
