# Analyzing Hardware Circuits using Yosys

SAW has experimental support for analysis of hardware descriptions written in VHDL ([via GHDL](https://github.com/ghdl/ghdl-yosys-plugin)) through an intermediate representation produced by [Yosys](https://yosyshq.net/yosys/).
This generally follows the same conventions and idioms used in the rest of SAWScript.

## Processing VHDL With Yosys

Given a VHDL file `test.vhd` containing an entity `test`, one can generate an intermediate representation `test.json` suitable for loading into SAW:

:::{code-block} console
$ ghdl -a test.vhd
$ yosys
...
Yosys 0.10+1 (git sha1 7a7df9a3b4, gcc 10.3.0 -fPIC -Os)
yosys> ghdl test

1. Executing GHDL.
Importing module test.

yosys> write_json test.json

2. Executing JSON backend.
:::

It can sometimes be helpful to invoke additional Yosys passes between the `ghdl` and `write_json` commands.
For example, at present SAW does not support the `$pmux` cell type.
Yosys is able to convert `$pmux` cells into trees of `$mux` cells using the `pmuxtree` command.
We expect there are many other situations where Yosys' considerable library of commands is valuable for pre-processing.

## Example: Ripple-Carry Adder

Consider three VHDL entities.
First, a half-adder:

:::{code-block} vhdl
library ieee;
use ieee.std_logic_1164.all;

entity half is
  port (
    a : in std_logic;
    b : in std_logic;
    c : out std_logic;
    s : out std_logic
  );
end half;

architecture halfarch of half is
begin
  c <= a and b;
  s <= a xor b;
end halfarch;
:::

Next, a one-bit adder built atop that half-adder:

:::{code-block} vhdl
library ieee;
use ieee.std_logic_1164.all;

entity full is
  port (
    a : in std_logic;
    b : in std_logic;
    cin : in std_logic;
    cout : out std_logic;
    s : out std_logic
  );
end full;

architecture fullarch of full is
  signal half0c : std_logic;
  signal half0s : std_logic;
  signal half1c : std_logic;
begin
  half0 : entity work.half port map (a => a, b => b, c => half0c, s => half0s);
  half1 : entity work.half port map (a => half0s, b => cin, c => half1c, s => s);
  cout <= half0c or half1c;
end fullarch;
:::

Finally, a four-bit adder:

:::{code-block} vhdl
library ieee;
use ieee.std_logic_1164.all;

entity add4 is
  port (
    a : in std_logic_vector(3 downto 0);
    b : in std_logic_vector(3 downto 0);
    res : out std_logic_vector(3 downto 0)
  );
end add4;

architecture add4arch of add4 is
  signal full0cout : std_logic;
  signal full1cout : std_logic;
  signal full2cout : std_logic;
  signal ignore : std_logic;
begin
  full0 : entity work.full port map (a => a(0), b => b(0), cin => '0', cout => full0cout, s => res(0));
  full1 : entity work.full port map (a => a(1), b => b(1), cin => full0cout, cout => full1cout, s => res(1));
  full2 : entity work.full port map (a => a(2), b => b(2), cin => full1cout, cout => full2cout, s => res(2));
  full3 : entity work.full port map (a => a(3), b => b(3), cin => full2cout, cout => ignore, s => res(3));
end add4arch;
:::

Using GHDL and Yosys, we can convert the VHDL source above into a format that SAW can import.
If all of the code above is in a file `adder.vhd`, we can run the following commands:

:::{code-block} console
$ ghdl -a adder.vhd
$ yosys -p 'ghdl add4; write_json adder.json'
:::

> **Side Note:** this assumes the ghdl plugin was properly installed, see https://github.com/ghdl/ghdl-yosys-plugin
> for installation details.

The produced file `adder.json` can then be loaded into SAW with `yosys_import`.

> **Side Note:** different versions of Yosys and GHDL may produce slightly different naming for the inner modules.
> TabbyCAD may produce different inner module names as well, so you would need to adjust the script below
> accordingly to account for different module names.
>
> The generated module names are not guaranteed to be valid Cryptol field names, so it is a good idea to sanity check
> your JSON file before loading, and at least removing parenthesis from the names with sed:
> `sed -i '' 's/)//g' adder.json && sed -i '' 's/(//g' adder.json`

:::{code-block} console
$ saw
...
sawscript> enable_experimental
sawscript> m <- yosys_import "adder.json"
sawscript> :type m
Term
sawscript> return (type m)
[23:57:14.492] {add4 : {a : [4], b : [4]} -> {res : [4]},
 full_Bfullarch : {a : [1], b : [1], cin : [1]} -> {cout : [1], s : [1]},
 half_Bhalfarch : {a : [1], b : [1]} -> {c : [1], s : [1]}}
:::

`yosys_import` returns a `Term` with a Cryptol record type, where the fields correspond to each VHDL module.
We can access the fields of this record like we would any Cryptol record, and call the functions within like any Cryptol function.

:::{code-block} console
sawscript> return (type {{ m.add4 }})
[00:00:25.255] {a : [4], b : [4]} -> {res : [4]}
sawscript> return (eval_int {{ (m.add4 { a = 1, b = 2 }).res }})
[00:02:07.329] 3
:::

We can also use all of SAW's infrastructure for asking solvers about `Term`s, such as the `sat` and `prove` commands.
For example:

:::{code-block} console
sawscript> sat w4 {{ m.add4 === \_ -> { res = 5 } }}
[00:04:41.993] Sat: [_ = (5, 0)]
sawscript> prove z3 {{ m.add4 === \inp -> { res = inp.a + inp.b } }}
[00:05:43.659] Valid
sawscript> prove yices {{ m.add4 === \inp -> { res = inp.a - inp.b } }}
[00:05:56.171] Invalid: [_ = (8, 13)]
:::

The full library of `ProofScript` tactics is available in this setting.
If necessary, proof tactics like `simplify` can be used to rewrite goals before querying a solver.

Special support is provided for the common case of equivalence proofs between HDL modules and other `Term`s (e.g. Cryptol functions, other HDL modules, or "extracted" imperative LLVM or JVM code).
The command `yosys_verify` has an interface similar to `llvm_verify`: given a specification, some lemmas, and a proof tactic, it produces evidence of a proven equivalence that may be passed as a lemma to future calls of `yosys_verify`.
For example, consider the following Cryptol specifications for one-bit and four-bit adders:

:::{code-block} cryptol
cryfull :  {a : [1], b : [1], cin : [1]} -> {cout : [1], s : [1]}
cryfull inp = { cout = [cout], s = [s] }
  where [cout, s] = zext inp.a + zext inp.b + zext inp.cin

cryadd4 : {a : [4], b : [4]} -> {res : [4]}
cryadd4 inp = { res = inp.a + inp.b }
:::

If the Cryptol code above is in a file named `adder.cry`, we can prove equivalence between `cryfull` and the VHDL `full` module:

:::{code-block} console
sawscript> import "adder.cry"
sawscript> full_spec <- yosys_verify {{ m.full }} [] {{ cryfull }} [] w4;
:::

The result `full_spec` can then be used as an "override" when proving equivalence between `cryadd4` and the VHDL `add4` module:

:::{code-block} console
sawscript> add4_spec <- yosys_verify {{ m.add4 }} [] {{ cryadd4 }} [full_spec] w4;
:::

The above could also be accomplished through the use of `prove_print` and term rewriting, but it is much more verbose.

`yosys_verify` may also be given a list of preconditions under which the equivalence holds.
For example, consider the following Cryptol specification for `full` that ignores the `cin` bit (save them into `cryfullnocarry.cry` file):

:::{code-block} cryptol
cryfullnocarry :  {a : [1], b : [1], cin : [1]} -> {cout : [1], s : [1]}
cryfullnocarry inp = { cout = [cout], s = [s] }
  where [cout, s] = zext inp.a + zext inp.b
:::

This is not equivalent to `full` in general, but it is if constrained to inputs where `cin = 0`.
We may express that precondition like so:

:::{code-block} console
sawscript> import "cryfullnocarry.cry"
sawscript> full_nocarry_spec <- yosys_verify {{ m.full_Bfullarch }} [{{\(inp : {a : [1], b : [1], cin : [1]}) -> inp.cin == 0}}] {{ cryfullnocarry }} [] w4;
:::

The resulting override `full_nocarry_spec` may still be used in the proof for `add4` (this is accomplished by rewriting to a conditional expression).

## API Reference

The following commands must first be enabled using `enable_experimental`.

- `yosys_import : String -> TopLevel Term` produces a `Term` given the path to a JSON file produced by the Yosys `write_json` command.
  The resulting term is a Cryptol record, where each field corresponds to one HDL module exported by Yosys.
  Each HDL module is in turn represented by a function from a record of input port values to a record of output port values.
  For example, consider a Yosys JSON file derived from the following VHDL entities:

  :::{code-block} vhdl
  entity half is
    port (
      a : in std_logic;
      b : in std_logic;
      c : out std_logic;
      s : out std_logic
    );
  end half;

  entity full is
    port (
      a : in std_logic;
      b : in std_logic;
      cin : in std_logic;
      cout : out std_logic;
      s : out std_logic
    );
  end full;
  :::

  The resulting `Term` will have the type:

  :::{code-block} cryptol
  { half : {a : [1], b : [1]} -> {c : [1], s : [1]}
  , full : {a : [1], b : [1], cin : [1]} -> {cout : [1], s : [1]}
  }
  :::

- `yosys_verify : Term -> [Term] -> Term -> [YosysTheorem] -> ProofScript () -> TopLevel YosysTheorem` proves equality between an HDL module and a specification.
  The first parameter is the HDL module - given a record `m` from `yosys_import`, this will typically look something like `{{ m.foo }}`.
  The second parameter is a list of preconditions for the equality.
  The third parameter is the specification, a term of the same type as the HDL module, which will typically be some Cryptol function or another HDL module.
  The fourth parameter is a list of "overrides", which witness the results of previous `yosys_verify` proofs.
  These overrides can be used to simplify terms by replacing use sites of submodules with their specifications.

  Note that `Term`s derived from HDL modules are "first class", and are not restricted to `yosys_verify`: they may also be used with SAW's typical `Term` infrastructure like `sat`, `prove_print`, term rewriting, etc.
  `yosys_verify` simply provides a convenient and familiar interface, similar to `llvm_verify` or `jvm_verify`.
