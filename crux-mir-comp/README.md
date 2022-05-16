# Compositional `crux-mir`

This is a variant of [`crux-mir`][crux-mir] with support for compositional
verification and Cryptol integration.


## Building

First, set up baseline `crux-mir` as described in the [`crux-mir`
README][crux-mir].

[crux-mir]: https://github.com/GaloisInc/crucible/tree/master/crux-mir#readme

Then install `crux-mir-comp`:

```sh
cabal v2-install exe:crux-mir-comp --overwrite-policy=always
```


## Running

To run `crux-mir-comp` on a Cargo project, first set the
`CRUX_RUST_LIBRARY_PATH` environment variable as described in the [`crux-mir`
README][crux-mir-env]:

```sh
export CRUX_RUST_LIBRARY_PATH=.../crucible/crux-mir/rlibs
```

[crux-mir-env]: https://github.com/GaloisInc/crucible/tree/master/crux-mir#running-on-a-cargo-project

Next, configure `cargo crux-test` to use `crux-mir-comp` instead of `crux-mir`:

```sh
export CRUX_MIR=crux-mir-comp
```

For tests that use Cryptol via the `cryptol!` macro, it may also be necessary
to set `CRYPTOLPATH`.

Finally, in the directory of a Cargo project, run the project's tests:

```sh
cargo crux-test
```


## Compositional verification



## Cryptol support




## Troubleshooting

If you encounter a panic inside the `crucible::method_spec` module, like this:

```
[Crux] Found counterexample for verification goal
[Crux]   internal: error: in crucible/3a1fbbbh::method_spec[0]::raw[0]::builder_new[0]::_inst24b007056ae0a9a6[0]
[Crux]   panicking::panic_fmt, called from crucible/3a1fbbbh::method_spec[0]::raw[0]::builder_new[0]::_inst24b007056ae0a9a6[0]
```

Then most likely `cargo crux-test` is using `crux-mir` as the simulation
backend instead of `crux-mir-comp`.  Check that `CRUX_MIR=crux-mir-comp` is set
in the environment and that you are using the most recent version of
`mir-json`.


