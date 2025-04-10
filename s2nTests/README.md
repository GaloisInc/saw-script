# Regression tests on existing proofs
This directory contains Docker configurations for running some more complex cryptographic proofs.
(These are the same configurations used in our GitHub Actions CI.)

## Building SAWScript
Running `make saw-script` will build SAWScript from the current working tree and place the resulting `saw` binary in `bin/`. This is useful if you develop on a system that isn't binary-compatible with Ubuntu 24.04 (e.g. macOS or NixOS).

## Running tests
Running `make <target>` on one of the following targets will use the `saw` binary in `bin/` to run the respective proof:
- `hmac`
- `drbg`
- `sike`
- `bike`
- `tls`
- `hmac-failure`
- `awslc`
- `blst`

`make` alone with no targets will run all of the proofs.

## Ongoing maintenance concerns

- Currently the awslc proof fails because it tickles #1094.
  It's consequently disabled in the CI run until that gets fixed; see #2273.

- Currently the tls proof contains invalid SAWScript that is accepted with a
  warning in SAW 1.3 but will be rejected eventually.
  This will need to be fixed.
  See #2169.

- The pending deprecation of llvm_struct per #2159 will eventually require
  upstream updates to a number of the proofs.
