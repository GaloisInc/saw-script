# Regression tests on existing proofs
This directory contains Docker configurations for running some more complex cryptographic proofs.
(These are the same configurations used in our GitHub Actions CI.)

## Building SAWScript
Running `make saw-script` will build SAWScript from the current working tree and place the resulting `saw` binary in `bin/`. This is useful if you develop on a system that isn't binary-compatible with Ubuntu 18.04 (e.g. macOS or NixOS).

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
