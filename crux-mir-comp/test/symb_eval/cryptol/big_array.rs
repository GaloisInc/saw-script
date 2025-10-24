//! This test guards against `crucible-mir-comp` inadvertently creating too many
//! fresh SAWCore variables during Cryptol term translation - see
//! https://github.com/GaloisInc/saw-script/issues/2734. It's expected to
//! complete within a few seconds. Taking on the order of minutes, or causing an
//! overall test suite/CI timeout, should be considered test failure.

extern crate crucible;
use crucible::*;

#[crux::test]
fn test() {
    let arr = <[u16; 1024]>::symbolic("big");

    let f: fn([u16; 1024]) -> u16 =
        crucible::cryptol::load("Cryptol", r"\(_ : [1024][16]) -> 0 : [16]");

    for i in 0..1000 {
        crucible_assert!(f(arr) == 0);
    }
}
