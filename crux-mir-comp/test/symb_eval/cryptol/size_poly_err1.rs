extern crate crucible;
use crucible::*;

#[crux::test]
fn test() {
    let f: fn() -> u8 = cryptol::load("Cryptol", "sum`{_,[8]}");
}