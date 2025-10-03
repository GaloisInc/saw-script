extern crate crucible;
use crucible::*;

#[crux::test]
fn test() {
    let f: fn(usize,usize,&[u8]) -> u8 = cryptol::load("Cryptol", "sum");
}