extern crate crucible;
use crucible::*;

const PATH: &str = "test::symb_eval::cryptol::basic";

#[crux::test]
fn test() {
    let f: fn(u8, u8, u8) -> u8 = cryptol::load(PATH, "addByte");
}
