extern crate crucible;
use crucible::*;

const PATH: &str = "test::symb_eval::cryptol::basic";

#[crux::test]
fn test() {
    let f: fn((u16, u16, u16)) -> u16 = cryptol::load(PATH, "tupleArg");
}
