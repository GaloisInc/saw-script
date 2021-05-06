extern crate crucible;
use crucible::*;

const PATH: &str = "test::symb_eval::cryptol::basic";

#[crux_test]
fn test() {
    let f: fn([u8; 3]) -> u8 = cryptol::load(PATH, "arrayArg");
}
