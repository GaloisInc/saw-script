extern crate crucible;
use crucible::*;

const PATH: &str = "test/symb_eval/cryptol/basic.cry";

#[crux_test]
fn test() {
    let x = u8::symbolic("x");
    let y = u8::symbolic("y");
    let expected = x.wrapping_add(y);

    let f: fn((u8, u8)) -> u8 = cryptol::load(PATH, "tupleArg");
    let actual = f((x, y));

    crucible_assert!(
        actual == expected,
        "f(({}, {})) = {:?}, but expected {:?}", x, y, actual, expected,
    );
}
