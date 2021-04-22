extern crate crucible;
use crucible::*;

cryptol! {
    path "test/symb_eval/cryptol/basic.cry";

    fn add_byte(x: u8, y: u8) -> u8 = "addByte";
}

#[crux_test]
fn test() {
    let x = u8::symbolic("x");
    let y = u8::symbolic("y");
    let expected = x.wrapping_add(y);
    let actual = add_byte(x, y);

    crucible_assert!(
        actual == expected,
        "f({}, {}) = {:?}, but expected {:?}", x, y, actual, expected,
    );
}
