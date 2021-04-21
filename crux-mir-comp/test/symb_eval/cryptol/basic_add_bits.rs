extern crate crucible;
use crucible::*;

const PATH: &str = "test/symb_eval/cryptol/basic.cry";

fn to_bits(x: u8) -> [bool; 8] {
    [
        x & (1 << 7) != 0,
        x & (1 << 6) != 0,
        x & (1 << 5) != 0,
        x & (1 << 4) != 0,
        x & (1 << 3) != 0,
        x & (1 << 2) != 0,
        x & (1 << 1) != 0,
        x & (1 << 0) != 0,
    ]
}

fn from_bits(x: [bool; 8]) -> u8 {
    ((x[0] as u8) << 7) |
    ((x[1] as u8) << 6) |
    ((x[2] as u8) << 5) |
    ((x[3] as u8) << 4) |
    ((x[4] as u8) << 3) |
    ((x[5] as u8) << 2) |
    ((x[6] as u8) << 1) |
    ((x[7] as u8) << 0)
}

#[crux_test]
fn test() {
    let x = u8::symbolic("x");
    let y = u8::symbolic("y");
    let expected = x.wrapping_add(y);

    let f: fn([bool; 8], [bool; 8]) -> [bool; 8] = cryptol::load(PATH, "addByte");
    let actual = from_bits(f(to_bits(x), to_bits(y)));

    crucible_assert!(
        actual == expected,
        "f({}, {}) = {:?}, but expected {:?}", x, y, actual, expected,
    );
}
