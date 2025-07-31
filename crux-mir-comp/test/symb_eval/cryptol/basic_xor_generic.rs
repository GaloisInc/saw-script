extern crate crucible;
use crucible::*;

cryptol! {
    path "test::symb_eval::cryptol::basic";

    /// Xor the bits of two arrays
    fn xor_bits<const N: usize>(x: [bool; N], y: [bool; N]) -> [bool; N] = "xorBits`{{{N}}}";
}

#[crux::test]
fn test() {
    let x = <[bool; 10]>::symbolic("x");
    let y = <[bool; 10]>::symbolic("y");
    let expected = std::array::from_fn(|i| x[i] ^ y[i]);
    let actual = xor_bits(x, y);
    crucible_assert!(
        actual == expected,
        "f({x}, {y}) = {actual:?}, but expected {expected:?}");
}
