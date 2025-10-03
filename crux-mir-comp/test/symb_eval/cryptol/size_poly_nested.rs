extern crate crucible;
use crucible::*;

const PATH: &str = "test::symb_eval::cryptol::size_poly_nested";

#[crux::test]
fn test() {
    let f: fn(usize, usize, &[&[u8]]) -> u8 = cryptol::load(PATH, "f");
    let arr_in = <[u8;3]>::symbolic("arr");
    let arr_in_ref = &arr_in[0..];
    let arr = [ arr_in_ref, arr_in_ref ];
    let arr_ref = &arr[0..];
    let mut sum = 0_u8;
    for i in arr_in {
      sum = sum.wrapping_add(i);
    }
    assert_eq!(f(2,3,arr_ref),sum.wrapping_mul(2));
}