extern crate crucible;
use crucible::*;

#[crux::test]
fn test() {
    let f: fn(usize, &[u8]) -> u8 = cryptol::load("Cryptol", "sum`{_,[8]}");
    let arr = <[u8;3]>::symbolic("arr");
    let mut sum = 0_u8;
    assert_eq!(f(0,&arr[0..0]), 0);
    for i in 0 .. arr.len() {
        sum = sum.wrapping_add(arr[i]);
        let s = &arr[0..=i];
        assert_eq!(f(s.len(),s),sum);
    }
}