extern crate crucible;
use crucible::*;

#[crux::test]
fn test() {
    let f: fn(usize, &[u8]) -> u8 = cryptol::load("Cryptol", "sum`{_,[8]}");
    let arr = <[u8;3]>::symbolic("arr");
    f(usize::symbolic("s"),&arr[0..]);
}