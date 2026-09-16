extern crate crucible;
use crucible::*;

const PATH: &str = "test::symb_eval::cryptol::true_constraint";

#[crux::test]
fn test() {
    let f: fn(usize, usize, &[u8], &[u8]) -> [u8; 4] =
        cryptol::load(PATH, "Instantiated::f");
    let key = <[u8; 2]>::symbolic("key");
    let message = <[u8; 3]>::symbolic("message");
    assert_eq!(f(key.len(), message.len(), &key, &message), [0; 4]);
}
