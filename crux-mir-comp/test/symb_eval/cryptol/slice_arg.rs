
use crucible::*;
cryptol! {
    path "test::symb_eval::cryptol::SliceArg";
    pub fn f(x: &[u8]) -> u32 = r"f";
}

fn g(x: u8) -> u32 { f(&[x,x,x]) }

#[crux::test]
pub fn bar() {
  let x = u8::symbolic("x");
  let y = (x.wrapping_add(x.wrapping_add(x))) as u32;
  assert_eq!(g(x),y)
}
