extern crate crucible;
extern crate crucible_proc_macros;

use crucible::*;
use crucible_proc_macros::crux_spec_for;

pub fn f(vec: &Vec<u8>) -> u64 {
    let mut r: u64 = 0;
    for x in vec {
        r += *x as u64;
    }
    r
}

pub fn g(vec: &Vec<u8>) -> u64 {
    f(vec)
}

fn mk_vec(arr: &[u8; 4]) -> Vec<u8> {
    let mut v = Vec::with_capacity(4);
    for y in arr { v.push(*y); }
    v
}

#[crux_spec_for(f)]
fn f_equiv() {
    let arr = <[u8; 4]>::symbolic("arr");
    let vec = mk_vec(&arr);
    let output_impl = f(&vec);
    crucible_assert!(output_impl == arr.into_iter().map(|n| n as u64).sum());
}

#[crux::test]
fn g_equiv() {
    let arr = <[u8; 4]>::symbolic("arr");
    let vec = mk_vec(&arr);
    f_equiv_spec().enable();
    let output_impl = g(&vec);
    crucible_assert!(output_impl == arr.into_iter().map(|n| n as u64).sum());
}
