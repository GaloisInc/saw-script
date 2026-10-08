extern crate crucible;
extern crate crucible_proc_macros;

use crucible::*;
use crucible_proc_macros::*;

#[derive(Symbolic)]
#[repr(transparent)]
struct S(());

fn f(s: &S) {
    s.0
}

#[crux_spec_for(f)]
fn f_equiv() {
    let s = S::symbolic("s");
    let expected = ();
    let actual = f(&s);
    crucible_assert!(expected == actual);
}

fn g(s: S) {
    f(&s)
}

#[crux_spec_for(g)]
fn g_equiv() {
    f_equiv_spec().enable();
    let s = S::symbolic("s");
    let expected = ();
    let actual = g(s);
    crucible_assert!(expected == actual);
}
