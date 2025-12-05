// A regression test for #2873. crucible-mir-comp's override machinery needs to
// load the `Cryptol.seq` identifier when simulating the override arising from
// `f_equiv()`, and in order for this to work, we need to ensure that
// crucible-mir-comp loads the contents of cryptol-saw-core's `Cryptol` module
// beforehand.

pub fn f(x: [u8; 2]) -> [u8; 2] {
    x
}

pub fn g(x: [u8; 2]) -> [u8; 2] {
    f(x)
}

#[cfg(crux)]
mod verification {
    use super::*;
    extern crate crucible;
    extern crate crucible_proc_macros;
    use crucible::{Symbolic, crucible_assert, override_};
    use crucible::cryptol::uninterp;
    use crucible_proc_macros::crux_spec_for;

    mod cry {
        use super::crucible::cryptol;
        cryptol! {
            path "test::symb_eval::comp::crux_spec_for_array";
            pub fn foo(x: [u8; 2]) -> [u8; 2] = r"foo";
            pub fn goo(x: [u8; 2]) -> [u8; 2] = r"goo";
        }
    }

    #[crux_spec_for(f)]
    pub fn f_equiv() {
        let x = <[u8; 2]>::symbolic("x");
        let expected = cry::foo(x);
        let actual = f(x);
        crucible_assert!(expected == actual);
    }

    #[crux::test]
    pub fn g_equiv() {
        uninterp("foo");

        f_equiv_spec().enable();

        let x = <[u8; 2]>::symbolic("x");
        let expected = cry::goo(x);
        let actual = g(x);
        crucible_assert!(
            expected == actual,
            "x: {:?}, expected: {:?}, actual: {:?}",
            x,
            expected,
            actual,
        );
    }
}
