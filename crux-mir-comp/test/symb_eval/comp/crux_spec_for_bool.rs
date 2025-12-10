// A regression test for #2872, which ensures that crux-mir-comp can leverage
// the `crux_spec_for` macro in conjunction with a function that takes a `bool`
// as an argument.

pub fn f(x: bool) -> bool {
    x
}

pub fn g(x: bool) -> bool {
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
            path "test::symb_eval::comp::crux_spec_for_bool";
            pub fn foo(x: bool) -> bool = r"foo";
            pub fn goo(x: bool) -> bool = r"goo";
        }
    }

    #[crux_spec_for(f)]
    pub fn f_equiv() {
        let x = bool::symbolic("x");
        let expected = cry::foo(x);
        let actual = f(x);
        crucible_assert!(expected == actual);
    }

    #[crux::test]
    pub fn g_equiv() {
        uninterp("foo");

        override_(f, cry::foo);
        //f_equiv_spec().enable();

        let x = bool::symbolic("x");
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
