//! Check that enabling a `MethodSpec` only affects the current test.  Overrides for each test
//! should all be independent.
extern crate crucible;
use crucible::*;
use crucible::method_spec::{MethodSpec, MethodSpecBuilder, clobber_globals};

fn f(x: (u8, u8)) -> (u8, u8) {
    (x.1, x.0)
}

#[crux::test]
fn f_test() {
    clobber_globals();
    let x = <(u8, u8)>::symbolic("x");
    crucible_assume!(x.0 > 0);
    let y = f(x);
    crucible_assert!(y.1 > 0);
}

fn f_spec() -> MethodSpec {
    let x = <(u8, u8)>::symbolic("x");
    crucible_assume!(x.0 > 0);

    let mut msb = MethodSpecBuilder::new(f);
    msb.add_arg(&x);
    msb.gather_assumes();

    let y = <(u8, u8)>::symbolic("result");
    crucible_assert!(y.1 > 0);

    msb.set_return(&y);
    msb.gather_asserts();
    msb.finish()
}

#[crux::test]
fn use_f1() {
    let a = u8::symbolic("a");
    let b = u8::symbolic("b");
    crucible_assume!(0 < a && a < 10);
    let (c, d) = f((a, b));
    crucible_assert!(0 < d);
    // This should pass as long as the spec (which is imprecise) is not in use.
    crucible_assert!(d < 10);
}

#[crux::test]
fn use_f2() {
    f_spec().enable();

    let a = u8::symbolic("a");
    let b = u8::symbolic("b");
    crucible_assume!(0 < a && a < 10);
    let (c, d) = f((a, b));
    crucible_assert!(0 < d);
    // This should fail because the spec (which is imprecise) is in use for this test only.
    crucible_assert!(d < 10);
}

#[crux::test]
fn use_f3() {
    let a = u8::symbolic("a");
    let b = u8::symbolic("b");
    crucible_assume!(0 < a && a < 10);
    let (c, d) = f((a, b));
    crucible_assert!(0 < d);
    // This should pass as long as the spec (which is imprecise) is not in use.
    crucible_assert!(d < 10);
}
