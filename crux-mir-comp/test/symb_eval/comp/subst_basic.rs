// Test conversion of `var == expr` postconditions into substitutions.
extern crate crucible;
use crucible::*;
use crucible::method_spec::{MethodSpec, MethodSpecBuilder, clobber_globals};

fn f(x: u8) -> u8 {
    x + 1
}

fn f_spec() -> MethodSpec {
    let x = <u8>::symbolic("x");

    let mut msb = MethodSpecBuilder::new(f);
    msb.add_arg(&x);
    msb.gather_assumes();

    let y = <u8>::symbolic("result");
    crucible_assert!(y == x + 1);

    msb.set_return(&y);
    msb.gather_asserts();
    msb.finish()
}

#[crux_test]
fn use_f() {
    f_spec().enable();

    let a = u8::symbolic("a");
    crucible_assume!(0 < a && a < 10);
    let b = f(a);
    crucible_assert!(b == a + 1);
}
