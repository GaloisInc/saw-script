extern crate crucible;
use crucible::*;
use crucible::method_spec::{MethodSpec, MethodSpecBuilder, clobber_globals};

fn f(x: (u8, u8)) -> (u8, u8) {
    (x.1, x.0)
}

#[crux_test]
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

// Spec:
// - Pre state:
//   - Fresh vars: x0, x1
//   - Args: (x0, x1)
//   - PointsTos: none
//   - Preconditions: x0 > 0
// - Post state:
//   - Fresh vars: y0, y1
//   - Return: (y0, y1)
//   - PointsTos: none
//   - Postconditions: y1 > 0

#[crux_test]
fn use_f() {
    f_spec().enable();

    let a = u8::symbolic("a");
    let b = u8::symbolic("b");
    crucible_assume!(0 < a && a < 10);
    let (c, d) = f((a, b));
    crucible_assert!(0 < d);
    crucible_assert!(d < 10);
}
