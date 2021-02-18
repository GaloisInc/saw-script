extern crate crucible;
use crucible::*;
use crucible::method_spec::{MethodSpec, MethodSpecBuilder};

fn f(x: &[u8; 2]) -> Box<[u8; 2]> {
    Box::new([x[1], x[0]])
}

#[crux_test]
fn f_test() {
    let x = <[u8; 2]>::symbolic("x");
    crucible_assume!(x[0] > 0);
    let y = f(&x);
    crucible_assert!(y[1] > 0);
}

fn f_spec() -> MethodSpec {
    let x = <[u8; 2]>::symbolic("x");
    crucible_assume!(x[0] > 0);

    let mut msb = MethodSpecBuilder::new(f);
    msb.add_arg(&&x);
    msb.gather_assumes();

    let y = Box::new(<[u8; 2]>::symbolic("result"));
    crucible_assert!(y[1] > 0);

    msb.set_return(&y);
    msb.gather_asserts();
    msb.finish()
}

// Spec:
// - Pre state:
//   - Fresh vars: x0, x1
//   - Fresh allocs: ptr0
//   - Args: ptr0
//   - PointsTos: ptr0 -> (x0, x1)
//   - Preconditions: x0 > 0
// - Post state:
//   - Fresh vars: y0, y1
//   - Fresh allocs: ptr1
//   - Return: ptr1
//   - PointsTos: ptr1 -> (y0, y1)
//   - Postconditions: y1 > 0

#[crux_test]
fn use_f() {
    f_spec().enable();

    let a = u8::symbolic("a");
    let b = u8::symbolic("b");
    crucible_assume!(0 < a && a < 10);
    let cd = f(&[a, b]);
    let d = cd[1];
    crucible_assert!(0 < d);
    crucible_assert!(d < 10);
}
