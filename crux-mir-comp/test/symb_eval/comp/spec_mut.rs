extern crate crucible;
use crucible::*;
use crucible::method_spec::{MethodSpec, MethodSpecBuilder};

fn f(x: &mut [u8; 2]) {
    x.swap(0, 1);
}

#[crux_test]
fn f_test() {
    let mut x = <[u8; 2]>::symbolic("x");
    crucible_assume!(x[0] > 0);
    f(&mut x);
    crucible_assert!(x[1] > 0);
}

fn f_spec() -> MethodSpec {
    let mut x = <[u8; 2]>::symbolic("x");
    crucible_assume!(x[0] > 0);
    crucible_assume!(x[1] == 0);

    let mut msb = MethodSpecBuilder::new(f);
    msb.add_arg(& &mut x);
    msb.gather_assumes();

    // Call happens here
    crucible_assert!(x[1] > 0);

    msb.set_return(&());
    msb.gather_asserts();
    msb.finish()
}

// Spec:
// - Pre state:
//   - Fresh vars: x0, x1
//   - Fresh allocs: ptr0
//   - Args: ptr0
//   - PointsTos: ptr0 -> [x0, x1]
//   - Preconditions: x0 > 0
// - Post state:
//   - Fresh vars: y0, y1
//   - Fresh allocs: none
//   - Return: ()
//   - PointsTos: ptr0 -> [y0, y1]
//   - Postconditions: y1 > 0

#[crux_test]
fn use_f() {
    f_spec().enable();

    let a = u8::symbolic("a");
    let b = u8::symbolic("b");
    crucible_assume!(0 < a && a < 10);
    crucible_assume!(b == 0);
    let mut arr = [a, b];
    f(&mut arr);
    let [c, d] = arr;
    crucible_assert!(0 < d);
    crucible_assert!(d < 10);
}
