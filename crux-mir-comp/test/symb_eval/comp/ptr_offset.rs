extern crate crucible;
use std::ptr;
use crucible::*;
use crucible::method_spec::{MethodSpec, MethodSpecBuilder, clobber_globals};

fn f(ptr: *mut u8) {
    unsafe { ptr::swap(ptr, ptr.add(1)) };
}

#[crux_test]
fn f_test() {
    clobber_globals();
    let mut x = <[u8; 2]>::symbolic("x");
    crucible_assume!(x[0] > 0);
    f(&mut x[0]);
    crucible_assert!(x[1] > 0);
}

fn f_spec() -> MethodSpec {
    let mut x = <[u8; 2]>::symbolic("x");
    crucible_assume!(x[0] > 0);
    crucible_assume!(x[1] == 0);

    let mut msb = MethodSpecBuilder::new(f);
    msb.add_arg(& &mut x[0]);
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
    let x = u8::symbolic("x");
    let y = u8::symbolic("y");
    crucible_assume!(0 < a && a < 10);
    crucible_assume!(b == 0);
    let mut arr = [x, a, b, y];
    f(&mut arr[1]);
    let [x2, a2, b2, y2] = arr;
    crucible_assert!(0 < b2);
    crucible_assert!(b2 < 10);
    crucible_assert!(x2 == x);
    crucible_assert!(y2 == y);
}
