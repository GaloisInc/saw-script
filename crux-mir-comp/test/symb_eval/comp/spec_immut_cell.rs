use std::cell::Cell;
extern crate crucible;
use crucible::*;
use crucible::method_spec::{MethodSpec, MethodSpecBuilder, clobber_globals};

fn f(x: &[Cell<u8>; 2]) {
    x[0].swap(&x[1])
}

#[crux_test]
fn f_test() {
    clobber_globals();
    let mut x = [
        Cell::new(u8::symbolic("x0")),
        Cell::new(u8::symbolic("x1")),
    ];
    crucible_assume!(x[0].get() > 0);
    f(&x);
    crucible_assert!(x[1].get() > 0);
}

fn f_spec() -> MethodSpec {
    let mut x = [
        Cell::new(u8::symbolic("x0")),
        Cell::new(u8::symbolic("x1")),
    ];
    crucible_assume!(x[0].get() > 0);
    crucible_assume!(x[1].get() == 0);

    let mut msb = MethodSpecBuilder::new(f);
    msb.add_arg(& &x);
    msb.gather_assumes();

    // Call happens here
    crucible_assert!(x[1].get() > 0);

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

    let a = Cell::new(u8::symbolic("a"));
    let b = Cell::new(u8::symbolic("b"));
    crucible_assume!(0 < a.get() && a.get() < 10);
    crucible_assume!(b.get() == 0);
    let arr = [a, b];
    f(&arr);
    let [c, d] = arr;
    crucible_assert!(0 < d.get());
    crucible_assert!(d.get() < 10);
}
