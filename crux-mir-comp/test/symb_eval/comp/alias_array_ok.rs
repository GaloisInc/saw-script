extern crate crucible;
use std::cell::Cell;
use std::mem;
use crucible::*;
use crucible::method_spec::{MethodSpec, MethodSpecBuilder, clobber_globals};

fn f(x: &Cell<u8>, y: &[Cell<u8>; 2]) {
    x.swap(&y[0]);
}

#[crux_test]
fn f_test() {
    clobber_globals();
    let x = Cell::new(u8::symbolic("x"));
    let y = [Cell::new(u8::symbolic("y")), Cell::new(u8::symbolic("y"))];
    crucible_assume!(x.get() > 0);
    f(&x, &y);
    crucible_assert!(y[0].get() > 0);
}

fn f_spec() -> MethodSpec {
    let x = Cell::new(u8::symbolic("x"));
    let y = [Cell::new(u8::symbolic("y")), Cell::new(u8::symbolic("y"))];
    crucible_assume!(x.get() > 0);

    let mut msb = MethodSpecBuilder::new(f);
    msb.add_arg(& &x);
    msb.add_arg(& &y);
    msb.gather_assumes();

    // Call happens here
    crucible_assert!(y[0].get() > 0);

    msb.set_return(&());
    msb.gather_asserts();
    msb.finish()
}

#[crux_test]
fn use_f() {
    f_spec().enable();

    let a = Cell::new(u8::symbolic("a"));
    let b = [Cell::new(u8::symbolic("b")), Cell::new(u8::symbolic("b"))];
    crucible_assume!(0 < a.get() && a.get() < 10);
    f(&a, &b);
    crucible_assert!(0 < b[0].get());
    crucible_assert!(b[0].get() < 10);
}
