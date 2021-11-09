extern crate crucible;
use crucible::*;
use crucible::method_spec::{MethodSpec, MethodSpecBuilder, clobber_globals};

fn f(x: &mut [u8]) {
    x.swap(0, 1);
}

#[crux_test]
fn f_test() {
    clobber_globals();
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
    // TODO: would be nice to have strongly-typed add_arg, so coercions will apply here
    msb.add_arg(& (&mut x as &mut [_]));
    msb.gather_assumes();

    // Call happens here
    crucible_assert!(x[1] > 0);

    msb.set_return(&());
    msb.gather_asserts();
    msb.finish()
}

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
