// Test substitution with multiple related equalities.
extern crate crucible;
use crucible::*;
use crucible::method_spec::{MethodSpec, MethodSpecBuilder, clobber_globals};

fn f(x: u8) -> (u8, u8) {
    (x, x + 1)
}

fn f_spec() -> MethodSpec {
    let x = <u8>::symbolic("x");

    let mut msb = MethodSpecBuilder::new(f);
    msb.add_arg(&x);
    msb.gather_assumes();

    let (y0, y1) = <(u8, u8)>::symbolic("result");
    // These are in reverse order compared to `subst_multi.rs`.  As a result, only the first can be
    // turned into a substitution.  The second will remain as a postcondition, since using it as a
    // substitution would reintroduce the eliminated variable `y0`.
    crucible_assert!(y0 == x);
    crucible_assert!(y1 == y0 + 1);

    msb.set_return(&(y0, y1));
    msb.gather_asserts();
    msb.finish()
}

#[crux::test]
fn use_f() {
    f_spec().enable();

    let a = u8::symbolic("a");
    crucible_assume!(0 < a && a < 10);
    let (b0, b1) = f(a);
    crucible_assert!(b0 == a);
    crucible_assert!(b1 == b0 + 1);
}
