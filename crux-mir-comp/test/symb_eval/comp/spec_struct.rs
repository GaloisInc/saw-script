extern crate crucible;
use crucible::*;
use crucible::method_spec::{MethodSpec, MethodSpecBuilder, clobber_globals};

struct S(u8, u8);

impl Symbolic for S {
    fn symbolic(desc: &str) -> Self {
        S(u8::symbolic(desc), u8::symbolic(desc))
    }
}

fn f(x: S) -> S {
    S(x.1, x.0)
}

#[crux::test]
fn f_test() {
    clobber_globals();
    let x = <S>::symbolic("x");
    crucible_assume!(x.0 > 0);
    let y = f(x);
    crucible_assert!(y.1 > 0);
}

fn f_spec() -> MethodSpec {
    let x = <S>::symbolic("x");
    crucible_assume!(x.0 > 0);

    let mut msb = MethodSpecBuilder::new(f);
    msb.add_arg(&x);
    msb.gather_assumes();

    let y = <S>::symbolic("result");
    crucible_assert!(y.1 > 0);

    msb.set_return(&y);
    msb.gather_asserts();
    msb.finish()
}

#[crux::test]
fn use_f() {
    f_spec().enable();

    let a = u8::symbolic("a");
    let b = u8::symbolic("b");
    crucible_assume!(0 < a && a < 10);
    let S(c, d) = f(S(a, b));
    crucible_assert!(0 < d);
    crucible_assert!(d < 10);
}
