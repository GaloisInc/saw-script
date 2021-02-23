extern crate crucible;
use std::sync::atomic::{AtomicUsize, Ordering};
use crucible::*;
use crucible::method_spec::{MethodSpec, MethodSpecBuilder, clobber_globals};

static ATOMIC: AtomicUsize = AtomicUsize::new(123);

fn f() {
}

#[crux_test]
fn f_test() {
    clobber_globals();
    f();
    crucible_assert!(ATOMIC.load(Ordering::SeqCst) == 123,
        "expected failure; ATOMIC was clobbered by clobber_globals()");
}

fn f_spec() -> MethodSpec {
    let mut msb = MethodSpecBuilder::new(f);
    msb.gather_assumes();

    // Function call happens here

    msb.set_return(&());
    msb.gather_asserts();
    msb.finish()
}

#[crux_test]
fn use_f() {
    f_spec().enable();

    crucible_assert!(ATOMIC.load(Ordering::SeqCst) == 123,
        "this assert should succeed; f's spec hasn't run yet");
    f();
    crucible_assert!(ATOMIC.load(Ordering::SeqCst) == 123,
        "expected failure; ATOMIC was clobbered by f's spec");
}
