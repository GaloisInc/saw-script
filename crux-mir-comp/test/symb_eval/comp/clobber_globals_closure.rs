// A regression test for #2687. rustc will promote the closure used in the body
// of the mk_closure() function to a static item, which means that the value
// of this static will be clobbered as part of proving foo_equiv(). Because
// this closure does not capture any variables, it is represented as an empty
// MirAggregate in crucible-mir. There was a subtle bug involving mistreatment
// of empty MirAggregates that #2687 uncovered, and this test case aims to
// ensure that this bug remains fixed.

extern crate crucible;
extern crate crucible_proc_macros;
use crucible::crucible_assert;
use crucible_proc_macros::crux_spec_for;

// The closure must be promoted to get 'static lifetime
fn mk_closure() -> &'static impl Fn() -> u32 {
    &|| 42u32
}

pub fn foo() -> u32 {
    mk_closure()()
}

#[crux_spec_for(foo)]
pub fn foo_equiv() {
    let expected = 42u32;
    let actual = foo();
    crucible_assert!(expected == actual);
}
