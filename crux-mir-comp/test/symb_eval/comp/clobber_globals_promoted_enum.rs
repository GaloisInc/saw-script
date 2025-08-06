extern crate crucible;
use crucible::method_spec::clobber_globals;

#[crux::test]
fn f_test() {
    clobber_globals();
    let b = None::<()> == None;
}
