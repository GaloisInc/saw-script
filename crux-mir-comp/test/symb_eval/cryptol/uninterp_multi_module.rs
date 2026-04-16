// A regression test for #3164. Here is the play-by-play:
//
// * We import two Cryptol functions `a` and `b`, each from different Cryptol
//   modules `uninterp_multi_module_a` and `uninterp_multi_module_b`,
//   respectively (neither of which imports the other).
//
// * We mark `b` as uninterpreted, so any time `crux-mir-comp` loads a Cryptol
//   function into SAWCore, it must check to see if the Cryptol function
//   contains `b` or not. This requires resolving the name `b` in the current
//   Cryptol environment.
//
// * Because `crux-mir-comp` loads Cryptol code lazily, the first time that it
//   tries to load any Cryptol code is when it invokes `a` in the body of
//   `foo`. `crux-mir-comp` will load the `uninterp_multi_module_a` module (as
//   declared by the corresponding `cryptol!` block) and then try to resolve
//   `b` in the current Cryptol environment. Note, however, that the
//   `uninterp_multi_module_b` module (which contains `b`) hasn't been loaded
//   yet!
//
// * Due to #3164, `crux-mir-comp` used to throw an exception here, as it
//   couldn't find `b`. After fixing #3164, however, `crux-mir-comp` simply
//   proceeds after failing to find `b`, as there is nothing to mark
//   uninterpreted in the definition of `a`.
//
// * Later, when `crux-mir-comp` invokes `b` in the body of `foo`, it will load
//   the `uninterp_multi_module_b` module. Then, when it attempts to resolve
//   `b` in the current Cryptol environment, it will successfully find it. This
//   allows `crux-mir-comp` to treat `b` as uninterpreted.

extern crate crucible;
use crucible::{Symbolic, cryptol};
use crucible::cryptol::uninterp;

mod cry {
    use super::*;

    cryptol! {
        path "test::symb_eval::cryptol::uninterp_multi_module_a";
        pub fn a(x: u8) -> u8 = "a";
    }

    cryptol! {
        path "test::symb_eval::cryptol::uninterp_multi_module_b";
        pub fn b(x: u8) -> u8 = "b";
    }
}

fn foo(x: u8) -> u8 {
    cry::a(x).wrapping_add(cry::b(x))
}

#[crux::test]
fn foo_test() {
    uninterp("b");
    let x = u8::symbolic("x");
    foo(x);
}
