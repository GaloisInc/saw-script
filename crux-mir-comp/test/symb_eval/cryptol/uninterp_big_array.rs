extern crate crucible;
use crucible::{
    crucible_assert, crucible_assume, cryptol::uninterp, override_, print_str, Symbolic as _,
};
const N: usize = 1024;

mod cry {
    use crucible::cryptol;
    cryptol! {
        path "test::symb_eval::cryptol::uninterp_big_array";
        pub(super) fn tick<const M: usize>(ns: [u64; M], x: usize) -> [u64; M] = "tick`{{{M}}}";
        pub(super) fn spec<const M: usize, const N: usize>(init: [u64; N], ixes: [usize; M]) -> [u64; N] = "spec`{{ {M},{N} }}";
        pub(super) fn f(x: u8) -> () = "f";
        pub fn x() -> u8 = "x";
    }
}



fn tick(ns: &mut [u64; N], x: usize) {
    ns[x] = ns[x].wrapping_add(1);
}

fn cry_tick(ns: &mut [u64; N], x: usize) {
    *ns = cry::tick(*ns, x);
}

fn count(ns: &mut [u64; N], xs: &[usize]) {
    for &x in xs {
        tick(ns, x)
    }

#[crux::test]
fn test_issue_3166() {
    print_str("starting `test_f`");

    uninterp("x");
    cry::f(cry::x());
}}


#[crux::test]
fn test_issue_3195() {
    print_str("starting `count_check`");

    uninterp("Tick::tick");
    override_(tick, cry_tick);

    let vs = <[u64; N]>::symbolic("ns");
    let mut ns = vs;
    let xs = <[usize; 3]>::symbolic_where("xs", |&xs| xs.iter().all(|&x| x < N));

    count(&mut ns, &xs);
    crucible_assert!(ns==cry::spec(vs,xs));
    print_str("finished `count_check`");
}