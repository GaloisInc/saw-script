/// This function is adapted from the example in
/// https://github.com/GaloisInc/saw-script/issues/2740, and its verification is
/// expected to be tractable iff path satisfiability checking is enabled in SAW.
pub fn f(i: usize) -> usize {
    let mut x = i;

    for _ in i..1 {
        x += 1;
    }

    x
}
