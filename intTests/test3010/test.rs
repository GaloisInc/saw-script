fn f(a: &[u8]) -> u8 {
    a[0]
}

pub fn g(a: [u8; 5]) -> u8 {
    f(&a[2..4])
}

// We define and test `h` separately from `g` so that we can check that SAW is
// sensibly handling `crucible-mir`'s flattened aggregate representation (which
// will be used to represent `a`, as it's a nested array). See #3401, and
// `intTests/test3401-{failure,soundness}`, for more on how this can go wrong.
pub fn h(a: [[u8; 5]; 2]) -> u8 {
    f(&a[1][2..4])
}
