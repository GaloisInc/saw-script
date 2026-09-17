fn f(a: &mut [u8]) {
    a[0] = a[0].wrapping_add(1);
}

pub fn g(a: &mut [u8; 5]) {
    f(&mut a[0..2]);
    f(&mut a[2..4]);
}

// We define and test `h` separately from `g` so that we can check that SAW is
// sensibly handling `crucible-mir`'s flattened aggregate representation (which
// will be used to represent `a`, as it's a nested array). See #3401, and
// `intTests/test3401-{failure,soundness}`, for more on how this can go wrong.
pub fn h(a: &mut [[u8; 5]; 2]) {
    f(&mut a[0][0..2]);
    f(&mut a[0][2..4]);
    f(&mut a[1][0..2]);
    f(&mut a[1][2..4]);
}
