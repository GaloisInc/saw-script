fn f(_: &[u8]) {}

pub fn g(a: [u8; 2]) {
    f(&a)
}

pub fn h(a: [u8; 5], b: [u8; 2]) {
    f(&a[0..2]);
    f(&b);
}
