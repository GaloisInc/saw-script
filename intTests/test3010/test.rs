fn f(a: &[u8]) -> u8 {
    a[0]
}

pub fn g(a: [u8; 5]) -> u8 {
    f(&a[2..4])
}
