fn f(a: &[u8]) -> u8 {
    a[0]
}

pub fn g(a: [u8; 5]) -> u8 {
    f(&a[2..4])
}

pub fn h(a: [[u8; 5]; 2]) -> u8 {
    f(&a[1][2..4])
}
