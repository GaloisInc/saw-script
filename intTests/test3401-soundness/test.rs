pub fn f(x: &[u8]) -> u8 {
    x[0]
}

pub fn g(x: &[[u8; 4]; 2]) -> u8 {
    f(&x[1])
}
