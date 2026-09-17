pub fn f(_x0: &[u8], _x1: &[u8]) {}

pub fn g(x: &[[u8; 16]; 2]) {
    f(&x[0], &x[1])
}
