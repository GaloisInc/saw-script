const X: &[u32] = &[0; 4];
const Y: &[u32] = &[1; 4];

pub fn f(x: &[u32], y: &[u32]) -> bool {
    x[0] == y[0]
}

pub fn g() -> bool {
    f(X, Y)
}
