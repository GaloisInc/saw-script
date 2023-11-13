// Meant to be overridden
pub fn f(_x: u32) {}

pub fn g(b: bool) {
    if b {
        f(27)
    } else {
        f(42)
    }
}
