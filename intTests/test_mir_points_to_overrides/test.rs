pub fn inner(_x: &mut u32) {}

pub fn outer(x: &mut u32) {
    inner(x)
}
