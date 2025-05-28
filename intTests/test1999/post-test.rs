pub const X: u32 = 42;

pub fn x() -> &'static u32 {
    &X
}

pub fn is42() -> bool {
    *x() == 42
}
