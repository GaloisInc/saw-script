pub fn x(s: &u32) -> &u32 {
    s
}

pub fn is42() -> bool {
    *x(&42) == 42
}

