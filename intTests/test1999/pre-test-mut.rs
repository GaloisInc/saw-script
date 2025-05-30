pub fn x(s: &mut u32) -> &mut u32 {
    s
}

pub fn is42() -> bool {
    *x(&mut 42) == 42
}
