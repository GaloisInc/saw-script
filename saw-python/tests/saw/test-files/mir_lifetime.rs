pub struct S<'a> {
    pub x: &'a u32,
}

pub fn f<'a>(y: &'a u32) -> S<'a> {
    S { x: y }
}
