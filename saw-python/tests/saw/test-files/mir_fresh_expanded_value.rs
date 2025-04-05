pub struct S1 {
    pub x: u32,
    pub y: u32,
}

pub fn f(_s: S1) {}

pub fn g(_a: [u32; 2]) {}

pub fn h(_t: (u32, u32)) {}

pub struct S2 {
    pub z: u32,
    pub w: &'static u32,
}

pub fn i(_s: S2) {}
