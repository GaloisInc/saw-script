pub struct S<const N: usize> {
    pub x: [u32; N]
}

pub fn f(y: [u32; 1]) -> S<1> {
    S { x: y }
}

pub fn g(y: [u32; 2]) -> S<2> {
    S { x: y }
}

pub struct T<const A: i8,
             const B: i16,
             const C: i32,
             const D: i64,
             const E: isize,
             const F: u8,
             const G: u16,
             const H: u32,
             const I: u64,
             const J: usize,
             const K: bool,
             const L: char>;

pub fn h() -> T<0,0,0,0,0,0,0,0,0,0,true,'a'> { T }
