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
             const E: i128,
             const F: isize,
             const G: u8,
             const H: u16,
             const I: u32,
             const J: u64,
             const K: u128,
             const L: usize,
             const M: bool,
             const N: char>;

pub fn h() -> T<0,0,0,0,0,0,0,0,0,0,0,0,true,'a'> { T }
