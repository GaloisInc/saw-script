//! Numbers of rounds allowed to be used with a Salsa20 family stream cipher

pub trait Rounds: Copy {
    const COUNT: usize;
}

/// 8-rounds (Salsa20/8)
#[derive(Copy, Clone)]
pub struct R8;

impl Rounds for R8 {
    const COUNT: usize = 8;
}

/// 12-rounds (Salsa20/12)
#[derive(Copy, Clone)]
pub struct R12;

impl Rounds for R12 {
    const COUNT: usize = 12;
}

/// 20-rounds (Salsa20/20)
#[derive(Copy, Clone)]
pub struct R20;

impl Rounds for R20 {
    const COUNT: usize = 20;
}
