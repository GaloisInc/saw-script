pub struct Words<const N: usize>([u8; N]);

fn f<const N: usize>(a: Words<N>) -> [u8; N] { a.0 }

pub fn h4(a: Words<4>) -> [u8; 4] { f(a) }
pub fn h7(a: Words<7>) -> [u8; 7] { f(a) }
