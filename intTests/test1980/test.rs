pub fn f<T>(x: T) -> T { x }
pub fn g(x: u8) -> u8 { f(x) }
pub fn h(x: u16) -> u16 { f(x) }