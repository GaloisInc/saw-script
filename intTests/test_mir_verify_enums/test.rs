pub fn f(x: Option<u32>) -> u32 {
    match x {
        Some(x) => x,
        None => 27,
    }
}

pub fn g(b: bool) -> u32 {
    if b {
        f(None)
    } else {
        f(Some(42))
    }
}

pub fn h_none() -> Option<u32> {
    None
}

pub fn h_some(x: u32) -> Option<u32> {
    Some(x)
}

pub enum I {
    I42 = 42,
    I43,
}

pub fn i42() -> I {
    I::I42
}

pub fn i43() -> I {
    I::I43
}
