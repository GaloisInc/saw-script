pub fn f(x: Option<u32>) -> u32 {
    match x {
        Some(x) => x,
        None => 27,
    }
}

pub fn g(x: Option<u32>) {
    f(x);
}

pub fn gg(x: Option<u32>) {
    g(x);
}
