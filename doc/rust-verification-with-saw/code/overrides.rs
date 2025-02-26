pub fn g(x: u32) -> u32 {
    x.wrapping_add(1)
}

pub fn f(x: u32) -> u32 {
    let x1 = g(x);
    let x2 = g(x1);
    g(x2)
}
