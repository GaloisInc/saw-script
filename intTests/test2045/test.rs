pub fn f(s: &[u8]) -> u8 {
    s[0] + s[1]
}

pub fn g(s: &[u8]) -> u8 {
    f(s)
}
