pub fn f(s: &str) -> u8 {
    let bytes: &[u8] = s.as_bytes();
    bytes[0] + bytes[1]
}
