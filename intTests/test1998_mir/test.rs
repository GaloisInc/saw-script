pub fn f(x: [u16; 32], y: [u16; 32]) -> bool {
    let mut eq: bool = true;
    for i in 0..32 {
        eq &= x[i] == y[i];
    }
    eq
}
