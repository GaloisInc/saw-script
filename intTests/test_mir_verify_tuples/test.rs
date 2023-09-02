pub fn f(s: (u32, u32)) -> (u32, u32) {
    (s.1.wrapping_add(1), s.0.wrapping_add(2))
}

pub fn g(s: &(u32, u32)) -> (u32, u32) {
    (s.1.wrapping_add(1), s.0.wrapping_add(2))
}

pub fn h(s: &mut (u32, u32)) {
    let x = s.0;
    let y = s.1;
    s.0 = y.wrapping_add(1);
    s.1 = x.wrapping_add(2);
}
