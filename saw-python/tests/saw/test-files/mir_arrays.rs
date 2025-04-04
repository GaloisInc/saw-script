pub fn f(x: [&u32; 2]) -> u32 {
    x[0].wrapping_add(*x[1])
}

pub fn g(x: [&mut u32; 2]) {
    *x[0] = 42;
    *x[1] = x[1].wrapping_add(1);
}

pub fn h() -> [&'static u32; 2] {
    [&27, &42]
}

pub fn i(_x: [u32; 0]) -> [u64; 0] {
    []
}
