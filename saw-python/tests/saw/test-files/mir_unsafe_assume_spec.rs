pub fn f(_x: u32) -> u32 {
    unimplemented!("f should be overridden");
}

pub fn g(x: u32) -> u32 {
    f(x).wrapping_add(1)
}

pub fn h(x: u32) -> u32 {
    x.wrapping_add(1)
}

pub fn g2() -> u32 {
    f(2).wrapping_add(1)
}

pub fn p(_x: &u32, _y: &u32) -> u32 {
    unimplemented!("p should be overriden");
}

pub fn q(x: &u32, y: &u32) -> u32 {
    p(x, y)
}

pub fn side_effect(a: &mut u32) -> u32 {
    let v: u32 = *a;
    *a = 0;
    v
}

pub fn foo(x: u32) -> u32 {
    let mut b: u32 = x;
    side_effect(&mut b);
    side_effect(&mut b)
}
