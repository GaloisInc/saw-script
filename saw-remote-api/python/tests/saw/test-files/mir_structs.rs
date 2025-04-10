pub struct S1 {
    pub x1: u32,
    pub y1: u32,
}

pub fn f1(s: S1) -> S1 {
    S1 {
        x1: s.y1.wrapping_add(1),
        y1: s.x1.wrapping_add(2),
    }
}

pub fn g(s: &S1) -> S1 {
    S1 {
        x1: s.y1.wrapping_add(1),
        y1: s.x1.wrapping_add(2),
    }
}

pub fn h(s: &mut S1) {
    let x1 = s.x1;
    let y1 = s.y1;
    s.x1 = y1.wrapping_add(1);
    s.y1 = x1.wrapping_add(2);
}

// Polymorphism

pub struct S2<A, B> {
    pub x2: A,
    pub y2: B,
}

pub fn f2(s: S2<u32, u32>) -> S2<u32, u32> {
    S2 {
        x2: s.y2.wrapping_add(1),
        y2: s.x2.wrapping_add(2),
    }
}

pub struct S3(u32, u32);

pub fn f3(s: S3) -> S3 {
    match s {
        S3(x3, y3) => S3(y3.wrapping_add(1), x3.wrapping_add(2)),
    }
}

#[repr(transparent)]
pub struct S4(u32);

pub fn f4(s: S4) -> S4 {
    match s {
        S4(x4) => S4(x4.wrapping_add(2)),
    }
}
