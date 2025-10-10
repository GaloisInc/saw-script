// Overlapping inputs

pub fn f(x: *const u32, y: *const u32) -> bool {
    unsafe { x.add(1) == y }
}

pub fn g() -> bool {
    let a = [1, 2];
    let p = a.as_ptr();
    unsafe { f(p, p.add(1)) }
}

// Inputs of different pointee types

pub fn h(x: *const u32, y: *const u8) -> bool {
    x == y as *const u32
}

pub fn i() -> bool {
    let a: u32 = 1;
    h(&raw const a, &raw const a as *const u8)
}
