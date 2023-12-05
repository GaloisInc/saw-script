static mut A: u32 = 42;

pub fn side_effect() -> u32 {
    unsafe {
        let v: u32 = A;
        A = 0;
        v
    }
}

pub fn foo() -> u32 {
    side_effect();
    side_effect()
}
