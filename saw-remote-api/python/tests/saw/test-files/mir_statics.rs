static     S1: u32 = 1;
static     S2: u32 = 2;
static mut S3: u32 = 3;

// rustc is very eager to inline immutable, top-level static values, even on the
// lowest optimization settings. To ensure that S1 isn't inlined, we must
// introduce this extra layer of indirection.
#[inline(never)]
pub fn f1_aux() -> &'static u32 {
    &S1
}

pub fn f1() -> u32 {
    *f1_aux()
}

pub fn f2() -> &'static u32 {
    &S2
}

pub fn f3() -> u32 {
    unsafe {
        S3 = S3.wrapping_add(1);
        S3
    }
}

pub fn g(r: &u32) -> bool {
    std::ptr::eq(r, &S1)
}
