pub fn f(x: *const u32) -> u32 {
    unsafe { *x }
}

#[crux::test]
pub fn g() -> u32 {
    let x: *const u32 = std::ptr::null();
    f(x)
}
