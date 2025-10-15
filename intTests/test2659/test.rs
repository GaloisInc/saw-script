pub fn f(p: *const u32) -> bool {
    p.is_null()
}

pub fn g() -> bool {
    f(std::ptr::null())
}

pub fn h() -> *const u32 {
    std::ptr::null()
}
