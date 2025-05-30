pub unsafe fn raw_assign(src: *const i32, dest: *mut i32) {
    unsafe {
        *dest = *src;
    }
}

pub unsafe fn raw_swap(x: *mut i32, y: *mut i32) {
    unsafe {
        let tmp = *x;
        raw_assign(y, x);
        *y = tmp;
    }
}
