#[no_mangle]
static mut X: i32 = 0;

#[inline(never)]
#[no_mangle]
pub unsafe fn f(y: i32) -> i32 {
    X = X + 1;
    return X + y;
}

#[inline(never)]
#[no_mangle]
pub unsafe fn g(z: i32) -> i32 {
    X = X + 2;
    return X + z;
}

#[inline(never)]
#[no_mangle]
pub unsafe fn h(w: i32) -> i32 {
    return g(f(w));
}

fn main() {
}
