pub fn f(_x: *const u8) {}

pub fn g() {
    let n: i32 = 10;
    f(&raw const n as *const u8);
    let m: u8 = 11;
    f(&raw const m);
}
