pub fn read_ref(r: &u32) -> u32 {
    *r
}

pub fn swap(a: &mut u32, b: &mut u32) {
    let a_tmp: u32 = *a;
    let b_tmp: u32 = *b;

    *a = b_tmp;
    *b = a_tmp;
}
