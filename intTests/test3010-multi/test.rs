fn f(a: &mut [u8]) {
    a[0] = a[0].wrapping_add(1);
}

pub fn g(a: &mut [u8; 5]) {
    f(&mut a[0..2]);
    f(&mut a[2..4]);
}
