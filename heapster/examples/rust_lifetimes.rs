
pub fn mux_mut_refs_u64 <'a> (x1: &'a mut u64, x2: &'a mut u64, b: bool) -> &'a mut u64 {
    if b {
        return x1;
    } else {
        return x2;
    }
}

pub fn mux_mut_refs_poly <'a,X> (x1: &'a mut X, x2: &'a mut X, b: bool) -> &'a mut X {
    if b {
        return x1;
    } else {
        return x2;
    }
}

pub fn use_mux_mut_refs () -> u64 {
    let mut i1:u64 = 5;
    let mut i2:u64 = 42;
    let r = mux_mut_refs_u64 (&mut i1, &mut i2, true);
    *r = *r + 1;
    i1 = i1 + 1;
    return i1;
}

pub fn use_mux_mut_refs2 <'a,'b> (x1: &'a mut u64, x2: &'b mut u64) -> u64 {
    let r = mux_mut_refs_poly (x1,x2,true);
    *r = *r + 1;
    *x1 = *x1 + *x2;
    return *x1;
}

pub fn mux3_mut_refs_u64 <'a> (x1: &'a mut u64, x2: &'a mut u64,
                               x3: &'a mut u64, i: u64) -> &'a mut u64 {
    if i == 0 {
        return x1;
    } else if i == 1 {
        return x2;
    } else {
        return x3;
    }
}

pub fn use_mux3_mut_refs <'a,'b,'c> (x1: &'a mut u64, x2: &'b mut u64,
                                     x3: &'c mut u64) -> u64 {
    let r = mux3_mut_refs_u64 (x1,x2,x3,2);
    *r = *r + 1;
    *x1 = *x1 + *x2 + *x3;
    return *x1;
}

pub fn use_mux3_mut_refs_onel <'a> (x1: &'a mut u64, x2: &'a mut u64,
                                    x3: &'a mut u64) -> u64 {
    let r = mux3_mut_refs_u64 (x1,x2,x3,2);
    *r = *r + 1;
    *x1 = *x1 + *x2 + *x3;
    return *x1;
}
