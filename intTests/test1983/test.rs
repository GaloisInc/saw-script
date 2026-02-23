pub static ARRAY: [i32; 3] = [2, 4, 6];

pub fn get_3(xs: [i32; 10]) -> i32 {
    xs[3]
}

pub fn get_3_ref(xs: &[i32; 10]) -> &i32 {
    &xs[3]
}

pub fn get_19_3(xss: [[i32; 10]; 20]) -> i32 {
    get_3(xss[19])
}

pub fn get_19_3_ref(xss: &[[i32; 10]; 20]) -> &i32 {
    get_3_ref(&xss[19])
}

pub fn get_25_19_3(xsss: [[[i32; 10]; 20]; 30]) -> i32 {
    get_19_3(xsss[25])
}

pub fn get_25_19_3_ref(xsss: &[[[i32; 10]; 20]; 30]) -> &i32 {
    get_19_3_ref(&xsss[25])
}

pub fn get_static_2() -> i32 {
    ARRAY[2]
}

pub fn get_static_2_ref() -> &'static i32 {
    &ARRAY[2]
}

pub struct T {
    a: u64,
    b: [i32; 10],
}

pub struct U(bool, T);

#[repr(transparent)]
pub struct V {
    e: U,
    f: (),
}

pub static STRUCT: T = T { a: 5, b: [42; 10] };

pub fn get_a(t: T) -> u64 {
    t.a
}

pub fn get_a_ref(t: &T) -> &u64 {
    &t.a
}

pub fn get_b_3(t: T) -> i32 {
    get_3(t.b)
}

pub fn get_b_3_ref(t: &T) -> &i32 {
    get_3_ref(&t.b)
}

pub fn get_c_b_3(u: U) -> i32 {
    get_b_3(u.1)
}

pub fn get_c_b_3_ref(u: &U) -> &i32 {
    get_b_3_ref(&u.1)
}

pub fn get_e_c_b_3(v: V) -> i32 {
    get_c_b_3(v.e)
}

pub fn get_e_c_b_3_ref(v: &V) -> &i32 {
    get_c_b_3_ref(&v.e)
}

pub fn get_static_a() -> u64 {
    STRUCT.a
}

pub fn get_static_a_ref() -> &'static u64 {
    &STRUCT.a
}
