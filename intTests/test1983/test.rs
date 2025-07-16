static ARRAY: [i32; 3] = [2, 4, 6];

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
