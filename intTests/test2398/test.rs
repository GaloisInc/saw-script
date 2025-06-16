#[repr(transparent)]
pub struct Thing {
    a: (),
    b: i32,
    c: [u8; 0]
}

pub fn get_thing() -> Thing {
    Thing {
        a: (),
        b: 1,
        c: []
    }
}

pub fn get_thing_b() -> i32 {
    get_thing().b
}
