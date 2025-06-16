pub struct Stuff {
    p: *const i32,
}

pub fn mk_stuff(p: *const u8) -> Stuff {
    Stuff {
        p: p as *const i32
    }
}

pub fn do_stuff(s: Stuff) -> u8 {
    unsafe {
        (*(s.p as *const u8)).wrapping_add(1)
    }
}

pub fn weird_add(x: u8) -> u8 {
    let stuff = mk_stuff(&raw const x);
    do_stuff(stuff)
}
