pub fn read_from_ref(x: &u32) -> u32 {
    *x
}

pub fn write_to_ref(x: &mut u32, y: u32) {
    *x = y
}
