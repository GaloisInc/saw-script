pub fn times_two(x: u32) -> u32 {
    x << 1 // Gotta go fast
}

pub fn times_two_ref(x: u32) -> u32 {
    2 * x
}
