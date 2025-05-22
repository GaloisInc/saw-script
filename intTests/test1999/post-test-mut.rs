pub fn get41() -> &'static mut u32 {
    Box::leak(Box::new(41))
}

pub fn is42() -> bool {
    *get41() + 1 == 42
}

