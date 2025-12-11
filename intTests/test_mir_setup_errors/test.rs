// Non-void: used to test required mir_return, etc.
pub fn id(x: u32) -> u32 {
    x
}

// Void: used to test optional mir_return.
pub fn id_void(x: u32) {
    let _ = x;
}
