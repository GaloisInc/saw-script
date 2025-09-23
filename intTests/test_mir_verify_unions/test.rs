union U {
    x: u16,
    y: [u8; 2],
}

// These four functions are meant to implement the identity function on `u16`,
// regardless of system endianness.

fn init_x_read_x(x: u16) -> u16 {
    let u: U = U { x };
    unsafe { u.x }
}

fn init_y_read_y(x: u16) -> u16 {
    let y = x.to_ne_bytes();
    let u: U = U { y };
    u16::from_ne_bytes(unsafe { u.y })
}

fn init_x_read_y(x: u16) -> u16 {
    let u: U = U { x };
    u16::from_ne_bytes(unsafe { u.y })
}

fn init_y_read_x(x: u16) -> u16 {
    let y = x.to_ne_bytes();
    let u: U = U { y };
    unsafe { u.x }
}
