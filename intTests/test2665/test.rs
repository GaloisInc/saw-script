// Aliasing input and output

pub fn foo_in_out(x: *const u32) -> *const u32 {
    x
}

pub fn bar_in_out(x: *const u32) -> bool {
    x == foo_in_out(x)
}

// Aliasing input and mutable static

static mut GLOB_MUT: u32 = 0;

pub fn foo_in_static_mut(x: *mut u32) -> bool {
    x == &raw mut GLOB_MUT
}

pub fn bar_in_static_mut() -> bool {
    foo_in_static_mut(&raw mut GLOB_MUT)
}

// Aliasing input and immutable static

static GLOB: u32 = 0;

pub fn foo_in_static(x: *const u32) -> bool {
    x == &raw const GLOB
}

pub fn bar_in_static() -> bool {
    foo_in_static(&raw const GLOB)
}

// Aliasing output and mutable static

pub fn foo_out_static_mut() -> *mut u32 {
    &raw mut GLOB_MUT
}

pub fn bar_out_static_mut() -> bool {
    &raw mut GLOB_MUT == foo_out_static_mut()
}

// Aliasing output and immutable static

pub fn foo_out_static() -> *const u32 {
    &raw const GLOB
}

pub fn bar_out_static() -> bool {
    &raw const GLOB == foo_out_static()
}
