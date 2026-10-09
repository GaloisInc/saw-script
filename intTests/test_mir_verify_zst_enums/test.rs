//! This allows testing support for zero-sized enums across a few axes:
//! - Whether or not the enum is `repr(transparent)`
//! - Whether or not the function undergoing verification uses an override
//! - Whether the overridden function's parameter is owned or borrowed

pub enum E1 {
    A(()),
}

#[repr(transparent)]
pub enum E2 {
    A(()),
}

pub fn f1(e: &E1) {
    match e {
        E1::A(u) => *u,
    }
}

pub fn f2(e: &E2) {
    match e {
        E2::A(u) => *u,
    }
}

pub fn g1(e: E1) {
    f1(&e)
}

pub fn g2(e: E2) {
    f2(&e)
}

pub fn h1(e: E1) {
    g1(e)
}

pub fn h2(e: E2) {
    g2(e)
}
