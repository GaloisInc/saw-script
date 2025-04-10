#[repr(transparent)]
pub struct S(u8);

pub fn f(s: &S) -> &S {
    s
}
