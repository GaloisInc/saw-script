pub struct S(pub ());

pub fn f() -> S {
    S(())
}

pub fn g() -> S {
    f()
}

pub struct T((), pub u8);

pub fn h() -> T {
    T((), 42)
}

pub fn i() -> T {
    h()
}
