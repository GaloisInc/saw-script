pub struct S(pub ());

pub fn f() -> S {
    S(())
}

pub fn g() -> S {
    f()
}
