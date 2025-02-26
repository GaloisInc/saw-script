pub struct S(u32, u64);
pub struct T(u32, u64);

pub fn make_s() -> S {
    S(27, 42)
}

pub fn make_t() -> T {
    T(27, 42)
}

pub struct Foo<A, B>(A, B);

pub fn make_foo() -> Foo<u32, u64> {
    Foo(27, 42)
}

pub struct Bar(u8, u16, Foo<u32, u64>);

pub fn do_stuff_with_bar(b: Bar) {
    // ...
}
