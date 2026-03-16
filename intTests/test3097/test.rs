struct S {
    x: i32,
    y: i32,
}

struct T {
    a: i32,
    b: i32,
    c: bool,
}

pub fn f(_p: &i32, _q: &i32) {}

pub fn g() {
    let s = S { x: 7, y: 8 };
    f(&s.x, &s.y);
    let t = T { a: 1, b: 2, c: true };
    f(&t.a, &t.b);
    f(&3, &4);
}
