pub fn f(_p: &i32, _q: &i32) {}

pub fn g() {
    f(&1, &2);
    let xs = [1, 2, 3];
    f(&xs[0], &xs[1]);
}
