pub fn f(_x: Vec<u8>) {}

pub fn h() {
    f(vec![1, 2, 3, 4, 5]);
    f(vec![1, 2, 3, 4, 5, 6]);
}
