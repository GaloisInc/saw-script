pub fn rev(v: Vec<i32>) -> Vec<i32> {
    v.into_iter().rev().collect()
}

pub fn rev_rev(v: Vec<i32>) -> Vec<i32> {
    rev(rev(v))
}
