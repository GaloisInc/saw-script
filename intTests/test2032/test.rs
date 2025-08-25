pub fn rev<T>(v: Vec<T>) -> Vec<T> {
    v.into_iter().rev().collect()
}

pub fn rev_rev<T>(v: Vec<T>) -> Vec<T> {
    rev(rev(v))
}

pub fn rev_i32(v: Vec<i32>) -> Vec<i32> {
    rev(v)
}

pub fn rev_rev_i32(v: Vec<i32>) -> Vec<i32> {
    rev_rev(v)
}

pub fn rev_tuple(v: Vec<(u8, i64, u128)>) -> Vec<(u8, i64, u128)> {
    rev(v)
}

pub fn rev_rev_tuple(v: Vec<(u8, i64, u128)>) -> Vec<(u8, i64, u128)> {
    rev_rev(v)
}

pub fn rev_unit(v: Vec<()>) -> Vec<()> {
    rev(v)
}

pub fn rev_rev_unit(v: Vec<()>) -> Vec<()> {
    rev_rev(v)
}

pub fn empty() -> Vec<i32> {
    Vec::new()
}

pub fn empty_len() -> usize {
    empty().len()
}
