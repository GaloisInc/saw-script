
// Evaluate a vector of arguments to a new environment
pub fn xor_swap_rust (x:&mut i64, y:&mut i64) {
    *x = *x ^ *y;
    *y = *x ^ *y;
    *x = *x ^ *y;
}

pub fn main () {
    let mut x:i64 = 0;
    let mut y:i64 = 1;
    xor_swap_rust (&mut x, &mut y);
}
