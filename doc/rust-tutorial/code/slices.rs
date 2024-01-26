pub fn sum_of_prefix(s: &[u32]) -> u32 {
    s[0].wrapping_add(s[1])
}

pub fn sum_of_prefix_examples() {
    let a1 = [1, 2];
    let s1 = &a1[..];
    let sum1 = sum_of_prefix(s1);

    let a2 = [1, 2, 3, 4, 5];
    let s2 = &a2[..];
    let sum2 = sum_of_prefix(s2);

    let a3 = [1, 2, 3, 4, 5];
    let s3 = &a3[0..2];
    let sum3 = sum_of_prefix(s3);
}
