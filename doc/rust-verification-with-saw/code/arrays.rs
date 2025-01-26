pub fn index(arr: [u32; 3], idx: usize) -> u32 {
    arr[idx]
}

pub fn index_ref_arr(arr: [&u32; 3], idx: usize) -> u32 {
    *arr[idx]
}
