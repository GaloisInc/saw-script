struct BI {
    i: [[i32; 4]; 2],
}

#[inline(never)]
#[no_mangle]
fn f (w: &mut BI) {
    for row in w.i.iter_mut() {
        for col in row.iter_mut() {
            *col = 0;
        }
    }
}

fn main() {
    let x = &mut BI{i: [[0 as i32; 4]; 2]};
    f(x);
    println!("{}", x.i[1][3]);
}

