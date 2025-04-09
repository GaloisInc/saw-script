extern crate crucible;
use crucible::*;
use crucible::cryptol::munge;

#[derive(Clone)]
struct Point{
    x: u32,
    y: u32,
}

fn reflect(p: Point) -> Point {
    Point{x: p.y, y: p.x}
}

#[crux_test]
fn munge_struct_equiv_test() {
    let (x, y) = <(u32, u32)>::symbolic("p");
    let p2 = reflect(munge(Point{x, y}));
    crucible_assert!(p2.x == y);
}
