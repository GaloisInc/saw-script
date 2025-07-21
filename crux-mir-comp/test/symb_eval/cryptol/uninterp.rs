extern crate crucible;
use crucible::*;

const PATH: &str = "test::symb_eval::cryptol::uninterp";

fn mult(mut x: u64, mut y: u64) -> u64 {
    let mut acc = 0;
    while y > 0 {
        if y & 1 == 1 {
            acc ^= x;
        }

        y >>= 1;

        if x >= 0x8000000000000000 {
            x = (x << 1) ^ 0x1b;
        } else {
            x <<= 1;
        }
    }

    acc
}

fn pow(base: u64, exponent: u64) -> u64 {
    let mut acc = 1;

    for i in 0..64 {
        acc = mult(acc, acc);
        if (0x8000000000000000 >> i) & exponent != 0 {
            acc = mult(base, acc); // argument order matters and must match the spec
        }
    }

    acc
}

mod cry {
    super::crucible::cryptol! {
        path "test::symb_eval::cryptol::uninterp";
        pub fn pow(x: u64, y: u64) -> u64 = "pow";
        pub fn mult(x: u64, y: u64) -> u64 = "mult";
    }
}

#[crux::test]
fn pow_equiv() {
    crucible::cryptol::uninterp("test::symb_eval::cryptol::uninterp::mult");
    override_(mult, cry::mult);
    let x = Symbolic::symbolic("x");
    let y = Symbolic::symbolic("y");
    let expected = cry::pow(x, y);
    let actual = pow(x, y);
    crucible_assert!(actual == expected);
}
