extern crate crucible;
use crucible::*;
use std::num::Wrapping;

mod cry {
    use super::crucible::cryptol;

    cryptol! {
        path "test::symb_eval::cryptol::Issue3308";

        pub fn compress_t1(e: u32, f: u32, g: u32, h: u32, k_t: u32, w_t: u32) -> u32
            = r#" \e f g h k_t (w_t : [32]) -> h + S1 e + Ch e f g + k_t + w_t "#;
        pub fn compress_t2(a: u32, b: u32, c: u32) -> u32
            = r#" \a b (c : [32]) -> S0 a + Maj a b c "#;
    }
}

const CHAINING_WORDS: usize = 8;

const K: &'static [Wrapping<u32>] = &[
    Wrapping(0x428a2f98),
    Wrapping(0x71374491),
    Wrapping(0xb5c0fbcf),
    Wrapping(0xe9b5dba5),
    Wrapping(0x3956c25b),
    Wrapping(0x59f111f1),
    Wrapping(0x923f82a4),
    Wrapping(0xab1c5ed5),
    Wrapping(0xd807aa98),
    Wrapping(0x12835b01),
    Wrapping(0x243185be),
    Wrapping(0x550c7dc3),
    Wrapping(0x72be5d74),
    Wrapping(0x80deb1fe),
    Wrapping(0x9bdc06a7),
    Wrapping(0xc19bf174),
    Wrapping(0xe49b69c1),
    Wrapping(0xefbe4786),
    Wrapping(0x0fc19dc6),
    Wrapping(0x240ca1cc),
    Wrapping(0x2de92c6f),
    Wrapping(0x4a7484aa),
    Wrapping(0x5cb0a9dc),
    Wrapping(0x76f988da),
    Wrapping(0x983e5152),
    Wrapping(0xa831c66d),
    Wrapping(0xb00327c8),
    Wrapping(0xbf597fc7),
    Wrapping(0xc6e00bf3),
    Wrapping(0xd5a79147),
    Wrapping(0x06ca6351),
    Wrapping(0x14292967),
    Wrapping(0x27b70a85),
    Wrapping(0x2e1b2138),
    Wrapping(0x4d2c6dfc),
    Wrapping(0x53380d13),
    Wrapping(0x650a7354),
    Wrapping(0x766a0abb),
    Wrapping(0x81c2c92e),
    Wrapping(0x92722c85),
    Wrapping(0xa2bfe8a1),
    Wrapping(0xa81a664b),
    Wrapping(0xc24b8b70),
    Wrapping(0xc76c51a3),
    Wrapping(0xd192e819),
    Wrapping(0xd6990624),
    Wrapping(0xf40e3585),
    Wrapping(0x106aa070),
    Wrapping(0x19a4c116),
    Wrapping(0x1e376c08),
    Wrapping(0x2748774c),
    Wrapping(0x34b0bcb5),
    Wrapping(0x391c0cb3),
    Wrapping(0x4ed8aa4a),
    Wrapping(0x5b9cca4f),
    Wrapping(0x682e6ff3),
    Wrapping(0x748f82ee),
    Wrapping(0x78a5636f),
    Wrapping(0x84c87814),
    Wrapping(0x8cc70208),
    Wrapping(0x90befffa),
    Wrapping(0xa4506ceb),
    Wrapping(0xbef9a3f7),
    Wrapping(0xc67178f2),
];

fn compress_words(
    mut H: [Wrapping<u32>; CHAINING_WORDS],
    W: &[Wrapping<u32>],
) -> [Wrapping<u32>; CHAINING_WORDS] {
    let mut a = H[0];
    let mut b = H[1];
    let mut c = H[2];
    let mut d = H[3];
    let mut e = H[4];
    let mut f = H[5];
    let mut g = H[6];
    let mut h = H[7];

    assert_eq!(K.len(), W.len());
    for (idx, (Kt, Wt)) in K.iter().zip(W.iter()).enumerate() {
        print_str(&*format!("=== Begin loop iteration {:?} ========", idx));
        let T1 = cryptol_compress_t1(e, f, g, h, *Kt, *Wt);
        let T2 = cryptol_compress_t2(a, b, c);
        h = g;
        g = f;
        f = e;
        e = d + T1;
        d = c;
        c = b;
        b = a;
        a = T1 + T2;
    }

    H[0] += a;
    H[1] += b;
    H[2] += c;
    H[3] += d;
    H[4] += e;
    H[5] += f;
    H[6] += g;
    H[7] += h;

    H
}

fn cryptol_compress_t1(
    e: Wrapping<u32>,
    f: Wrapping<u32>,
    g: Wrapping<u32>,
    h: Wrapping<u32>,
    k_t: Wrapping<u32>,
    w_t: Wrapping<u32>,
) -> Wrapping<u32> {
    Wrapping(cry::compress_t1(e.0, f.0, g.0, h.0, k_t.0, w_t.0))
}

fn cryptol_compress_t2(
    a: Wrapping<u32>,
    b: Wrapping<u32>,
    c: Wrapping<u32>,
) -> Wrapping<u32> {
    Wrapping(cry::compress_t2(a.0, b.0, c.0))
}

#[crux::test]
pub fn compress_words_simulate() {
    let state = <[Wrapping<u32>; 8]>::symbolic("state");
    let schedule = <[Wrapping<u32>; 64]>::symbolic("schedule");
    compress_words(state, &schedule as &[_]);
}
