//! The Salsa20 core function.

use crate::{rounds::Rounds, Key, Nonce, BLOCK_SIZE, CONSTANTS, STATE_WORDS};
use core::{convert::TryInto, marker::PhantomData, /* mem */};

/// The Salsa20 core function.
// TODO(tarcieri): zeroize support
pub struct Core<R: Rounds> {
    /// Internal state of the core function
    state: [u32; STATE_WORDS],

    /// Number of rounds to perform
    rounds: PhantomData<R>,
}

impl<R: Rounds> Core<R> {
    /// Initialize core function with the given key and IV
    pub fn new(key: &Key, iv: &Nonce) -> Self {
        Self::new_raw(key.as_ref(), iv.as_ref())
    }

    /// Initialize core function with the given key and IV
    pub fn new_raw(key: &[u8; 32], iv: &[u8; 8]) -> Self {
        #[allow(unsafe_code)]
        //let mut state: [u32; STATE_WORDS] = unsafe { mem::zeroed() };
        let mut state: [u32; STATE_WORDS] = [0; STATE_WORDS];
        state[0] = CONSTANTS[0];

        for (i, chunk) in key[..16].chunks(4).enumerate() {
            state[1 + i] = u32::from_le_bytes(chunk.try_into().unwrap());
        }

        state[5] = CONSTANTS[1];

        for (i, chunk) in iv.chunks(4).enumerate() {
            state[6 + i] = u32::from_le_bytes(chunk.try_into().unwrap());
        }

        state[8] = 0;
        state[9] = 0;
        state[10] = CONSTANTS[2];

        for (i, chunk) in key[16..].chunks(4).enumerate() {
            state[11 + i] = u32::from_le_bytes(chunk.try_into().unwrap());
        }

        state[15] = CONSTANTS[3];

        Self {
            state,
            rounds: PhantomData,
        }
    }

    /// Generate output, overwriting data already in the buffer
    pub fn generate(&mut self, output: &mut [u8]) {
        debug_assert_eq!(output.len(), BLOCK_SIZE);

        let mut state = self.state;
        self.rounds(&mut state);

        for (i, chunk) in output.chunks_mut(4).enumerate() {
            chunk.copy_from_slice(&state[i].to_le_bytes());
        }
    }

    /// Apply generated keystream to the output buffer
    pub fn apply_keystream(&mut self, counter: u64, output: &mut [u8]) {
        debug_assert_eq!(output.len(), BLOCK_SIZE);
        self.counter_setup(counter);

        let mut state = self.state;
        self.rounds(&mut state);

        for (i, chunk) in output.chunks_mut(4).enumerate() {
            for (a, b) in chunk.iter_mut().zip(&state[i].to_le_bytes()) {
                *a ^= *b;
            }
        }
    }

    #[inline]
    pub(crate) fn counter_setup(&mut self, counter: u64) {
        self.state[8] = (counter & 0xffff_ffff) as u32;
        self.state[9] = ((counter >> 32) & 0xffff_ffff) as u32;
    }

    /// Run the 20 rounds (i.e. 10 double rounds) of Salsa20
    #[inline]
    fn rounds(&mut self, state: &mut [u32; STATE_WORDS]) {
        for _ in 0..(R::COUNT / 2) {
            // column rounds
            quarter_round(0, 4, 8, 12, state);
            quarter_round(5, 9, 13, 1, state);
            quarter_round(10, 14, 2, 6, state);
            quarter_round(15, 3, 7, 11, state);

            // diagonal rounds
            quarter_round(0, 1, 2, 3, state);
            quarter_round(5, 6, 7, 4, state);
            quarter_round(10, 11, 8, 9, state);
            quarter_round(15, 12, 13, 14, state);
        }

        for (s1, s0) in state.iter_mut().zip(&self.state) {
            *s1 = s1.wrapping_add(*s0);
        }
    }
}

impl<R: Rounds> From<[u32; STATE_WORDS]> for Core<R> {
    fn from(state: [u32; STATE_WORDS]) -> Core<R> {
        Self {
            state,
            rounds: PhantomData,
        }
    }
}

#[inline]
#[allow(clippy::many_single_char_names)]
pub(crate) fn quarter_round(
    a: usize,
    b: usize,
    c: usize,
    d: usize,
    state: &mut [u32; STATE_WORDS],
) {
    let mut t: u32;

    t = state[a].wrapping_add(state[d]);
    state[b] ^= t.rotate_left(7) as u32;

    t = state[b].wrapping_add(state[a]);
    state[c] ^= t.rotate_left(9) as u32;

    t = state[c].wrapping_add(state[b]);
    state[d] ^= t.rotate_left(13) as u32;

    t = state[d].wrapping_add(state[c]);
    state[a] ^= t.rotate_left(18) as u32;
}

#[inline]
fn double_round(
    state: &mut [u32; STATE_WORDS],
) {
    // column rounds
    quarter_round(0, 4, 8, 12, state);
    quarter_round(5, 9, 13, 1, state);
    quarter_round(10, 14, 2, 6, state);
    quarter_round(15, 3, 7, 11, state);

    // diagonal rounds
    quarter_round(0, 1, 2, 3, state);
    quarter_round(5, 6, 7, 4, state);
    quarter_round(10, 11, 8, 9, state);
    quarter_round(15, 12, 13, 14, state);
}


#[cfg(crux)]
mod crux_test {
    extern crate crucible;
    use crucible::*;
    // use crucible::method_spec::{MethodSpec, MethodSpecBuilder, clobber_globals};
    use super::*;

    /*
    mod cry {
        use super::crucible::cryptol;
        cryptol! {
            path "/home/stuart/work/cryptol-specs/Primitive/Symmetric/Cipher/Stream/Salsa20.cry";
            pub fn quarter_round(x: [u32; 4]) -> [u32; 4] = "quarterround";
            pub fn double_round(x: [u32; 16]) -> [u32; 16] = "doubleround";
            pub fn rounds(x: [u32; 16]) -> [u32; 16];
            pub fn salsa20(x: [u8; 64]) -> [u8; 64] = "Salsa20";

            pub fn u32_from_bytes_le(x: [u8; 4]) -> u32 = "littleendian";
            pub fn u32_to_bytes_le(x: u32) -> [u8; 4] = "littleendian_inverse";

            pub fn expand(k: [u8; 32], n: [u8; 16]) -> [u8; 64] = "Salsa20_expansion_key32";

            pub fn encrypt_block(k: [u8; 32], v: [u8; 8], o: u64, m: [u8; 64]) -> [u8; 64]
                = "Salsa20_encrypt_block_key32";
        }
    }

    fn state_to_bytes<F: Fn(u32) -> [u8; 4]>(f: F, x: [u32; 16]) -> [u8; 64] {
        let mut out = [0; 64];
        for i in 0 .. 16 {
            out[i * 4 .. (i + 1) * 4].copy_from_slice(&f(x[i]));
        }
        out
    }

    fn state_from_bytes<F: Fn([u8; 4]) -> u32>(f: F, x: [u8; 64]) -> [u32; 16] {
        let mut out = [0; 16];
        for i in 0 .. 16 {
            let mut buf = [0; 4];
            buf.copy_from_slice(&x[i * 4 .. (i + 1) * 4]);
            out[i] = f(buf);
        }
        out
    }

    fn state_to_bytes_cryptol(x: [u32; 16]) -> [u8; 64] {
        state_to_bytes(cry::u32_to_bytes_le, x)
    }

    fn state_from_bytes_cryptol(x: [u8; 64]) -> [u32; 16] {
        state_from_bytes(cry::u32_from_bytes_le, x)
    }

    fn state_to_bytes_rust(x: [u32; 16]) -> [u8; 64] {
        state_to_bytes(u32::to_le_bytes, x)
    }

    fn state_from_bytes_rust(x: [u8; 64]) -> [u32; 16] {
        state_from_bytes(u32::from_le_bytes, x)
    }

    #[crux::test]
    fn test_state_to_bytes_eq() {
        let state = <[u32; 16]>::symbolic("state");
        crucible_assert!(
            (&state_to_bytes_cryptol(state) as &[_]) ==
            (&state_to_bytes_rust(state) as &[_]));
    }

    #[crux::test]
    fn test_state_to_from_bytes() {
        let state = <[u32; 16]>::symbolic("state");
        crucible_assert!(state == state_from_bytes_cryptol(state_to_bytes_cryptol(state)));
    }

    #[crux::test]
    fn test_state_from_to_bytes() {
        let mut state = [0; 64];
        for b in state.iter_mut() {
            *b = u8::symbolic("state");
        }
        crucible_assert!((&state as &[_]) ==
                         (&state_to_bytes_cryptol(state_from_bytes_cryptol(state)) as &[_]));
    }

    #[crux::test]
    fn test_salsa20_rounds_from_bytes() {
        let mut state0 = [0; 64];
        for b in state0.iter_mut() {
            *b = u8::symbolic("state");
        }
        crucible_assert!(
            state_from_bytes_cryptol(cry::salsa20(state0)) ==
            cry::rounds(state_from_bytes_cryptol(state0))
        )
    }

    #[crux::test]
    fn test_salsa20_rounds_to_from_bytes() {
        let mut state0 = [0; 64];
        for b in state0.iter_mut() {
            *b = u8::symbolic("state");
        }
        let x = cry::salsa20(state0);
        let y = state_to_bytes_cryptol(cry::rounds(state_from_bytes_cryptol(state0)));
        assert!(x.len() == y.len());
        crucible_assert!(x.iter().eq(y.iter()));
    }

    fn quarter_round_cryptol(
        a: usize,
        b: usize,
        c: usize,
        d: usize,
        state: &mut [u32; STATE_WORDS],
    ) {
        let vals0 = [state[a], state[b], state[c], state[d]];
        let vals1 = cry::quarter_round(vals0);
        state[a] = vals1[0];
        state[b] = vals1[1];
        state[c] = vals1[2];
        state[d] = vals1[3];
    }

    fn rounds_cryptol(
        state0: [u32; 16],
    ) -> [u32; 16] {
        let mut state_bytes0 = [0; 64];
        for (i, &x) in state0.iter().enumerate() {
            state_bytes0[i * 4 .. (i + 1) * 4].copy_from_slice(&x.to_le_bytes());
        }

        let state_bytes1 = cry::salsa20(state_bytes0);
        let mut state1 = [0; 16];
        for (i, x) in state1.iter_mut().enumerate() {
            let mut arr = [0; 4];
            arr.copy_from_slice(&state_bytes1[i * 4 .. (i + 1) * 4]);
            *x = u32::from_le_bytes(arr);
        }

        state1
    }

    /// There are eight sets of indices that are used with the `quarter_round` function; this
    /// function chooses one such set arbitrarily.
    fn quarter_round_indices() -> (usize, usize, usize, usize) {
        let indices = Symbolic::symbolic("indices");
        crucible_assume!(
            indices == (0, 1, 2, 3) ||
            indices == (5, 6, 7, 4) ||
            indices == (10, 11, 8, 9) ||
            indices == (15, 12, 13, 14) ||
            indices == (0, 4, 8, 12) ||
            indices == (5, 9, 13, 1) ||
            indices == (10, 14, 2, 6) ||
            indices == (15, 3, 7, 11)
        );
        indices
    }

    #[crux::test]
    fn quarter_round_test() {
        let state0 = <[u32; STATE_WORDS]>::symbolic("state");
        let (a, b, c, d) = quarter_round_indices();

        let mut state1_real = state0;
        quarter_round(a, b, c, d, &mut state1_real);

        let mut state1_cryptol = state0;
        quarter_round_cryptol(a, b, c, d, &mut state1_cryptol);

        crucible_assert!(state1_real == state1_cryptol);
    }

    fn quarter_round_spec() -> MethodSpec {
        let state0 = <[u32; STATE_WORDS]>::symbolic("state");
        let (a, b, c, d) = quarter_round_indices();

        let mut state1_real = state0;
        //quarter_round(a, b, c, d, &mut state1_real);
        let mut msb = MethodSpecBuilder::new(quarter_round);
        msb.add_arg(&a);
        msb.add_arg(&b);
        msb.add_arg(&c);
        msb.add_arg(&d);
        msb.add_arg(& &mut state1_real);
        msb.gather_assumes();

        let mut state1_cryptol = state0;
        quarter_round_cryptol(a, b, c, d, &mut state1_cryptol);

        crucible_assert!(state1_real == state1_cryptol);

        msb.set_return(&());
        msb.gather_asserts();
        msb.finish()
    }
    */

    #[crux::test]
    fn double_round_test() {
        //quarter_round_spec().enable();

        let state0 = <[u32; STATE_WORDS]>::symbolic("state");

        let mut state1_real = state0;
        double_round(&mut state1_real);

        // crucible_assert!(state1_real == cry::double_round(state0));
    }

    /*
    fn double_round_spec() -> MethodSpec {
        let state0 = <[u32; STATE_WORDS]>::symbolic("state");

        let mut state1_real = state0;
        //double_round(&mut state1_real);
        let mut msb = MethodSpecBuilder::new(double_round);
        msb.add_arg(& &mut state1_real);
        msb.gather_assumes();

        crucible_assert!(state1_real == cry::double_round(state0));

        msb.set_return(&());
        msb.gather_asserts();
        msb.finish()
    }
    */

    /*
    #[crux::test]
    fn rounds_test() {
        //double_round_spec().enable();

        let state0 = <[u32; STATE_WORDS]>::symbolic("state");

        let mut core = Core::<crate::rounds::R20> {
            state: state0,
            rounds: PhantomData,
        };
        let mut state_copy = core.state;
        core.rounds(&mut state_copy);

        crucible_assert!(state_copy == cry::rounds(state0));
    }
    */

    /*
    #[crux::test]
    fn rounds_test() {
        //double_round_spec().enable();

        let mut state0_bytes = [0; 64];
        for b in state0_bytes.iter_mut() {
            *b = u8::symbolic("state");
        }
        let state0 = state_from_bytes_rust(state0_bytes);

        let mut core = Core::<crate::rounds::R20> {
            state: state0,
            rounds: PhantomData,
        };
        let mut state_copy = core.state;
        core.rounds(&mut state_copy);

        crucible_assert!(
            state_to_bytes_rust(state_copy).iter()
                .eq(cry::salsa20(state0_bytes).iter())
        );
    }

    #[crux::test]
    fn expansion_test() {
        let key = <[u8; 32]>::symbolic("key");
        let nonce = <[u8; 8]>::symbolic("nonce");
        let counter = <[u8; 8]>::symbolic("counter");

        let mut core = Core::<crate::rounds::R20>::new_raw(&key, &nonce);
        core.counter_setup(u64::from_le_bytes(counter));
        let mut state = core.state;
        core.rounds(&mut state);

        let mut nonce_and_counter = [0; 16];
        nonce_and_counter[0..8].copy_from_slice(&nonce);
        nonce_and_counter[8..16].copy_from_slice(&counter);
        let expansion = cry::expand(key, nonce_and_counter);

        crucible_assert!(
            state.iter()
                .eq(state_from_bytes_rust(expansion).iter())
        );
    }
    */

    #[crux::test]
    fn apply_keystream_test() {
        let key = <[u8; 32]>::symbolic("key");
        let nonce = <[u8; 8]>::symbolic("nonce");
        let counter = u64::symbolic("counter");
        let mut msg = [0; 64];
        for b in msg.iter_mut() {
            *b = u8::symbolic("msg");
        }

        let mut core = Core::<crate::rounds::R20>::new_raw(&key, &nonce);
        let mut msg1 = msg;
        core.apply_keystream(counter, &mut msg1);

        // let msg2 = cry::encrypt_block(key, nonce, counter, msg);

        // crucible_assert!(
        //     msg1.iter().eq(msg2.iter())
        // );
    }

    #[crux::test]
    fn apply_keystream_test8() {
        let key = <[u8; 32]>::symbolic("key");
        let nonce = <[u8; 8]>::symbolic("nonce");
        let counter = u64::symbolic("counter");
        let mut msg = [0; 64];
        for b in msg.iter_mut() {
            *b = u8::symbolic("msg");
        }

        let mut core = Core::<crate::rounds::R8>::new_raw(&key, &nonce);
        let mut msg1 = msg;
        core.apply_keystream(counter, &mut msg1);

        // let msg2 = cry::encrypt_block(key, nonce, counter, msg);

        // crucible_assert!(
        //     msg1.iter().eq(msg2.iter())
        // );
    }

}
