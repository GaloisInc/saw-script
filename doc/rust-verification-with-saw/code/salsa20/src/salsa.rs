//! Salsa20 stream cipher implementation.
//!
//! Adapted from the `ctr` crate.

// TODO(tarcieri): figure out how to unify this with the `ctr` crate (see #95)

// use crate::{
//     core::Core,
//     rounds::{Rounds, R12, R20, R8},
//     BLOCK_SIZE,
// };
use cipher::{
    consts::{U32, U8},
    // errors::{LoopError, OverflowError},
    // NewCipher, SeekNum, StreamCipher, StreamCipherSeek,
};
// use core::fmt;

#[cfg(docsrs)]
use cipher::generic_array::GenericArray;

/// Key type.
///
/// Implemented as an alias for [`GenericArray`].
///
/// (NOTE: all three round variants use the same key size)
pub type Key = cipher::generic_array::GenericArray<u8, U32>;
// pub type Key = cipher::CipherKey<Salsa20>;

/// Nonce type.
///
/// Implemented as an alias for [`GenericArray`].
pub type Nonce = cipher::generic_array::GenericArray<u8, U8>;
// pub type Nonce = cipher::Nonce<Salsa20>;

/*
/// Salsa20/8 stream cipher
/// (reduced-round variant of Salsa20 with 8 rounds, *not recommended*)
pub type Salsa8 = Salsa<R8>;

/// Salsa20/12 stream cipher
/// (reduced-round variant of Salsa20 with 12 rounds, *not recommended*)
pub type Salsa12 = Salsa<R12>;

/// Salsa20/20 stream cipher
/// (20 rounds; **recommended**)
pub type Salsa20 = Salsa<R20>;

/// Internal buffer
type Buffer = [u8; BLOCK_SIZE];

/// The Salsa20 family of stream ciphers
/// (implemented generically over a number of rounds).
///
/// We recommend you use the [`Salsa20`] (a.k.a. Salsa20/20) variant.
pub struct Salsa<R: Rounds> {
    /// Salsa core function initialized with a key and IV
    block: Core<R>,

    /// Buffer containing previous output
    buffer: Buffer,

    /// Position within buffer, or `None` if the buffer is not in use
    buffer_pos: u8,

    /// Current counter value relative to the start of the keystream
    counter: u64,
}

impl<R: Rounds> NewCipher for Salsa<R> {
    /// Key size in bytes
    type KeySize = U32;

    /// Nonce size in bytes
    type NonceSize = U8;

    fn new(key: &Key, nonce: &Nonce) -> Self {
        let block = Core::new(key, nonce);

        Self {
            block,
            buffer: [0u8; BLOCK_SIZE],
            buffer_pos: 0,
            counter: 0,
        }
    }
}

impl<R: Rounds> StreamCipher for Salsa<R> {
    fn try_apply_keystream(&mut self, mut data: &mut [u8]) -> Result<(), LoopError> {
        self.check_data_len(data)?;
        let pos = self.buffer_pos as usize;
        debug_assert!(BLOCK_SIZE > pos);

        let mut counter = self.counter;
        // xor with leftover bytes from the last call if any
        if pos != 0 {
            if data.len() < BLOCK_SIZE - pos {
                let n = pos + data.len();
                xor(data, &self.buffer[pos..n]);
                self.buffer_pos = n as u8;
                return Ok(());
            } else {
                let (l, r) = data.split_at_mut(BLOCK_SIZE - pos);
                data = r;
                xor(l, &self.buffer[pos..]);
                counter += 1;
            }
        }

        let mut chunks = data.chunks_exact_mut(BLOCK_SIZE);
        for chunk in &mut chunks {
            self.block.apply_keystream(counter, chunk);
            counter += 1;
        }

        let rem = chunks.into_remainder();
        self.buffer_pos = rem.len() as u8;
        self.counter = counter;
        if !rem.is_empty() {
            self.block.counter_setup(counter);
            self.block.generate(&mut self.buffer);
            xor(rem, &self.buffer[..rem.len()]);
        }

        Ok(())
    }
}

impl<R: Rounds> StreamCipherSeek for Salsa<R> {
    fn try_current_pos<T: SeekNum>(&self) -> Result<T, OverflowError> {
        T::from_block_byte(self.counter, self.buffer_pos, BLOCK_SIZE as u8)
    }

    fn try_seek<T: SeekNum>(&mut self, pos: T) -> Result<(), LoopError> {
        let res = pos.to_block_byte(BLOCK_SIZE as u8)?;
        self.counter = res.0;
        self.buffer_pos = res.1;
        if self.buffer_pos != 0 {
            self.block.counter_setup(self.counter);
            self.block.generate(&mut self.buffer);
        }
        Ok(())
    }
}

impl<R: Rounds> Salsa<R> {
    fn check_data_len(&self, data: &[u8]) -> Result<(), LoopError> {
        let leftover_bytes = BLOCK_SIZE - self.buffer_pos as usize;
        if data.len() < leftover_bytes {
            return Ok(());
        }
        let blocks = 1 + (data.len() - leftover_bytes) / BLOCK_SIZE;
        self.counter
            .checked_add(blocks as u64)
            .ok_or(LoopError)
            .map(|_| ())
    }
}

impl<R: Rounds> fmt::Debug for Salsa<R> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "Cipher {{ .. }}")
    }
}

#[inline(always)]
fn xor(buf: &mut [u8], key: &[u8]) {
    debug_assert_eq!(buf.len(), key.len());
    for (a, b) in buf.iter_mut().zip(key) {
        *a ^= *b;
    }
}
*/
