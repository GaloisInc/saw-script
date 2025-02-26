//! The Salsa20 stream cipher.
//!
//! Cipher functionality is accessed using traits from re-exported
//! [`cipher`](https://docs.rs/cipher) crate.
//!
//! # Security Warning
//!
//! This crate does not ensure ciphertexts are authentic! Thus ciphertext integrity
//! is not verified, which can lead to serious vulnerabilities!
//!
//! USE AT YOUR OWN RISK!
//!
//! # Diagram
//!
//! This diagram illustrates the Salsa quarter round function.
//! Each round consists of four quarter-rounds:
//!
//! <img src="https://raw.githubusercontent.com/RustCrypto/meta/master/img/stream-ciphers/salsa20.png" width="300px">
//!
//! Legend:
//!
//! - ⊞ add
//! - ‹‹‹ rotate
//! - ⊕ xor
//!
//! # Usage
//!
//! ```
//! use salsa20::{Salsa20, Key, Nonce};
//! use salsa20::cipher::{NewCipher, StreamCipher, StreamCipherSeek};
//!
//! let mut data = [1, 2, 3, 4, 5, 6, 7];
//!
//! let key = Key::from_slice(b"an example very very secret key.");
//! let nonce = Nonce::from_slice(b"a nonce.");
//!
//! // create cipher instance
//! let mut cipher = Salsa20::new(&key, &nonce);
//!
//! // apply keystream (encrypt)
//! cipher.apply_keystream(&mut data);
//! assert_eq!(data, [182, 14, 133, 113, 210, 25, 165]);
//!
//! // seek to the keystream beginning and apply it again to the `data` (decrypt)
//! cipher.seek(0);
//! cipher.apply_keystream(&mut data);
//! assert_eq!(data, [1, 2, 3, 4, 5, 6, 7]);
//! ```

#![no_std]
#![doc(
    html_logo_url = "https://raw.githubusercontent.com/RustCrypto/meta/master/logo.svg",
    html_favicon_url = "https://raw.githubusercontent.com/RustCrypto/meta/master/logo.svg"
)]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![deny(unsafe_code)]
#![warn(missing_docs, rust_2018_idioms, trivial_casts, unused_qualifications)]

pub use cipher;

mod core;
mod rounds;
mod salsa;
// #[cfg(feature = "xsalsa20")]
// mod xsalsa;

pub use crate::salsa::{Key, Nonce};
// pub use crate::salsa::{Key, Nonce, Salsa, Salsa12, Salsa20, Salsa8};

// #[cfg(feature = "expose-core")]
pub use crate::{
    core::Core,
    rounds::{R12, R20, R8},
};

// #[cfg(feature = "hsalsa20")]
// pub use crate::xsalsa::hsalsa20;
//
// #[cfg(feature = "xsalsa20")]
// pub use crate::xsalsa::{XNonce, XSalsa20};

/// Size of a Salsa20 block in bytes
pub const BLOCK_SIZE: usize = 64;

/// Size of a Salsa20 key in bytes
pub const KEY_SIZE: usize = 32;

/// Number of 32-bit words in the Salsa20 state
const STATE_WORDS: usize = 16;

/// State initialization constant ("expand 32-byte k")
const CONSTANTS: [u32; 4] = [0x6170_7865, 0x3320_646e, 0x7962_2d32, 0x6b20_6574];
