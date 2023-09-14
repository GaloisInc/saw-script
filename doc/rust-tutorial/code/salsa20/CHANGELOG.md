# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/)
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## 0.7.2 (2020-11-11)
### Fixed
- `no_std` builds with `zeroize` feature enabled ([#189])

[#189]: https://github.com/RustCrypto/stream-ciphers/pull/189

## 0.7.1 (2020-10-18)
### Added
- `expose-core` feature ([#180])

[#180]: https://github.com/RustCrypto/stream-ciphers/pull/180

## 0.7.0 (2020-10-16)
### Changed
- Replace `block-cipher`/`stream-cipher` with `cipher` crate ([#177])
- Renamed `Cipher` to `Salsa` ([#177])

[#177]: https://github.com/RustCrypto/stream-ciphers/pull/177

## 0.6.0 (2020-08-25)
### Changed
- Bump `stream-cipher` dependency to v0.7 ([#161], [#164])

[#161]: https://github.com/RustCrypto/stream-ciphers/pull/161
[#164]: https://github.com/RustCrypto/stream-ciphers/pull/164

## 0.5.2 (2020-06-11)
### Changed
- Use `Key` and `Nonce` in usage docs ([#155])

### Fixed
- `stream-cipher` version requirement ([#152])

[#155]: https://github.com/RustCrypto/stream-ciphers/pull/155
[#152]: https://github.com/RustCrypto/stream-ciphers/pull/152

## 0.5.1 (2020-06-11)
### Added
- Documentation improvements ([#149])
- `Key`, `Nonce`, and `XNonce` type aliases ([#146])

### Changed
- Bump `stream-cipher` to v0.4.1 ([#148])

[#149]: https://github.com/RustCrypto/stream-ciphers/pull/149
[#148]: https://github.com/RustCrypto/stream-ciphers/pull/148
[#146]: https://github.com/RustCrypto/stream-ciphers/pull/146

## 0.5.0 (2020-06-06)
### Added
- `Salsa8` and `Salsa12` variants ([#133])

### Changed
- Upgrade to the `stream-cipher` v0.4 crate ([#125], [#138])

[#138]: https://github.com/RustCrypto/stream-ciphers/pull/138
[#133]: https://github.com/RustCrypto/stream-ciphers/pull/133
[#125]: https://github.com/RustCrypto/stream-ciphers/pull/125

## 0.4.1 (2020-02-25)
### Added
- `hsalsa20` feature ([#103])

[#103]: https://github.com/RustCrypto/stream-ciphers/pull/103

## 0.4.0 (2020-01-17)
### Changed
- Replace `salsa20-core` with `ctr`-derived buffering; MSRV 1.34+ ([#94])

[#94]: https://github.com/RustCrypto/stream-ciphers/pull/94

## 0.3.0 (2019-10-01)
### Added
- XSalsa20 ([#54])

[#54]: https://github.com/RustCrypto/stream-ciphers/pull/44

## 0.2.0 (2019-08-18)
### Added
- Improve documentation ([#17])
- Impl `SyncStreamCipher` ([#39])

### Changed
- Refactoring ([#38], [#44])

### Fixed
- Fix broken Cargo feature attributes ([#21])

[#44]: https://github.com/RustCrypto/stream-ciphers/pull/44
[#39]: https://github.com/RustCrypto/stream-ciphers/pull/39
[#38]: https://github.com/RustCrypto/stream-ciphers/pull/38
[#21]: https://github.com/RustCrypto/stream-ciphers/pull/21
[#17]: https://github.com/RustCrypto/stream-ciphers/pull/17

## 0.1.1 (2019-06-30)

### Added
- `#![no_std]` support

[#19]: https://github.com/RustCrypto/stream-ciphers/pull/19

## 0.1.0 (2019-06-24)

- Initial release
