# 0002. Cryptography comes from a separate library over OpenSSL 3 (Q10)

Status: accepted, M2, 2026-09-22.

## Decision

- Crypto lives in its own repository, **leancrypto** (`../leancrypto`,
  tag `v0.1.0`), as `intent.md` asks. LeanAPI depends on it; nothing
  secret-dependent is implemented in LeanAPI.
- Secret-dependent operations (SHA-256, HMAC-SHA256, constant-time compare,
  random bytes, scrypt) go through a small C FFI to OpenSSL 3 libcrypto.
  Constant-time behaviour is OpenSSL's, not something proved in Lean.
- Encodings (base64, base64url, hex) are pure Lean and strict: each byte
  string has exactly one accepted encoding.
- libcrypto is statically linked into leancrypto's extern lib, so every
  executable depending on LeanAPI links without extra flags and has no
  runtime OpenSSL dependency. Rebuild to pick up OpenSSL security fixes.
- Password hashing: scrypt (`ln=15, r=8, p=1` default) with self-describing
  encoded parameters (`$scrypt$ln=..,r=..,p=..$salt$hash`) and
  `needsRehash` for upgrades. argon2id is a follow-up.
- JWT: HS256 only in 0.2. RS256, ES256 and JWKS fetching are follow-ups.

## Trust (for the evidence record)

Assumed, not proved: OpenSSL's implementations and their constant-time
properties; the OS random source behind `RAND_bytes`; the C binding code in
leancrypto; RFC test vectors act as checks (RFC 4231, RFC 7914, NIST SHA-256,
RFC 4648), not proofs.

## Deployment requirements

Build hosts need OpenSSL 3 with a static `libcrypto.a` (Homebrew `openssl@3`,
Debian `libssl-dev`, or `OPENSSL_DIR`). Runtime hosts need nothing extra.
