/*
The C half of `Resources/Crypto/Sodium.lean`: every libsodium call this project
makes, and nothing else.

Each function here is the C side of one `@[extern]` in that file, and the Lean
file states the contract each one is assumed to satisfy. The rules this file
keeps to, which is what makes those contracts checkable by reading:

  * Every buffer whose length libsodium's contract fixes is checked here before
    the call. A primitive that reads `crypto_sign_PUBLICKEYBYTES` from a pointer
    reads them whatever the caller passed, so a key of the wrong size is a
    buffer over-read rather than a failed check, and Lean's `ByteArray` carries
    a length that C can ask for.
  * A failure is a value, never a crash and never a partial result: the byte
    functions return an empty `ByteArray` and the opening functions return
    `none`. Lean turns an empty answer into a failed check everywhere it can
    arise, because no output this file produces is legitimately empty.
  * Nothing here allocates a Lean object it does not return, and the one buffer
    that is allocated before it is known to be wanted (a decryption's plaintext)
    is released on the failing path.
  * Secret keys that live on the stack are wiped with `sodium_memzero` before
    returning, so a key pair derived from a seed does not stay in a stack frame
    the next call writes over piecemeal.
*/

#include <lean/lean.h>
#include <sodium.h>
#include <string.h>

#ifdef _WIN32
#define RESOURCES_API __declspec(dllexport)
#else
#define RESOURCES_API __attribute__((visibility("default")))
#endif

/* A fresh Lean `ByteArray` holding `n` bytes from `src`. */
static lean_obj_res resources_bytes(const uint8_t *src, size_t n) {
  lean_object *out = lean_alloc_sarray(1, n, n);
  if (n > 0) {
    memcpy(lean_sarray_cptr(out), src, n);
  }
  return out;
}

/* The empty `ByteArray`, which is how every byte-returning function here fails. */
static lean_obj_res resources_no_bytes(void) { return lean_alloc_sarray(1, 0, 0); }

/* `some v`, for a function returning `Option ByteArray`. */
static lean_obj_res resources_some(lean_obj_arg v) {
  lean_object *out = lean_alloc_ctor(1, 1, 0);
  lean_ctor_set(out, 0, v);
  return out;
}

/* `none`, for a function returning `Option ByteArray`. */
static lean_obj_res resources_none(void) { return lean_box(0); }

/* One `Unit -> USize` binding returning a libsodium compile-time constant. */
#define RESOURCES_SODIUM_SIZE(fn, constant)                                                        \
  RESOURCES_API size_t fn(lean_object *unit) {                                                     \
    (void) unit;                                                                                   \
    return (size_t) (constant);                                                                    \
  }

/* ---------------------------------------------------------------- start-up */

/*
`sodium_init`. Idempotent, but Lean calls it exactly once, from the module
initializer of `Resources/Crypto/Sodium.lean`, before any other function here
can be reached.
*/
RESOURCES_API lean_obj_res resources_sodium_init(lean_object *world) {
  (void) world;
  if (sodium_init() < 0) {
    return lean_io_result_mk_error(
        lean_mk_io_user_error(lean_mk_string("libsodium failed to initialise")));
  }
  return lean_io_result_mk_ok(lean_box(0));
}

/* ----------------------------------------------------------------- sizes */

RESOURCES_SODIUM_SIZE(resources_sodium_sign_pk_size, crypto_sign_PUBLICKEYBYTES)
RESOURCES_SODIUM_SIZE(resources_sodium_sign_sk_size, crypto_sign_SECRETKEYBYTES)
RESOURCES_SODIUM_SIZE(resources_sodium_sign_seed_size, crypto_sign_SEEDBYTES)
RESOURCES_SODIUM_SIZE(resources_sodium_signature_size, crypto_sign_BYTES)
RESOURCES_SODIUM_SIZE(resources_sodium_box_pk_size, crypto_box_PUBLICKEYBYTES)
RESOURCES_SODIUM_SIZE(resources_sodium_box_sk_size, crypto_box_SECRETKEYBYTES)
RESOURCES_SODIUM_SIZE(resources_sodium_box_seed_size, crypto_box_SEEDBYTES)
RESOURCES_SODIUM_SIZE(resources_sodium_seal_overhead, crypto_box_SEALBYTES)
RESOURCES_SODIUM_SIZE(resources_sodium_aead_key_size, crypto_aead_xchacha20poly1305_ietf_KEYBYTES)
RESOURCES_SODIUM_SIZE(resources_sodium_aead_nonce_size,
                      crypto_aead_xchacha20poly1305_ietf_NPUBBYTES)
RESOURCES_SODIUM_SIZE(resources_sodium_aead_tag_size, crypto_aead_xchacha20poly1305_ietf_ABYTES)
RESOURCES_SODIUM_SIZE(resources_sodium_pwhash_salt_size, crypto_pwhash_SALTBYTES)
RESOURCES_SODIUM_SIZE(resources_sodium_pwhash_ops_interactive, crypto_pwhash_OPSLIMIT_INTERACTIVE)
RESOURCES_SODIUM_SIZE(resources_sodium_pwhash_mem_interactive, crypto_pwhash_MEMLIMIT_INTERACTIVE)

/* --------------------------------------------------------------- randomness */

/* `randombytes_buf`: `n` bytes from the operating system's generator. */
RESOURCES_API lean_obj_res resources_sodium_random_bytes(size_t n, lean_object *world) {
  (void) world;
  lean_object *out = lean_alloc_sarray(1, n, n);
  if (n > 0) {
    randombytes_buf(lean_sarray_cptr(out), n);
  }
  return lean_io_result_mk_ok(out);
}

/* ------------------------------------------------------------------ Ed25519 */

/*
`crypto_sign_seed_keypair`: the public key followed by the secret key, 96 bytes
in all. A seed of any other length is refused, because the call reads exactly
`crypto_sign_SEEDBYTES` from the pointer it is given.
*/
RESOURCES_API lean_obj_res resources_sodium_sign_seed_keypair(b_lean_obj_arg seed) {
  if (lean_sarray_size(seed) != crypto_sign_SEEDBYTES) {
    return resources_no_bytes();
  }
  uint8_t pk[crypto_sign_PUBLICKEYBYTES];
  uint8_t sk[crypto_sign_SECRETKEYBYTES];
  if (crypto_sign_seed_keypair(pk, sk, lean_sarray_cptr(seed)) != 0) {
    sodium_memzero(sk, sizeof sk);
    return resources_no_bytes();
  }
  lean_object *out = lean_alloc_sarray(1, sizeof pk + sizeof sk, sizeof pk + sizeof sk);
  memcpy(lean_sarray_cptr(out), pk, sizeof pk);
  memcpy(lean_sarray_cptr(out) + sizeof pk, sk, sizeof sk);
  sodium_memzero(sk, sizeof sk);
  return out;
}

/* `crypto_sign_detached`: a 64-byte signature of `msg` under a 64-byte secret key. */
RESOURCES_API lean_obj_res resources_sodium_sign(b_lean_obj_arg sk, b_lean_obj_arg msg) {
  if (lean_sarray_size(sk) != crypto_sign_SECRETKEYBYTES) {
    return resources_no_bytes();
  }
  uint8_t sig[crypto_sign_BYTES];
  if (crypto_sign_detached(sig, NULL, lean_sarray_cptr(msg), lean_sarray_size(msg),
                           lean_sarray_cptr(sk)) != 0) {
    return resources_no_bytes();
  }
  return resources_bytes(sig, sizeof sig);
}

/* `crypto_sign_verify_detached`: whether this signature is this key's, over these bytes. */
RESOURCES_API uint8_t resources_sodium_verify(b_lean_obj_arg pk, b_lean_obj_arg msg,
                                              b_lean_obj_arg sig) {
  if (lean_sarray_size(pk) != crypto_sign_PUBLICKEYBYTES ||
      lean_sarray_size(sig) != crypto_sign_BYTES) {
    return 0;
  }
  return crypto_sign_verify_detached(lean_sarray_cptr(sig), lean_sarray_cptr(msg),
                                     lean_sarray_size(msg), lean_sarray_cptr(pk)) == 0;
}

/* ------------------------------------------------------------------- X25519 */

/*
`crypto_box_seed_keypair`: the public key followed by the secret key, 64 bytes
in all.
*/
RESOURCES_API lean_obj_res resources_sodium_box_seed_keypair(b_lean_obj_arg seed) {
  if (lean_sarray_size(seed) != crypto_box_SEEDBYTES) {
    return resources_no_bytes();
  }
  uint8_t pk[crypto_box_PUBLICKEYBYTES];
  uint8_t sk[crypto_box_SECRETKEYBYTES];
  if (crypto_box_seed_keypair(pk, sk, lean_sarray_cptr(seed)) != 0) {
    sodium_memzero(sk, sizeof sk);
    return resources_no_bytes();
  }
  lean_object *out = lean_alloc_sarray(1, sizeof pk + sizeof sk, sizeof pk + sizeof sk);
  memcpy(lean_sarray_cptr(out), pk, sizeof pk);
  memcpy(lean_sarray_cptr(out) + sizeof pk, sk, sizeof sk);
  sodium_memzero(sk, sizeof sk);
  return out;
}

/*
`crypto_box_seal`: `msg` sealed to an X25519 public key, `crypto_box_SEALBYTES`
longer than it went in. The sender is an ephemeral key pair libsodium makes and
throws away, so the box says nothing about who sealed it.
*/
RESOURCES_API lean_obj_res resources_sodium_box_seal(b_lean_obj_arg pk, b_lean_obj_arg msg) {
  if (lean_sarray_size(pk) != crypto_box_PUBLICKEYBYTES) {
    return resources_no_bytes();
  }
  size_t mlen = lean_sarray_size(msg);
  size_t clen = mlen + crypto_box_SEALBYTES;
  lean_object *out = lean_alloc_sarray(1, clen, clen);
  if (crypto_box_seal(lean_sarray_cptr(out), lean_sarray_cptr(msg), mlen, lean_sarray_cptr(pk)) !=
      0) {
    lean_dec_ref(out);
    return resources_no_bytes();
  }
  return out;
}

/*
`crypto_box_seal_open`: what was sealed to this secret key's public key, or
`none`.

The public key is recomputed here with `crypto_scalarmult_base` rather than
carried alongside the secret key, because `crypto_box_seal_open` needs both and
a public key handed in beside a secret key is one more thing that can disagree
with it.
*/
RESOURCES_API lean_obj_res resources_sodium_box_seal_open(b_lean_obj_arg sk, b_lean_obj_arg ct) {
  size_t clen = lean_sarray_size(ct);
  if (lean_sarray_size(sk) != crypto_box_SECRETKEYBYTES || clen < crypto_box_SEALBYTES) {
    return resources_none();
  }
  uint8_t pk[crypto_box_PUBLICKEYBYTES];
  if (crypto_scalarmult_base(pk, lean_sarray_cptr(sk)) != 0) {
    return resources_none();
  }
  size_t mlen = clen - crypto_box_SEALBYTES;
  lean_object *out = lean_alloc_sarray(1, mlen, mlen);
  if (crypto_box_seal_open(lean_sarray_cptr(out), lean_sarray_cptr(ct), clen, pk,
                           lean_sarray_cptr(sk)) != 0) {
    lean_dec_ref(out);
    return resources_none();
  }
  return resources_some(out);
}

/* -------------------------------------------------- XChaCha20-Poly1305 IETF */

/*
`crypto_aead_xchacha20poly1305_ietf_encrypt`: `msg` under a 32-byte key and a
24-byte nonce, authenticating `ad` as well, with the 16-byte tag appended.

The nonce is the caller's to choose and must not be used twice under one key.
Every caller in this repository takes it from `randomBytes`, which at 24 bytes
is the reason this is the XChaCha variant.
*/
RESOURCES_API lean_obj_res resources_sodium_aead_encrypt(b_lean_obj_arg key, b_lean_obj_arg nonce,
                                                         b_lean_obj_arg ad, b_lean_obj_arg msg) {
  if (lean_sarray_size(key) != crypto_aead_xchacha20poly1305_ietf_KEYBYTES ||
      lean_sarray_size(nonce) != crypto_aead_xchacha20poly1305_ietf_NPUBBYTES) {
    return resources_no_bytes();
  }
  size_t mlen = lean_sarray_size(msg);
  size_t clen = mlen + crypto_aead_xchacha20poly1305_ietf_ABYTES;
  lean_object *out = lean_alloc_sarray(1, clen, clen);
  unsigned long long written = 0;
  if (crypto_aead_xchacha20poly1305_ietf_encrypt(
          lean_sarray_cptr(out), &written, lean_sarray_cptr(msg), mlen, lean_sarray_cptr(ad),
          lean_sarray_size(ad), NULL, lean_sarray_cptr(nonce), lean_sarray_cptr(key)) != 0 ||
      written != clen) {
    lean_dec_ref(out);
    return resources_no_bytes();
  }
  return out;
}

/*
`crypto_aead_xchacha20poly1305_ietf_decrypt`: the plaintext, or `none` if the
key, the nonce, the associated data or any byte of the ciphertext is not what
was sealed.
*/
RESOURCES_API lean_obj_res resources_sodium_aead_decrypt(b_lean_obj_arg key, b_lean_obj_arg nonce,
                                                         b_lean_obj_arg ad, b_lean_obj_arg ct) {
  size_t clen = lean_sarray_size(ct);
  if (lean_sarray_size(key) != crypto_aead_xchacha20poly1305_ietf_KEYBYTES ||
      lean_sarray_size(nonce) != crypto_aead_xchacha20poly1305_ietf_NPUBBYTES ||
      clen < crypto_aead_xchacha20poly1305_ietf_ABYTES) {
    return resources_none();
  }
  size_t mlen = clen - crypto_aead_xchacha20poly1305_ietf_ABYTES;
  lean_object *out = lean_alloc_sarray(1, mlen, mlen);
  unsigned long long written = 0;
  if (crypto_aead_xchacha20poly1305_ietf_decrypt(
          lean_sarray_cptr(out), &written, NULL, lean_sarray_cptr(ct), clen, lean_sarray_cptr(ad),
          lean_sarray_size(ad), lean_sarray_cptr(nonce), lean_sarray_cptr(key)) != 0 ||
      written != mlen) {
    lean_dec_ref(out);
    return resources_none();
  }
  return resources_some(out);
}

/* ----------------------------------------------------------------- Argon2id */

/*
`crypto_pwhash` with `crypto_pwhash_ALG_ARGON2ID13`: `outlen` bytes from a
passphrase and a salt, at the stated cost.

Which algorithm is not a parameter: this shim computes Argon2id and nothing
else, and the Lean side refuses to call it for a file that names another
stretcher. The failing cases -- a salt of the wrong length, a cost below what
libsodium accepts, or memory it could not get -- all come back as no bytes at
all, which is a key that opens nothing.
*/
RESOURCES_API lean_obj_res resources_sodium_pwhash(b_lean_obj_arg passphrase, b_lean_obj_arg salt,
                                                   size_t outlen, size_t ops, size_t mem) {
  if (lean_sarray_size(salt) != crypto_pwhash_SALTBYTES || outlen < crypto_pwhash_BYTES_MIN ||
      ops < crypto_pwhash_OPSLIMIT_MIN || ops > crypto_pwhash_OPSLIMIT_MAX ||
      mem < crypto_pwhash_MEMLIMIT_MIN || mem > crypto_pwhash_MEMLIMIT_MAX) {
    return resources_no_bytes();
  }
  /* A Lean string is stored UTF-8 encoded with a terminating null it does not count. */
  size_t passlen = lean_string_size(passphrase) - 1;
  lean_object *out = lean_alloc_sarray(1, outlen, outlen);
  if (crypto_pwhash(lean_sarray_cptr(out), (unsigned long long) outlen,
                    lean_string_cstr(passphrase), (unsigned long long) passlen,
                    lean_sarray_cptr(salt), (unsigned long long) ops, mem,
                    crypto_pwhash_ALG_ARGON2ID13) != 0) {
    lean_dec_ref(out);
    return resources_no_bytes();
  }
  return out;
}
