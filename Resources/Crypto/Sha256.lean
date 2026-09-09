import Resources.Util

/-!
# SHA-256

Nothing in `Std` hashes, and three separate parts of this system need a stable
digest: content-addressed receipts, import fingerprints, and API token storage.
This is a direct transcription of FIPS 180-4, checked against the standard test
vectors at the bottom of the file.
-/

namespace Resources.Sha256

private def roundConstants : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

private def initialState : Array UInt32 :=
  #[0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

@[inline] private def rotr (x : UInt32) (n : UInt32) : UInt32 :=
  (x >>> n) ||| (x <<< (32 - n))

private def compress (st : Array UInt32) (block : ByteArray) (off : Nat) : Array UInt32 := Id.run do
  let mut w : Array UInt32 := Array.replicate 64 0
  for i in [0:16] do
    let b : Nat → UInt32 := fun j => (block[off + 4 * i + j]!).toUInt32
    w := w.set! i ((b 0 <<< 24) ||| (b 1 <<< 16) ||| (b 2 <<< 8) ||| b 3)
  for i in [16:64] do
    let x := w[i - 15]!
    let y := w[i - 2]!
    let s0 := (rotr x 7) ^^^ (rotr x 18) ^^^ (x >>> 3)
    let s1 := (rotr y 17) ^^^ (rotr y 19) ^^^ (y >>> 10)
    w := w.set! i (w[i - 16]! + s0 + w[i - 7]! + s1)
  let mut a := st[0]!; let mut b := st[1]!; let mut c := st[2]!; let mut d := st[3]!
  let mut e := st[4]!; let mut f := st[5]!; let mut g := st[6]!; let mut h := st[7]!
  for i in [0:64] do
    let s1 := (rotr e 6) ^^^ (rotr e 11) ^^^ (rotr e 25)
    let ch := (e &&& f) ^^^ ((~~~e) &&& g)
    let t1 := h + s1 + ch + roundConstants[i]! + w[i]!
    let s0 := (rotr a 2) ^^^ (rotr a 13) ^^^ (rotr a 22)
    let maj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
    let t2 := s0 + maj
    h := g; g := f; f := e; e := d + t1
    d := c; c := b; b := a; a := t1 + t2
  return #[st[0]! + a, st[1]! + b, st[2]! + c, st[3]! + d,
           st[4]! + e, st[5]! + f, st[6]! + g, st[7]! + h]

/-- Appends the FIPS 180-4 padding: a `0x80` byte, zeroes, then the bit length big-endian. -/
private def pad (msg : ByteArray) : ByteArray := Id.run do
  let len := msg.size
  let bitLen : UInt64 := (UInt64.ofNat len) * 8
  let padLen := if len % 64 < 56 then 56 - len % 64 else 120 - len % 64
  let mut out := msg.push 0x80
  for _ in [0 : padLen - 1] do
    out := out.push 0
  for i in [0:8] do
    out := out.push (((bitLen >>> (UInt64.ofNat (56 - 8 * i))) &&& 0xff).toUInt8)
  return out

/-- The SHA-256 digest of `msg`, 32 bytes. -/
def hash (msg : ByteArray) : ByteArray := Id.run do
  let padded := pad msg
  let mut st := initialState
  let blocks := padded.size / 64
  for i in [0:blocks] do
    st := compress st padded (i * 64)
  let mut out := ByteArray.empty
  for word in st do
    for j in [0:4] do
      out := out.push (((word >>> (UInt32.ofNat (24 - 8 * j))) &&& 0xff).toUInt8)
  return out

/-- The SHA-256 digest of a string's UTF-8 encoding, as lowercase hex. -/
def hex (s : String) : String := toHex (hash s.toUTF8)

/-- The SHA-256 digest of a byte array, as lowercase hex. -/
def hexBytes (bs : ByteArray) : String := toHex (hash bs)

/-- Constant-time byte-array comparison, for comparing secrets. -/
def constantTimeEq (a b : ByteArray) : Bool := Id.run do
  if a.size != b.size then return false
  let mut diff : UInt8 := 0
  for i in [0:a.size] do
    diff := diff ||| (a[i]! ^^^ b[i]!)
  return diff == 0

-- FIPS 180-4 / NESSIE test vectors.
example : hex "" = "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855" := by
  native_decide
example : hex "abc" = "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad" := by
  native_decide
example :
    hex "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"
      = "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1" := by
  native_decide

end Resources.Sha256
