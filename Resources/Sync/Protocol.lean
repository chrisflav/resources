import Lean.Data.Json
import Resources.Crypto.Sha256

/-!
# Sequencer protocol

The shapes the sequencer and its clients exchange, and every byte string a key
ever signs. Nothing here touches storage or sockets, so the canonical encodings
can be read in one sitting and tested on their own.

The sequencer only ever sees ciphertext. A *part* is one realm's slice of an
envelope, encrypted under that realm's key at a stated generation; the server
can order parts, count them and refuse them, and can read none of them.

## Canonical encoding

Everything hashed or signed is built from one primitive, so that no two
different field vectors can produce the same bytes:

```
seg(bs) = ASCII decimal of bs.size, then ":", then bs
```

A number is segmented as its ASCII decimal digits, a string as its UTF-8. Every
canonical string starts with a segmented domain tag, so bytes signed for one
purpose can never be replayed as bytes signed for another.

## What version 2 changed, and why

Version 1 signed and hashed a part's *ciphertext*. A fetch hands back only the
parts the caller holds a grant for, so a filtered reader was shown neither the
bytes the signature covered nor the bytes the hash digested: they could check
nothing, and the protocol had a state called "unverifiable" that the sequencer's
word was the only thing standing behind.

Version 2 signs and hashes each part's `cipherHash` — the hex SHA-256 of the
ciphertext — instead. That digest is the same for every reader, so:

* the signature over an envelope can be checked by anybody who receives it,
  filtered or not;
* `hash(envelope)` is one value rather than one per audience, and a reader
  recomputes it rather than being told it;
* a reader who *does* receive a part checks its bytes against `cipherHash`, so
  nothing between the author and them can change a payload undetected.

The signed bytes also name the author now, so authorship no longer rests on the
route layer's check alone.

* what an envelope's signature covers:
  `seg("resources/seq/v2/envelope-sig") ++ seg(ledger) ++ seg(seq) ++ seg(prevHash)
   ++ seg(author) ++ seg(|parts|) ++ for each part seg(realm) ++ seg(generation)
   ++ seg(cipherHash)`
* what `hash(envelope)` digests:
  the same, under the tag `"resources/seq/v2/envelope"`, then `seg(signature)`
* what a key signs to answer a challenge:
  `seg("resources/seq/v2/challenge") ++ seg(origin) ++ seg(nonce)`
* what an invite's holder signs to join a realm:
  `seg("resources/join/v1") ++ seg(ledger) ++ seg(realm) ++ seg(member)`
* what a grant's issuer signs:
  `seg("resources/grant/v1") ++ seg(ledger) ++ seg(realm) ++ seg(generation)
   ++ seg(member) ++ seg(role) ++ seg(wrappedKey)`
* what a member signs to publish their agreement key:
  `seg("resources/member/v1") ++ seg(ledger) ++ seg(member) ++ seg(keyGeneration)
   ++ seg(boxPk)`
* what a checkpoint's signature covers:
  `seg("resources/seq/v2/checkpoint") ++ seg(ledger) ++ seg(realm) ++ seg(generation)
   ++ seg(seq) ++ seg(stateHash) ++ seg(headHash) ++ seg(snapshotHash)`

`hash(envelope)` is the lowercase hex of the SHA-256 of those bytes. It covers
the author and the signature as well as the signed fields: the chain is meant to
fix who said what, and a hash that ignored the author would let a second member
re-sign the same payload and land on the same link.

The grant's wrapped key is segmented as its *raw bytes*, not as the base64 that
carries it, because base64 is not canonical here — `ofBase64?` accepts padding
and whitespace that the bytes do not record — and a signature over a
non-canonical encoding is a signature two parties can disagree about.
-/

open Lean

namespace Resources
namespace Sync

/-! ## Byte encodings -/

/-- The standard base64 alphabet. -/
private def b64Alphabet : Array Char :=
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/".toList.toArray

/-- Standard base64 with `=` padding: how ciphertext and wrapped keys travel. -/
def toBase64 (bs : ByteArray) : String := Id.run do
  let mut out := ""
  let full := bs.size / 3
  for k in [0:full] do
    let i := 3 * k
    let v := (bs[i]!.toNat <<< 16) ||| (bs[i + 1]!.toNat <<< 8) ||| bs[i + 2]!.toNat
    out := out.push b64Alphabet[(v >>> 18) &&& 63]!
      |>.push b64Alphabet[(v >>> 12) &&& 63]!
      |>.push b64Alphabet[(v >>> 6) &&& 63]!
      |>.push b64Alphabet[v &&& 63]!
  match bs.size % 3 with
  | 1 =>
    let v := bs[3 * full]!.toNat <<< 16
    out := out.push b64Alphabet[(v >>> 18) &&& 63]!
      |>.push b64Alphabet[(v >>> 12) &&& 63]! |>.push '=' |>.push '='
  | 2 =>
    let v := (bs[3 * full]!.toNat <<< 16) ||| (bs[3 * full + 1]!.toNat <<< 8)
    out := out.push b64Alphabet[(v >>> 18) &&& 63]!
      |>.push b64Alphabet[(v >>> 12) &&& 63]!
      |>.push b64Alphabet[(v >>> 6) &&& 63]! |>.push '='
  | _ => pure ()
  return out

/-- The six bits a base64 character stands for. -/
private def b64Value (c : Char) : Option Nat :=
  let n := c.toNat
  if n ≥ 65 && n ≤ 90 then some (n - 65)
  else if n ≥ 97 && n ≤ 122 then some (n - 97 + 26)
  else if n ≥ 48 && n ≤ 57 then some (n - 48 + 52)
  else if c == '+' then some 62
  else if c == '/' then some 63
  else none

/-- Decodes base64, ignoring padding and whitespace. `none` if a character is not base64. -/
def ofBase64? (s : String) : Option ByteArray := Id.run do
  let mut acc : Nat := 0
  let mut bits : Nat := 0
  let mut out := ByteArray.empty
  for c in s.toList do
    if c == '=' || c == '\n' || c == '\r' || c == ' ' || c == '\t' then
      continue
    let some v := b64Value c | return none
    acc := ((acc <<< 6) ||| v) &&& 0xffffff
    bits := bits + 6
    if bits ≥ 8 then
      bits := bits - 8
      out := out.push (((acc >>> bits) &&& 0xff).toUInt8)
  return some out

/-- The nibble a hex digit stands for. -/
private def hexValue (c : Char) : Option Nat :=
  let n := c.toNat
  if n ≥ 48 && n ≤ 57 then some (n - 48)
  else if n ≥ 97 && n ≤ 102 then some (n - 97 + 10)
  else if n ≥ 65 && n ≤ 70 then some (n - 65 + 10)
  else none

/-- Decodes hex in either case. `none` unless the string is an even run of hex digits. -/
def ofHex? (s : String) : Option ByteArray := Id.run do
  let cs := s.toList.toArray
  if cs.size % 2 != 0 then return none
  let mut out := ByteArray.empty
  for k in [0:cs.size / 2] do
    let some hi := hexValue cs[2 * k]! | return none
    let some lo := hexValue cs[2 * k + 1]! | return none
    out := out.push (((hi <<< 4) ||| lo).toUInt8)
  return some out

/--
Whether a string is exactly `n` lowercase hex digits.

Every key in this protocol is a fixed-width byte string rendered one way, and
the sequencer refuses the other renderings rather than storing them: `AB…` and
`ab…` would otherwise be two members backed by one key pair, and a member id is
the one string the whole service indexes by.
-/
def isLowerHex (s : String) (n : Nat) : Bool :=
  s.length == n && s.all fun c =>
    (c ≥ '0' && c ≤ '9') || (c ≥ 'a' && c ≤ 'f')

/-- The width of a signing key, an agreement key and a member id, in hex digits. -/
def keyHexWidth : Nat := 64

/-- Whether a string is a well-formed member id: 64 lowercase hex digits. -/
def isMemberId (s : String) : Bool := isLowerHex s keyHexWidth

/-- The longest a ledger id or a realm id may be. -/
def idMaxLength : Nat := 64

/--
Whether a string is a well-formed ledger or realm id.

A member id is a key and needs no rules beyond its own shape, but a ledger and a
realm are *named*, by whoever makes them, and until now the name was any
non-empty string up to the body cap: 64 kilobytes of anything at all, stored,
served to every member, and carried through an invite link. So the character set
is closed to what a name can be written in without becoming something else
somewhere down the line — `[A-Za-z0-9._-]`, at most `idMaxLength` of them.

That rules out, in one stroke, three of the places an id had to be re-escaped:
a `:` (which is what an invite fragment delimits its fields with), a `%` (which
is the wildcard in a `LIKE` pattern), and a `,` (a delimiter clients once used
in a stored list). A display name that wants a space or an accent belongs in
the ciphertext, where the server has no business reading it.

`_` is deliberately still allowed, because it is what people write names with,
and it is `LIKE`'s *other* wildcard: a client that builds a pattern out of a
realm id has to escape it or stop using `LIKE`. Nothing here does; the note is
for whoever reads this next.
-/
def isPlainId (s : String) : Bool :=
  !s.isEmpty && s.length ≤ idMaxLength && s.all fun c =>
    c.isAlphanum || c == '.' || c == '_' || c == '-'

/-! ## Text that is written down

The audit trail is a line-oriented file, and every field in it — a path, a
member id, an outcome — arrives from whoever made the request. Version 2 wrote
them through verbatim, so a `%0A` in a path segment was a newline by the time it
reached the file and an attacker could forge a whole entry, timestamp and all,
in the one forensic record this service keeps.

So nothing reaches the file unescaped. `logField` percent-encodes everything
that is not a printable, non-space US-ASCII character, and `logLine` is the last
guard on the assembled line. `hasControl` is the other half: a request whose
path carries a control character is refused outright, before it is routed, since
nothing this protocol names can contain one.
-/

/-- Whether a character is a C0 or C1 control: what neither a path nor a log line may carry. -/
def isControl (c : Char) : Bool :=
  c.toNat < 0x20 || (c.toNat ≥ 0x7f && c.toNat ≤ 0x9f)

/-- Whether a string carries a control character anywhere. -/
def hasControl (s : String) : Bool := s.any isControl

/-- The lowercase hex digits, for percent-encoding. -/
private def hexDigits : Array Char := "0123456789abcdef".toList.toArray

/-- One byte as `%xx`, lowercase. -/
private def percentByte (b : UInt8) : String :=
  let n := b.toNat
  ("%".push hexDigits[n / 16]!).push hexDigits[n % 16]!

/--
One field of an audit line: printable US-ASCII, percent-encoded, and bounded.

Space is encoded as well as the control characters, because a space is what
separates one field of a line from the next, and `%` because an encoded byte
has to be told apart from a literal one. Anything longer than `maxBytes` is cut
and marked, so that a kilobyte of path cannot be a kilobyte of log.
-/
def logField (s : String) (maxBytes : Nat := 256) : String := Id.run do
  let bs := s.toUTF8
  let n := min bs.size maxBytes
  let mut out := ""
  for i in [0:n] do
    let b := bs[i]!
    if b > 0x20 && b < 0x7f && b != 0x25 then out := out.push (Char.ofNat b.toNat)
    else out := out ++ percentByte b
  if bs.size > maxBytes then out := out ++ "[cut]"
  return out

/--
The last guard on a whole audit line: no control character survives it.

The fields are escaped where they are assembled, one by one; this catches
anything that reached the line another way. Spaces are left alone here, because
by this point they are the line's own separators.
-/
def logLine (s : String) : String := Id.run do
  let bs := s.toUTF8
  let mut out := ""
  for i in [0:bs.size] do
    let b := bs[i]!
    if b == 0x20 || (b > 0x20 && b < 0x7f) then out := out.push (Char.ofNat b.toNat)
    else out := out ++ percentByte b
  return out

/-! ## Roles

The two roles a grant may carry, which are the two the ledger's own `State` has.
The sequencer enforces them, so the list is closed: a grant in a role this
binary has never heard of buys nothing at all, rather than quietly buying
everything, which is what a carried-but-unenforced field amounts to.
-/

/-- Every role a grant may be issued in. -/
def roles : List String := ["viewer", "admin"]

/-- Whether a string names a role this sequencer knows. -/
def isRole (s : String) : Bool := roles.contains s

/--
Whether a grant in this role may add to the order and commit to a realm's state.

Both known roles may. A viewer is somebody who can read a realm and write in it
— that is what having the key *is* — and the distinction the sequencer draws is
not "who may write" but "who may let somebody else in", which is the realm's
admin field and is asked separately.
-/
def mayWrite (role : String) : Bool := isRole role

/--
Whether a grant in this role administers its realm.

Granting, inviting and revoking are the three things it buys. They are checked
against the realm's `admin` record rather than here, because the realm has
exactly one administrator and a role is a property of a grant; this is the
statement of what the word means, and what a client should expect of it.
-/
def mayAdminister (role : String) : Bool := role == "admin"

/-! ## Timestamps

An invite is the one record here with a lifetime, and the only one where a
client states a time. Version 1 took whatever string arrived and compared it with
`≤` against a *local* naive clock, so `"z"` never lapsed, a UTC stamp from a
browser sorted after every local one, and an offer could be made to last for
ever. So the format is fixed, parsed, range-checked and stored in one canonical
shape — which is also what keeps the lazy sweep's `expires <= now` a correct
comparison, since every row is in the same format.
-/

/-- The ASCII value of a digit, or `none`. -/
private def digit? (c : Char) : Option Nat :=
  if c ≥ '0' && c ≤ '9' then some (c.toNat - 48) else none

/-- Reads exactly `n` digits starting at `i`, as a number. -/
private def digitsAt (cs : Array Char) (i n : Nat) : Option Nat := Id.run do
  if i + n > cs.size then return none
  let mut v := 0
  for k in [0:n] do
    let some d := digit? cs[i + k]! | return none
    v := v * 10 + d
  return some v

/-- Days in a month of a proleptic-Gregorian year. -/
private def daysInMonth (y m : Nat) : Nat :=
  match m with
  | 1 | 3 | 5 | 7 | 8 | 10 | 12 => 31
  | 4 | 6 | 9 | 11 => 30
  | 2 => if (y % 4 == 0 && y % 100 != 0) || y % 400 == 0 then 29 else 28
  | _ => 0

/--
Days from 1970-01-01 to a proleptic-Gregorian date.

Howard Hinnant's `days_from_civil`, with the era shifted so the arithmetic stays
on non-negative numbers for every year this protocol will ever see.
-/
private def daysFromCivil (y m d : Nat) : Int :=
  let y := if m ≤ 2 then y - 1 else y
  let era := y / 400
  let yoe := y - era * 400
  let doy := (153 * (if m > 2 then m - 3 else m + 9) + 2) / 5 + d - 1
  let doe := yoe * 365 + yoe / 4 - yoe / 100 + doy
  Int.ofNat (era * 146097 + doe) - 719468

/--
The proleptic-Gregorian date a day number names: the inverse of `daysFromCivil`.

The same algorithm run backwards. The era shift keeps every intermediate on
non-negative numbers, so none of this depends on which way `Int` division
rounds, which is the one thing calendar arithmetic gets quietly wrong.
-/
def civilFromDays (days : Int) : Nat × Nat × Nat :=
  let z := (days + 719468).toNat
  let era := z / 146097
  let doe := z - era * 146097
  let yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365
  let y := yoe + era * 400
  let doy := doe - (365 * yoe + yoe / 4 - yoe / 100)
  let mp := (5 * doy + 2) / 153
  let d := doy - (153 * mp + 2) / 5 + 1
  let m := if mp < 10 then mp + 3 else mp - 9
  (if m ≤ 2 then y + 1 else y, m, d)

/--
Reads an ISO-8601 instant in UTC, as seconds since the Unix epoch.

`YYYY-MM-DDTHH:MM:SS`, then optionally a fractional part, then optionally `Z`.
A numeric offset is refused rather than converted: this is a wire format, not a
date library, and "the time you meant, in UTC" is the only thing two parties
need to agree on. A naive stamp is read as UTC, which is what it has to be for
the comparison to mean anything at all.
-/
def isoSeconds? (s : String) : Option Int := do
  let cs := s.toList.toArray
  guard (cs.size ≥ 19)
  guard (cs[4]! == '-' && cs[7]! == '-' && cs[10]! == 'T' && cs[13]! == ':' && cs[16]! == ':')
  let year ← digitsAt cs 0 4
  let month ← digitsAt cs 5 2
  let day ← digitsAt cs 8 2
  let hour ← digitsAt cs 11 2
  let minute ← digitsAt cs 14 2
  let second ← digitsAt cs 17 2
  guard (year ≥ 1 && month ≥ 1 && month ≤ 12)
  guard (day ≥ 1 && day ≤ daysInMonth year month)
  guard (hour ≤ 23 && minute ≤ 59 && second ≤ 59)
  -- What may follow: an optional fractional part, then an optional `Z`.
  let afterFraction ←
    match (cs.extract 19 cs.size).toList with
    | '.' :: more =>
      let ds := more.takeWhile (fun c => (digit? c).isSome)
      if ds.isEmpty then none else some (more.drop ds.length)
    | rest => some rest
  guard (afterFraction == [] || afterFraction == ['Z'] || afterFraction == ['z'])
  return (daysFromCivil year month day) * 86400
    + Int.ofNat (hour * 3600 + minute * 60 + second)

/-- Two digits, zero-padded. -/
private def pad2 (n : Nat) : String := if n < 10 then s!"0{n}" else toString n

/-- Four digits, zero-padded. -/
private def pad4 (n : Nat) : String :=
  if n < 10 then s!"000{n}" else if n < 100 then s!"00{n}" else if n < 1000 then s!"0{n}"
  else toString n

/-- Renders a parsed instant back in the one shape this protocol stores. -/
def isoCanonical (year month day hour minute second : Nat) : String :=
  s!"{pad4 year}-{pad2 month}-{pad2 day}T{pad2 hour}:{pad2 minute}:{pad2 second}Z"

/--
Normalises an ISO instant to `YYYY-MM-DDTHH:MM:SSZ`, or `none` if it is not one.

Every stored timestamp goes through here, so that the sweep's string comparison
and a client's chronological reading are the same ordering.
-/
def isoNormalise? (s : String) : Option String := do
  let _ ← isoSeconds? s
  let cs := s.toList.toArray
  let year ← digitsAt cs 0 4
  let month ← digitsAt cs 5 2
  let day ← digitsAt cs 8 2
  let hour ← digitsAt cs 11 2
  let minute ← digitsAt cs 14 2
  let second ← digitsAt cs 17 2
  return isoCanonical year month day hour minute second

/-! ## Canonical byte strings -/

/-- One length-prefixed segment: the byte length in ASCII decimal, a colon, then the bytes. -/
def seg (bs : ByteArray) : ByteArray := (toString bs.size).toUTF8 ++ ":".toUTF8 ++ bs

/-- A string as one segment of its UTF-8. -/
def segStr (s : String) : ByteArray := seg s.toUTF8

/-- A number as one segment of its ASCII decimal digits. -/
def segNat (n : Nat) : ByteArray := segStr (toString n)

/-- The domain tag under which an envelope's signature is taken. -/
def envelopeSigTag : String := "resources/seq/v2/envelope-sig"

/-- The domain tag under which an envelope is hashed. -/
def envelopeHashTag : String := "resources/seq/v2/envelope"

/-- The domain tag under which a checkpoint commitment is signed. -/
def checkpointTag : String := "resources/seq/v2/checkpoint"

/-- The domain tag under which an authentication challenge is signed. -/
def challengeTag : String := "resources/seq/v2/challenge"

/-- The domain tag under which an invite's holder proves a join. -/
def joinTag : String := "resources/join/v1"

/-- The domain tag under which a grant is signed by whoever issued it. -/
def grantTag : String := "resources/grant/v1"

/-- The domain tag under which a member publishes their own agreement key. -/
def memberTag : String := "resources/member/v1"

/--
The bytes a key signs to answer a challenge.

The origin is in them because a signature that named no sequencer was valid at
every sequencer: anybody who could lure a member to a second instance — and an
invite link is a URL, so luring is easy — could relay a challenge from the real
one and open a session as them. A client checks that the origin it is about to
sign is the one it meant to talk to.

It is the second argument, and defaults to empty, because it is configuration
rather than protocol: a sequencer that has not been told its own public name
(one embedded in a test, or reached only over a loopback socket) binds nothing,
and both ends then agree on nothing, which is the same agreement.
-/
def challengeBytes (nonce : String) (origin : String := "") : ByteArray :=
  segStr challengeTag ++ segStr origin ++ segStr nonce

/--
The bytes an invite's signing key signs so that its holder may join a realm.

The joiner's own id is inside them, so a proof overheard on its way to the
server is worth nothing to anybody else: it only ever admits the one member it
names, to the one realm of the one ledger it names.
-/
def joinBytes (ledger realm member : String) : ByteArray :=
  segStr joinTag ++ segStr ledger ++ segStr realm ++ segStr member

/--
The bytes whoever issues a grant signs.

A grant says "this realm key, at this generation, wrapped for this member, in
this role". Every one of those is in here, so a grant cannot be lifted onto
another realm, another member, another role or an older generation, and a
sequencer that substituted a wrapped key of its own would be signing for
somebody whose key it does not hold.
-/
def grantBytes (ledger realm : String) (generation : Nat) (member role : String)
    (wrappedKey : ByteArray) : ByteArray :=
  segStr grantTag ++ segStr ledger ++ segStr realm ++ segNat generation ++ segStr member
    ++ segStr role ++ seg wrappedKey

/-! ### What a client has to change to rotate an agreement key

The generation is a wire change, and it is a small one, but it is in signed
bytes and so both ends have to make it together. For the two clients in this
repository:

* **The node** (`Resources/Node/Session.lean`). `publishBoxPk` sends
  `{"boxPk", "boxPkSignature"}` and signs `memberBytes ledger member boxPk`,
  which is generation 0 — correct for a first key, and refused by the sequencer
  for a second one. To rotate, it reads `keyGeneration` off the member record it
  already fetches, signs `memberBytes ledger member boxPk (g+1)` and sends
  `keyGeneration` beside the signature. `memberBoxPk?` has the mirror problem:
  it checks the signature against generation 0, so it must take the record's
  `keyGeneration` and, where it holds more than one attestation for a member,
  prefer the highest it has seen rather than the one the server served last.
* **The browser** (`web-thin/src/crypto.ts`, `sequencer.ts`, `App.tsx`).
  `memberBytes(ledger, member, boxPk)` gains a fourth argument and emits
  `seg(keyGeneration)` between the member and the key, exactly as here;
  `publishBoxPk` sends `keyGeneration`; the `Member` row gains it; and
  `verifySigned` is called with the generation from the row.

Until both are changed, every client keeps working: absent means zero, and zero
is what every key published so far was signed under.
-/

/--
The bytes a member signs to publish the agreement key realm keys are sealed to.

This is the fix for the one hole that made the whole encryption story a
formality: the agreement key used to be whatever the server said it was, so an
operator — or any ledger admin — could substitute a key they held and be
re-granted every realm on the next rotation. Now the key is only ever a claim
its own signing key made, and the signing key *is* the member id.

`keyGeneration` is what makes the claim replaceable. Without it a member who
published a second key — because the secret half of the first had leaked — left
the first `(boxPk, signature)` pair a perfectly valid self-attestation for ever,
and an untrusted sequencer could go on serving it: the next rotation would seal
the realm key to the compromised one, and the member had no way to say "not that
one". With it, an attestation carries a number that only goes up, the sequencer
refuses a lower one, and a client prefers the highest it has seen.

It defaults to zero, which is the number a member's first key carries, so a
client that has not been taught to rotate yet signs exactly what it signed
before under a zero it never has to mention.
-/
def memberBytes (ledger member boxPk : String) (keyGeneration : Nat := 0) : ByteArray :=
  segStr memberTag ++ segStr ledger ++ segStr member ++ segNat keyGeneration ++ segStr boxPk

/-! ## Wire shapes -/

/--
One realm's slice of an envelope: ciphertext under that realm's key, at the
generation of the key it was encrypted with.

`cipherHash` is what the signature and the envelope hash are taken over, so it
travels whether or not the ciphertext does. A part whose `ciphertext` the
sequencer stripped — because the caller holds no grant on its realm — carries
an empty one and `visible := false`.
-/
structure Part where
  /-- Which realm the ciphertext belongs to. -/
  realm : String
  /-- Which generation of the realm key it is encrypted under. -/
  generation : Nat
  /-- The ciphertext itself; base64 on the wire, bytes here. Empty when stripped. -/
  ciphertext : ByteArray
  /-- The hex SHA-256 of the ciphertext as its author sealed it. Always present. -/
  cipherHash : String := Sha256.hexBytes ciphertext
  /-- Whether `ciphertext` is the payload rather than a placeholder for one withheld. -/
  visible : Bool := true
  deriving Inhabited

/-- Whether a part's bytes really are the bytes its digest names. -/
def Part.intact (p : Part) : Bool :=
  p.visible && p.cipherHash == Sha256.hexBytes p.ciphertext

/-- The same part with its payload withheld: the digest stays, the bytes go. -/
def Part.stripped (p : Part) : Part :=
  { p with ciphertext := ByteArray.empty, visible := false }

/--
One entry in a ledger's total order.

`seq` and `prevHash` are the client's claim about where the entry belongs; the
sequencer accepts it only if that claim still matches the head.
-/
structure Envelope where
  /-- The ledger this entry belongs to. -/
  ledger : String
  /-- Position in the total order, starting at 1. -/
  seq : Nat
  /-- `hash` of the entry before it; empty for the first entry in a ledger. -/
  prevHash : String
  /-- The author's public key, hex. -/
  author : String
  /-- The encrypted slices, one per realm the entry touches. -/
  parts : List Part
  /-- Signature over `signingBytes`, hex. -/
  signature : String
  /--
  The digest the sequencer stored when it accepted this entry, or empty for one
  that has not been appended yet.

  It is served from the column rather than recomputed on the way out, so that
  what a client chains onto is the value the compare-and-swap is actually taken
  against. `hash` is what it must equal, and every reader checks that it does.
  -/
  storedHash : String := ""
  deriving Inhabited

/-- Where a ledger's chain has got to. `seq = 0` with an empty hash is an empty ledger. -/
structure Head where
  /-- The sequence number of the last entry, or 0. -/
  seq : Nat := 0
  /-- `hash` of the last entry, or the empty string. -/
  hash : String := ""
  deriving Inhabited, BEq

/--
A member of a ledger, by public key.

Two keys, because the two things a member does with cryptography are different
things: `key` is the Ed25519 key they sign envelopes with, and the member id is
its lowercase hex; `boxPk` is the X25519 key realm keys are sealed to.

`boxPk` is only ever published by its owner, and `boxPkSignature` is the proof:
a signature by `key` over `memberBytes`. An admin who adds a member leaves the
agreement key empty, and the member fills it in themselves.

`keyGeneration` is how an agreement key is replaced: it is inside the signed
bytes, the sequencer refuses a publication that does not move it forward, and a
client that holds two attestations takes the one with the higher number. A
member who has published nothing sits at generation 0 with an empty key.
-/
structure Member where
  /-- The member's Ed25519 signing key, hex. This is also their id. -/
  key : String
  /-- The member's X25519 agreement key, hex; empty for a member who published none. -/
  boxPk : String := ""
  /-- The member's own signature over `memberBytes`, hex; empty when `boxPk` is. -/
  boxPkSignature : String := ""
  /-- Which agreement key of this member's this is: 0 for their first. -/
  keyGeneration : Nat := 0
  /-- Whether they may add and remove members. -/
  admin : Bool
  /-- When they were added. -/
  addedAt : String
  deriving Inhabited

/-- A realm: one key's worth of a ledger, and the generation that key is on. -/
structure Realm where
  /-- The realm's name, unique within its ledger. -/
  name : String
  /-- The current key generation; a revoke bumps it. -/
  generation : Nat
  /-- The member who may grant and revoke on it. -/
  admin : String
  deriving Inhabited

/--
One member's access to one realm: the realm key, wrapped to their public key,
and the signature of whoever said so.

`grantedBy` is a realm admin, or the member themselves when the grant came out
of an invite they redeemed. A client accepts a grant for its own use only from a
signer it has a reason to trust — itself, the inviter pinned from the link it
joined by, or a realm admin its own replayed state records.
-/
structure Grant where
  /-- The realm granted. -/
  realm : String
  /-- Who holds the grant, by public key. -/
  member : String
  /-- Which generation of the realm key is wrapped here. -/
  generation : Nat
  /-- The wrapped key; opaque to the sequencer. -/
  wrappedKey : ByteArray
  /-- What the holder is meant to do with it. -/
  role : String := "viewer"
  /-- Who issued it, by member id. -/
  grantedBy : String := ""
  /-- `grantedBy`'s signature over `grantBytes`, hex. -/
  signature : String := ""
  deriving Inhabited

/--
A pending grant: a realm key wrapped to an ephemeral public key, redeemable once
by whoever holds that key's secret half.

The invite is the only record here that is not about somebody the ledger already
knows. `signPk` names the Ed25519 key a joiner must prove they can sign with
(`joinBytes`), `boxPk` names the X25519 key the wrapped key was sealed to, and
the generation is the one the realm was on when the invite was made — a revoke
between then and the join makes the wrapped key useless, so the join is refused
rather than recorded.

`createdBy` is the inviter's member id, which is also their signing key: it is
what a joiner pins as the one admin of the realm they have any reason to trust
before they have replayed anything.
-/
structure Invite where
  /-- The realm being offered. -/
  realm : String
  /-- The invite's Ed25519 key, hex; the proof is checked against it. -/
  signPk : String
  /-- The invite's X25519 key, hex; `wrappedKey` is sealed to it. -/
  boxPk : String
  /-- The realm key sealed to `boxPk`; opaque to the sequencer. -/
  wrappedKey : ByteArray
  /-- The generation of the realm key sealed here. -/
  generation : Nat
  /-- The role the joiner's grant will carry. -/
  role : String := "viewer"
  /-- When the offer lapses, as an ISO timestamp. -/
  expires : String
  /-- The realm admin who made it; their member id is their signing key. -/
  createdBy : String
  deriving Inhabited

/--
A signed commitment that a realm's plaintext state, at a point in the order, is
what the author says it is, plus an encrypted snapshot a newcomer can start from.

One is kept per author rather than one per realm: a checkpoint is one member's
claim about what they replayed, and keeping only the newest of them all let any
grant holder erase everybody else's.
-/
structure Checkpoint where
  /-- The ledger committed to. -/
  ledger : String
  /-- The realm committed to. -/
  realm : String
  /-- The key generation the snapshot is encrypted under. -/
  generation : Nat
  /-- The position in the order the commitment speaks about. -/
  seq : Nat
  /-- The client's hash of the realm's plaintext state, opaque here. -/
  stateHash : String
  /-- `hash` of the envelope at `seq`; empty when `seq` is 0. -/
  headHash : String
  /-- Who signed the commitment, by public key. -/
  author : String
  /-- Signature over `commitmentBytes`, hex. -/
  signature : String
  /-- The encrypted snapshot; base64 on the wire. -/
  snapshot : ByteArray
  deriving Inhabited

/-- The digest of the encrypted snapshot, which the commitment covers. -/
def Checkpoint.snapshotHash (c : Checkpoint) : String := Sha256.hexBytes c.snapshot

/-- The fields both an envelope's signature and its hash are taken over. -/
private def Envelope.core (e : Envelope) (tag : String) : ByteArray :=
  e.parts.foldl
    (fun acc p => acc ++ segStr p.realm ++ segNat p.generation ++ segStr p.cipherHash)
    (segStr tag ++ segStr e.ledger ++ segNat e.seq ++ segStr e.prevHash ++ segStr e.author
      ++ segNat e.parts.length)

/-- The bytes an envelope's signature covers. -/
def Envelope.signingBytes (e : Envelope) : ByteArray := e.core envelopeSigTag

/-- The bytes `hash` digests: the signed fields, plus the signature. -/
def Envelope.hashBytes (e : Envelope) : ByteArray :=
  e.core envelopeHashTag ++ segStr e.signature

/--
`hash(envelope)`: the lowercase hex SHA-256 of `hashBytes`.

It is the same value for every reader, because nothing it digests is ever
withheld from one. A reader recomputes it rather than believing a server that
states it.
-/
def Envelope.hash (e : Envelope) : String := Sha256.hexBytes e.hashBytes

/-- The head this envelope becomes once it is accepted. -/
def Envelope.head (e : Envelope) : Head := { seq := e.seq, hash := e.hash }

/--
The bytes a checkpoint's signature covers: ledger, realm, generation, seq, state
hash, head hash, snapshot hash.

The head hash is what ties the commitment to the order it speaks about. Without
it a snapshot says only "the state was this at entry 3", which a reader starting
from it has no way to join onto the chain: the first envelope after a checkpoint
carries a `prevHash`, and this is the value it has to match.

The snapshot hash is what ties it to the bytes it ships with. Without it the
binding rested entirely on a reader decrypting the snapshot and recomputing
`stateHash` from it, which nothing forced them to do — so a server could swap
the snapshot and keep the signature valid.
-/
def Checkpoint.commitmentBytes (c : Checkpoint) : ByteArray :=
  segStr checkpointTag ++ segStr c.ledger ++ segStr c.realm ++ segNat c.generation
    ++ segNat c.seq ++ segStr c.stateHash ++ segStr c.headHash ++ segStr c.snapshotHash

/-! ## JSON -/

/-- A `Nat` as JSON. -/
def jnat (n : Nat) : Json := Json.num (JsonNumber.fromInt (Int.ofNat n))

/-- Reads a string field, naming it if it is missing or of the wrong type. -/
def strField (j : Json) (key : String) : Except String String :=
  match j.getObjValAs? String key with
  | .ok s => .ok s
  | .error _ => .error s!"'{key}' must be a string"

/-- Reads a string field, defaulting when it is absent. -/
def strField? (j : Json) (key : String) (dflt : String := "") : String :=
  (j.getObjValAs? String key).toOption.getD dflt

/-- Reads a natural-number field. -/
def natField (j : Json) (key : String) : Except String Nat :=
  match j.getObjValAs? Nat key with
  | .ok n => .ok n
  | .error _ => .error s!"'{key}' must be a non-negative integer"

/-- Reads a base64 field as bytes. -/
def bytesField (j : Json) (key : String) : Except String ByteArray := do
  let s ← strField j key
  match ofBase64? s with
  | some bs => .ok bs
  | none => .error s!"'{key}' must be base64"

/-- A part: its digest always, its ciphertext only when the reader may have it. -/
def Part.toJson (p : Part) : Json :=
  Json.mkObj ([("realm", Json.str p.realm), ("generation", jnat p.generation),
               ("cipherHash", Json.str p.cipherHash)]
    ++ (if p.visible then [("ciphertext", Json.str (toBase64 p.ciphertext))] else []))

/--
Reads a part.

`cipherHash` is required, because it is what the signature covers; `ciphertext`
is optional, because a fetch strips it from the realms the caller holds no grant
on. Whether it was there is remembered rather than guessed at from an empty
byte string.
-/
def Part.ofJson? (j : Json) : Except String Part := do
  let realm ← strField j "realm"
  let generation ← natField j "generation"
  let cipherHash ← strField j "cipherHash"
  match j.getObjVal? "ciphertext" with
  | .error _ => return { realm, generation, ciphertext := ByteArray.empty, cipherHash,
                         visible := false }
  | .ok _ =>
    return { realm, generation, ciphertext := ← bytesField j "ciphertext", cipherHash,
             visible := true }

/-- The hash to serve: the stored one when there is one, the recomputed one otherwise. -/
private def Envelope.statedHash (e : Envelope) : String :=
  if e.storedHash.isEmpty then e.hash else e.storedHash

/-- An envelope, carrying whichever parts the caller is allowed to see. -/
def Envelope.toJson (e : Envelope) : Json :=
  Json.mkObj [("ledger", e.ledger), ("seq", jnat e.seq), ("prevHash", e.prevHash),
              ("author", e.author), ("parts", Json.arr ((e.parts.map Part.toJson).toArray)),
              ("signature", e.signature), ("hash", e.statedHash)]

/-- Reads an envelope. The `hash` field, if present, is kept but never trusted. -/
def Envelope.ofJson? (j : Json) : Except String Envelope := do
  let partsJson ←
    match j.getObjVal? "parts" with
    | .ok v => v.getArr?
    | .error _ => .error "'parts' must be an array"
  let parts ← partsJson.toList.mapM Part.ofJson?
  return { ledger := ← strField j "ledger", seq := ← natField j "seq",
           prevHash := strField? j "prevHash", author := ← strField j "author",
           parts, signature := ← strField j "signature",
           storedHash := strField? j "hash" }

/--
An envelope carrying only the parts a caller may see.

A fetch hands back the ciphertext of the realms the caller holds a grant for and
withholds the rest — but every part's realm, generation and `cipherHash` travel
either way, because those are what the signature and the hash are taken over.
So the filtered envelope hashes to exactly what the whole one does, and a reader
who was handed half of it can still check who wrote it and where it sits in the
chain.
-/
def Envelope.filterJson (e : Envelope) (visible : String → Bool) : Json :=
  { e with parts := e.parts.map fun (p : Part) =>
      if visible p.realm then p else p.stripped }.toJson

/-- A head. -/
def Head.toJson (h : Head) : Json := Json.mkObj [("seq", jnat h.seq), ("hash", h.hash)]

/--
A member, with both of their public keys and the proof of the second.

`member` and `signPk` are the same string: the id *is* the signing key, and
saying so twice costs a field and saves every reader from having to know it.
-/
def Member.toJson (m : Member) : Json :=
  Json.mkObj [("member", m.key), ("signPk", m.key), ("boxPk", m.boxPk),
              ("boxPkSignature", m.boxPkSignature),
              ("keyGeneration", jnat m.keyGeneration),
              ("admin", Json.bool m.admin), ("addedAt", m.addedAt)]

/-- A realm. -/
def Realm.toJson (r : Realm) : Json :=
  Json.mkObj [("realm", r.name), ("generation", jnat r.generation), ("admin", r.admin)]

/-- A grant, with the wrapped key base64-encoded and the issuer's signature beside it. -/
def Grant.toJson (g : Grant) : Json :=
  Json.mkObj [("realm", g.realm), ("member", g.member), ("generation", jnat g.generation),
              ("wrappedKey", Json.str (toBase64 g.wrappedKey)), ("role", g.role),
              ("grantedBy", g.grantedBy), ("signature", g.signature)]

/-- The bytes this grant's issuer signed, in the ledger it belongs to. -/
def Grant.signingBytes (g : Grant) (ledger : String) : ByteArray :=
  grantBytes ledger g.realm g.generation g.member g.role g.wrappedKey

/--
An invite, *without* the wrapped key.

The sealed key is the one part of an invite that is worth stealing, so it leaves
the server down one road only: to somebody who has proved they hold the invite's
signing key, and can therefore unseal it anyway. A listing is not that road — it
says what an invite is for and to whom it was issued, and nothing a bystander
could use.
-/
def Invite.toJson (i : Invite) : Json :=
  Json.mkObj [("realm", i.realm), ("inviteSignPk", i.signPk), ("inviteBoxPk", i.boxPk),
              ("generation", jnat i.generation), ("role", i.role), ("expires", i.expires),
              ("createdBy", i.createdBy), ("inviterSignPk", i.createdBy)]

/--
Reads an invite. The realm, the generation and the issuer come from the request
and the realm's own state, so an invite cannot be filed under another realm or
backdated to a generation its maker no longer holds.
-/
def Invite.ofJson? (j : Json) (realm : String) (generation : Nat) (createdBy : String) :
    Except String Invite := do
  return { realm, generation, createdBy,
           signPk := (← strField j "inviteSignPk").toLower,
           boxPk := (← strField j "inviteBoxPk").toLower,
           wrappedKey := ← bytesField j "wrappedKey",
           role := strField? j "role" "viewer",
           expires := ← strField j "expires" }

/-- A checkpoint, with the snapshot base64-encoded. -/
def Checkpoint.toJson (c : Checkpoint) : Json :=
  Json.mkObj [("ledger", c.ledger), ("realm", c.realm), ("generation", jnat c.generation),
              ("seq", jnat c.seq), ("stateHash", c.stateHash), ("headHash", c.headHash),
              ("snapshotHash", c.snapshotHash), ("author", c.author),
              ("signature", c.signature), ("snapshot", Json.str (toBase64 c.snapshot))]

/--
Reads a checkpoint. The ledger, realm and author come from the request rather
than the body, so a signed commitment cannot be filed under another name.
-/
def Checkpoint.ofJson? (j : Json) (ledger realm author : String) : Except String Checkpoint := do
  return { ledger, realm, author,
           generation := ← natField j "generation", seq := ← natField j "seq",
           stateHash := ← strField j "stateHash", headHash := strField? j "headHash",
           signature := ← strField j "signature", snapshot := ← bytesField j "snapshot" }

/-! ## Signatures -/

/--
How a signature is checked.

The check is a field rather than a call, so that the sequencer is written against
this interface and a signature scheme is one value. That is how it went: the
routes below were finished, and enforcing order, membership, grants and
checkpoints, before anything verified a signature, and binding libsodium
(`Cli.sequencerVerifier`) replaced this one field and nothing else. What is
signed, what is hashed and what is enforced never moved.

`name` is what `GET health` reports, so that an operator — and the client's own
chrome — can see from the outside which of these a deployment is running.
-/
structure Verifier where
  /-- What this verifier is: `sodium`, `insecure` or `reject-all`. -/
  name : String
  /--
  How many hex characters a signature under this scheme has, or 0 for "the
  scheme did not say".

  A verifier that states its width gets an exact check; one that does not gets
  the range every scheme this protocol could carry falls inside. Ed25519 is 128
  (64 bytes) and the test suite is 64 (32 bytes), and the reason the field
  exists rather than the number being written into `check` is that both of those
  have to work, on the same code, today.
  -/
  signatureHexWidth : Nat := 0
  /-- Whether `signature` is a valid signature of `message` under `pubKey`. -/
  verify : (pubKey : ByteArray) → (message : ByteArray) → (signature : ByteArray) → Bool

namespace Verifier

/-- The shortest signature any scheme here could carry, in hex characters. -/
def signatureHexMin : Nat := 64

/-- The longest, in hex characters. -/
def signatureHexMax : Nat := 128

/--
Accepts every signature. **Test-only.**

A sequencer built with this verifier enforces order, membership and grants, and
enforces nothing at all about who signed what. It exists so that a test can
exercise a refusal that has nothing to do with cryptography, and it must never
be the verifier a deployed sequencer is started with.
-/
def acceptAll : Verifier := { name := "accept-all", verify := fun _ _ _ => true }

/-- Rejects every signature; the safe default for a sequencer with no scheme bound. -/
def rejectAll : Verifier := { name := "reject-all", verify := fun _ _ _ => false }

/--
Whether this verifier proves nothing at all about who signed something.

`insecure` recomputes a signature from the *public* key and `accept-all` does
not look, so a sequencer running either of them has no authentication: anybody
can be anybody. It is the question `Sync.Node.make` asks, and the answer decides
whether there is a sequencer at all: one of these is refused unless whoever
builds it says in as many words that it is for a test. The routes no longer ask,
because a thing that cannot be built is not a case they have to handle.
-/
def isInsecure (v : Verifier) : Bool := v.name == "insecure" || v.name == "accept-all"

/-- Whether a hex signature is the right shape to hand to this scheme. -/
def wellFormedSignature (v : Verifier) (sigHex : String) : Bool :=
  if v.signatureHexWidth != 0 then sigHex.length == v.signatureHexWidth
  else sigHex.length % 2 == 0 && sigHex.length ≥ signatureHexMin
    && sigHex.length ≤ signatureHexMax

/--
Checks a hex-encoded key and signature over `message`.

The lengths are checked *before* the scheme is asked. `ofHex?` is happy with any
even run of hex digits, so a one-byte "key" and a three-byte "signature" used to
reach the primitive — harmless while the primitive is Lean, and a buffer
over-read in C the day `crypto_sign_verify_detached` is behind it. Every public
key in this protocol is 32 bytes, which is 64 hex characters and is what a
member id is; a signature is whatever width the verifier declares, or inside the
range every scheme here could use.

Bad hex, or the wrong width, is a failed check rather than an error: a field
that is not a key cannot have signed anything, which is the same answer as a key
that did not sign this.
-/
def check (v : Verifier) (pubKeyHex : String) (message : ByteArray) (sigHex : String) : Bool :=
  if pubKeyHex.length != keyHexWidth || !v.wellFormedSignature sigHex then false
  else
    match ofHex? pubKeyHex, ofHex? sigHex with
    | some key, some sig => v.verify key message sig
    | _, _ => false

end Verifier

end Sync
end Resources
