import Std.Data.HashMap
import Resources.Api.Routes
import Resources.Sync.Log

/-!
# Sequencer routes

The whole sequencer API, expressed without reference to any HTTP library, over
the same `Api.Req`/`Api.Reply` pair the ledger API uses. `Std.Http` appears only
in `Resources.Sync.Server`.

Everything below `/seq/v2` is here. Two routes are open, because they are how a
caller gets a session at all: `challenge` hands out a nonce for a public key and
`authenticate` takes a signature over it. Every other route needs a bearer token
from `authenticate`, and the key that token is bound to is the caller — there are
no passwords, no accounts and no way to act as somebody whose signature you
cannot produce. Membership is then the gate on everything about a ledger, with
one deliberate exception: accepting an invite — reading its sealed key, then
spending it — is how somebody who holds one becomes a member, so those two routes
are reached before that gate.

## What this file checks that the store cannot

Every signature: the envelope's, the grant's, the member's over their own
agreement key, the checkpoint's commitment, and the invite holder's join proof.
A signature is the one check that does not need the database to be consistent
with itself, so it is taken here and the store is left to do what only it can —
membership, grants, generations, the compare-and-swap on the head and the single
use of an invite, each inside the transaction where it is still true at the
moment of the write.

Also here: the per-route body cap, the caps on what one envelope may carry, the
rate limiters, and the `headHash` of a checkpoint, which is a claim about a
position the head has passed and so is settled by the order the store already
holds.

Every route a session can reach that *writes* takes a token, not the append
alone: membership, realms, grants, invites, checkpoints, joins and blobs are all
writes behind the same lock, and a limit on one of eight doors is not a limit.
Blobs have a bucket of their own, so that a run of receipts does not spend what
an append needs.

And what is *not* checked here any more: whether the verifier proves anything.
A sequencer cannot be built with one that does not (`Node.make`), which is a
stronger statement than any refusal a route could make, and it is why nothing
below asks.

## One request at a time

`handleSafe` takes the store's mutex for the whole of a request and is the only
place that does. The sequencer has one SQLite connection and the server runs
handlers in parallel, so without it `BEGIN IMMEDIATE` is not isolation and the
two things this service exists to guarantee — the compare-and-swap and the
single-use invite — are not atomic. It also makes the in-memory tables below
(sessions, challenges, buckets) safe to read and write without any further care.

What is *not* under it is everything expensive that needs nothing from the
store: the SHA-256 of a sixteen-megabyte blob, the JSON parse of an append of
the same size, and that append's base64 decode and digest per part. Holding the
one global lock through those made the correct fix for unsynchronised transactions
into a way for one member with a burst of tokens to stop the whole service for
seconds at a time. `prepare` does that work first, outside the lock, and hands
the results in — and `maxParts` and `maxPartBytes` bound how much of it one
request can ask for at all.
-/

open Lean

namespace Resources
namespace Sync

/-- Tuning for the parts of the sequencer that live in memory. -/
structure Limits where
  /-- How long a session token stays valid, in milliseconds. -/
  sessionMillis : Int := 3600 * 1000
  /-- How long a challenge nonce stays valid, in milliseconds. -/
  challengeMillis : Int := 120 * 1000
  /--
  How many mutating requests a member may make back to back.

  It was thirty-two and it counted appends alone. It now counts every write a
  session can reach — membership, realms, grants, invites, checkpoints, joins —
  and joining a ledger is half a dozen of them before a single entry is pushed,
  so the number went up with what it covers.
  -/
  burst : Nat := 64
  /-- How many of those per second the bucket refills at. -/
  perSecond : Nat := 8
  /--
  How many blob uploads a member may make back to back.

  Blobs have an allowance of their own, and a larger one: storing a run of
  receipts is a thing people do in a burst, and spending on an attachment what
  an append needs would stall the order for the sake of it. What bounds the
  *bytes* is the quota and the body cap, which this is deliberately not a
  second copy of — it bounds how many, and they are what bound how much.
  -/
  blobBurst : Nat := 128
  /-- How many blob uploads a second that bucket refills at. -/
  blobPerSecond : Nat := 8
  /-- How many challenges or authentications a key may ask for back to back. -/
  authBurst : Nat := 8
  /-- How many of those it gains a second. -/
  authPerSecond : Nat := 1
  /-- How many challenges may be outstanding at once. -/
  maxChallenges : Nat := 10000
  /-- How many allowances of one kind are kept at once. -/
  maxBuckets : Nat := 4096
  /-- How long an allowance may sit untouched before it is dropped, in milliseconds. -/
  bucketIdleMillis : Int := 3600 * 1000
  /-- How many live sessions one key may hold at once. -/
  maxSessionsPerKey : Nat := 8
  /--
  How many bytes of blobs one ledger may hold.

  Nothing collects them: the sequencer cannot read an entry, so it cannot know
  which blobs the order still points at. Removal is therefore a request an
  administrator makes — `DELETE ledgers/{ledger}/blobs/{hash}` — and this
  number is what makes "the ledger is full" a sentence somebody is told rather
  than a disk that fills. A deployment sets it from `--blob-quota`.
  -/
  blobQuotaBytes : Nat := 256 * 1024 * 1024
  /--
  How many parts one envelope may carry.

  Each part costs a base64 decode and a SHA-256, and the body cap alone let one
  megabyte of JSON carry tens of thousands of them. Both are done before the
  store is locked now, but a bound that is stated is worth more than a bound
  that happens to follow from another one.
  -/
  maxParts : Nat := 64
  /--
  How many bytes of ciphertext one part may carry.

  It was 256 KiB, and that number was chosen for an ordinary entry: a payment,
  a receipt line, a label. A genesis is not one. The first entry of a shared
  order is the whole of a store as a single `Op.snapshot`, and for a ledger
  that has been kept for years that is megabytes — so the number that was
  comfortable for every later entry was the number that made the first one
  impossible to push at all, which is the one entry a ledger cannot do without.

  Eight mebibytes is what a years-old ledger's snapshot fits in with room over.
  What bounds it in practice is `maxAppendBytes`, which is 16 MiB of body and so
  12 MiB of base64-decoded parts however they are divided up: this number states
  what *one* part may be, and the body cap states what all of them together may.

  ### Why the work this buys is safe outside the mutex

  Every byte of it is decoded and digested by `prepare`, before the store's lock
  is taken, so none of it delays anybody else's append — it spends CPU and
  memory, not the order. What bounds those is the allowance, and the arithmetic
  is this. One append costs at most `maxAppendBytes` of body to parse, three
  quarters of that to base64-decode, and one SHA-256 over what comes out:
  measured on this machine, 1.7 seconds and 230 MB of memory at a full 16 MiB,
  and a member has to have uploaded all 16 MiB to ask for it.

  A member may spend `burst` writes back to back — 64 — which is 64 × 16 MiB =
  1 GiB of body, and they must send that gigabyte to spend them. The bucket then
  refills at `perSecond`, 8 a second, so the sustained ceiling per member is
  8 × 16 MiB = 128 MiB of body a second: a rate the network in front of this
  service refuses long before the parser does. The burst empties in eight
  seconds of silence and refills in eight.

  And the honest case is one request. A genesis is pushed once, by one member,
  when a ledger is first put on a sequencer; every entry after it is the
  kilobytes it always was.
  -/
  maxPartBytes : Nat := 8 * 1024 * 1024
  /--
  How many bytes of body an append or a checkpoint may carry.

  The two routes that carry a snapshot: `POST ledgers/{l}/events`, whose first
  entry is a whole store, and `PUT ledgers/{l}/realms/{r}/checkpoint`, which is
  that same state sealed under a realm key. They are the same class of object
  and so they are the same number, and a deployment sets it with
  `--max-append`. Every other route keeps the small caps in `bodyLimit`.
  -/
  maxAppendBytes : Nat := 16 * 1024 * 1024
  /-- How many envelopes one fetch may return. -/
  eventLimit : Nat := 500
  /-- The longest an invite may be made to stand, in days. -/
  inviteMaxDays : Nat := 30
  deriving Repr, Inhabited

/--
A size in bytes, as an operator writes one: `268435456`, `256MiB`, `512K`.

`--blob-quota` is the one number in here somebody is likely to want in a unit
rather than in bytes, and a quota typed with a zero missing is a service that
stops taking receipts three months later. The suffixes are the binary ones,
because that is what a disk is measured in, and `KB` means 1024 for the same
reason. A bare number is bytes.
-/
def byteSize? (s : String) : Option Nat := Id.run do
  let t := s.trimAscii.toString.toUpper
  -- Longest suffix first: `KIB` would otherwise be read as `B`.
  let units : List (String × Nat) :=
    [("KIB", 1024), ("MIB", 1024 * 1024), ("GIB", 1024 * 1024 * 1024),
     ("KB", 1024), ("MB", 1024 * 1024), ("GB", 1024 * 1024 * 1024),
     ("K", 1024), ("M", 1024 * 1024), ("G", 1024 * 1024 * 1024),
     ("B", 1), ("", 1)]
  for (suffix, scale) in units do
    if t.endsWith suffix then
      let digits := t.take (t.length - suffix.length)
      if digits.isEmpty || !digits.all Char.isDigit then return none
      return digits.toNat?.map (· * scale)
  return none

/-- A live session: a bearer token bound to the public key that proved itself. -/
structure Session where
  /-- The bearer token handed to the client. -/
  token : String
  /-- The public key it speaks for, hex. -/
  key : String
  /-- When it stops being accepted, in milliseconds since the epoch. -/
  expires : Int
  deriving Inhabited

/-- An outstanding challenge: a nonce waiting to be signed. -/
structure Challenge where
  /-- Which public key asked for it. -/
  key : String
  /-- The nonce itself, hex. -/
  nonce : String
  /-- When it stops being accepted. -/
  expires : Int
  deriving Inhabited

/--
One caller's allowance on one kind of request.

Counted in thousandths of a token so that refilling is exact: the bucket gains
`perSecond` thousandths per millisecond, which is `perSecond` tokens a second
however often it is consulted.
-/
structure Bucket where
  /-- What is left, in thousandths of a request. -/
  milliTokens : Int
  /-- When it was last refilled. -/
  refilledAt : Int
  deriving Inhabited, Repr

/--
Every allowance of one kind, by the key it belongs to.

An array with a linear `find?` over it was the first version of this, and it was
a remote denial of service on its own: `POST /challenge` needs no session, each
one appended an entry, the sweep that was supposed to remove them removed none
(it compared a *stale* token count against the brim, which is below it for every
bucket that ever spent anything), and every later request — honest ones
included — walked and copied the whole thing while holding the store's lock.
-/
abbrev Buckets := Std.HashMap String Bucket

/-- What a bucket is worth now, having refilled since it was last touched. -/
def Bucket.refilled (b : Bucket) (capacity : Int) (perSecond : Nat) (now : Int) : Bucket :=
  { milliTokens := min capacity (b.milliTokens + (now - b.refilledAt) * perSecond),
    refilledAt := now }

/--
The table with only the buckets worth keeping, and never more than `maxBuckets`.

Two rules and a ceiling. A bucket that has refilled to the brim says exactly
what an absent one says, so it goes; a bucket nobody has touched for
`idleMillis` goes whether it is full or not, which is what bounds a table whose
allowance refills at nothing per second. Both are decided on the *refilled*
value rather than the stored one, which is the bug this replaces.

The ceiling is what makes it a bound rather than a hope: a stranger can mint
distinct keys as fast as they can send bytes, and within one second none of
their buckets is either full or idle. When the table is over the line the
newest half is kept — evicting an allowance only ever gives somebody tokens
they could have had by using another key, which is the same thing the table
cannot stop anyway, and memory is the thing it must.
-/
def prunedBuckets (bs : Buckets) (capacity : Int) (perSecond : Nat) (now : Int)
    (maxBuckets : Nat) (idleMillis : Int) : Buckets :=
  let live := bs.filter fun _ b =>
    (b.refilled capacity perSecond now).milliTokens < capacity && now - b.refilledAt ≤ idleMillis
  if live.size < maxBuckets then live
  else
    let newest := live.toArray.qsort fun x y => x.2.refilledAt > y.2.refilledAt
    Std.HashMap.ofArray (newest.extract 0 (maxBuckets / 2))

/--
One running sequencer: its store, its verifier, its origin, and the memory that
authentication and rate limiting keep.

Sessions, challenges and buckets are deliberately not in the database. They are
worth nothing after a restart — a client that has to authenticate again loses a
round trip and nothing else — and keeping them out of SQLite means the write path
of the service is exactly the append.
-/
structure Node where
  /-- The store this sequencer serves. -/
  log : Sequencer
  /-- How signatures are checked. -/
  verifier : Verifier
  /-- Tuning for sessions and rate limits. -/
  limits : Limits
  /--
  The canonical public origin of this deployment, bound into every challenge.

  A signature over a nonce that named no sequencer was valid at every sequencer,
  so anybody running a second instance could relay one and open a session as the
  member who answered it. Clients check that the origin they are about to sign
  is the one they meant to talk to.

  The server states it in three places — `GET health`, the challenge, and the
  reply that hands out the token — and that is as much as a server can do. The
  other half is the client's, and it is the half that closes the attack: **a
  node must compare the origin to the URL it dialled**, not merely check that
  the server repeated itself. A relay at `evil.example` can report the real
  sequencer's origin from every route it serves, fetch a challenge from the real
  one, hand it over as its own and pass the answer back; what it cannot do is be
  the host in `settings.sequencer`. `Node/Transport.lean`'s `sessioned` takes
  the origin from the server it is already talking to and checks it against
  itself, which agrees with anybody.
  -/
  origin : String := ""
  /--
  Which keys may create a ledger, or `none` for a sequencer with no policy.

  `none` is for a sequencer embedded in a test or a single-tenant tool, where
  there is nobody to keep out. A deployment always passes a list — an empty one
  means nobody, which is the honest default for a service facing the internet
  where membership is otherwise self-serve.
  -/
  creators : Option (Array String) := none
  /--
  Whether this sequencer was built by a test.

  It is the one door to a verifier that proves nothing, and it is not a flag a
  deployment can reach: `make` takes it as an argument, the command line never
  passes it, and the only callers that do are this repository's own test suites
  and the in-process transport they run a node over. A sequencer carrying it
  also refuses every request it cannot place inside this machine, so that one
  started by accident behind a socket serves nobody.
  -/
  testOnly : Bool := false
  /-- Live sessions. -/
  sessions : IO.Ref (Array Session)
  /-- Challenges waiting to be answered. -/
  challenges : IO.Ref (Array Challenge)
  /-- One mutating-request allowance per member seen. -/
  buckets : IO.Ref Buckets
  /-- One blob-upload allowance per member seen. -/
  blobBuckets : IO.Ref Buckets
  /-- One challenge-and-authenticate allowance per key seen. -/
  authBuckets : IO.Ref Buckets

namespace Node

/--
Builds a sequencer over an open store.

A verifier that proves nothing is refused here rather than gated further in.
The gate this replaces was two of them — an environment variable and a flag on
the command line — and then a third inside the route table on the peer address,
which is the one this project's own documented topology defeats: behind nginx
on a loopback socket every request arrives from 127.0.0.1, so the refusal of
"remote" callers fired for nobody. A constructor that will not build the thing
is not a gate that can be walked around, and it leaves exactly one way to reach
`insecure` or `accept-all`: ask for it, in Lean, in a test.

`testOnly` is that ask. `Test/Sync.lean` and the node's own suites pass it; the
command line has no spelling for it at all.
-/
def make (log : Sequencer) (verifier : Verifier) (limits : Limits := {})
    (origin : String := "") (creators : Option (Array String) := none)
    (testOnly : Bool := false) : IO Node := do
  if verifier.isInsecure && !testOnly then
    throw <| IO.userError s!"the '{verifier.name}' verifier proves nothing about who signed \
      what, so a sequencer will not be built with it: anybody could authenticate as anybody. \
      Bind a real signature scheme, or run with 'Verifier.rejectAll', which refuses everybody \
      instead of admitting everybody."
  return { log, verifier, limits, origin, creators, testOnly,
           sessions := ← IO.mkRef #[], challenges := ← IO.mkRef #[],
           buckets := ← IO.mkRef ∅, blobBuckets := ← IO.mkRef ∅,
           authBuckets := ← IO.mkRef ∅ }

/--
Takes one token from a bucket, refilling it first. False when it is empty.

A key the table already holds costs a lookup and an insert and nothing else. A
key it does not is the one that makes the table grow, so it is the one that pays
for the sweep — which means the sweep happens on every insert, and the table is
bounded by `maxBuckets` between one and the next.
-/
private def takeToken (ref : IO.Ref Buckets) (key : String) (burst perSecond : Nat)
    (limits : Limits) (now : Int) : IO Bool := do
  let capacity : Int := Int.ofNat (burst * 1000)
  let bs ← ref.get
  match bs.get? key with
  | some b =>
    let current := b.refilled capacity perSecond now
    if current.milliTokens < 1000 then
      ref.set (bs.insert key current)
      return false
    ref.set (bs.insert key { current with milliTokens := current.milliTokens - 1000 })
    return true
  | none =>
    let kept := prunedBuckets bs capacity perSecond now limits.maxBuckets limits.bucketIdleMillis
    ref.set (kept.insert key { milliTokens := capacity - 1000, refilledAt := now })
    return capacity ≥ 1000

/--
The housekeeping every request does, whether it inserts anything or not.

Lapsed sessions and lapsed challenges used to be swept only when a new one was
inserted, so a burst followed by silence left the whole burst in memory until
somebody else turned up. The same goes for the buckets. None of this is
expensive — the tables are bounded by the rules above — and doing it on a tick
rather than on an insert is what makes those bounds hold while nothing is being
inserted.
-/
def tick (n : Node) : IO Unit := do
  let now ← nowMillis
  n.sessions.modify (·.filter (·.expires > now))
  n.challenges.modify (·.filter (·.expires > now))
  let sweep (ref : IO.Ref Buckets) (burst perSecond : Nat) : IO Unit :=
    ref.modify fun bs =>
      prunedBuckets bs (Int.ofNat (burst * 1000)) perSecond now n.limits.maxBuckets
        n.limits.bucketIdleMillis
  sweep n.buckets n.limits.burst n.limits.perSecond
  sweep n.blobBuckets n.limits.blobBurst n.limits.blobPerSecond
  sweep n.authBuckets n.limits.authBurst n.limits.authPerSecond

/--
Mints a challenge nonce for a key, replacing any outstanding one.

The table is swept of lapsed entries on every insert and capped, because nothing
authenticates this route: without a bound, a stranger could fill it one key at a
time and make every insert walk what they had already put there.
-/
def challenge (n : Node) (key : String) : IO Challenge := do
  let now ← nowMillis
  let c : Challenge :=
    { key, nonce := toHex (← IO.getRandomBytes 32), expires := now + n.limits.challengeMillis }
  n.challenges.modify fun cs =>
    let live := cs.filter (fun x => x.key != key && x.expires > now)
    let room := if live.size ≥ n.limits.maxChallenges then
        live.extract (live.size + 1 - n.limits.maxChallenges) live.size
      else live
    room.push c
  return c

/-- Whether a key may ask for another challenge or another authentication. -/
def allowAuth (n : Node) (key : String) : IO Bool := do
  takeToken n.authBuckets key n.limits.authBurst n.limits.authPerSecond n.limits (← nowMillis)

/--
Turns a signature over an outstanding nonce into a session.

One key may hold `maxSessionsPerKey` of them at once. A member with several
devices is ordinary and a member with a thousand is not, and the table is in
memory: when the cap is reached, the oldest of *that key's* sessions makes way,
which logs out the device that has gone longest without proving itself again.
-/
def authenticate (n : Node) (key signature : String) : IO (Option Session) := do
  let now ← nowMillis
  let cs ← n.challenges.get
  let some c := cs.find? (fun x => x.key == key && x.expires > now) | return none
  if !n.verifier.check key (challengeBytes c.nonce n.origin) signature then return none
  let s : Session :=
    { token := "seq_" ++ toBase32 (← IO.getRandomBytes 32), key,
      expires := now + n.limits.sessionMillis }
  n.challenges.modify (·.filter (fun x => x.key != key))
  n.sessions.modify fun ss =>
    let live := ss.filter (·.expires > now)
    let mine := live.filter (·.key == key)
    let room :=
      if mine.size < n.limits.maxSessionsPerKey then live
      else
        let newest := (mine.qsort fun a b => a.expires > b.expires).extract 0
          (n.limits.maxSessionsPerKey - 1)
        (live.filter (·.key != key)) ++ newest
    room.push s
  return some s

/--
The public key behind a request's bearer token, if its session is still live.

RFC 7235 makes the scheme name case-insensitive, and a conforming client that
sends `bearer` was getting 401s with nothing to say why, so the prefix is
matched on the lowercased header and the token is taken from the original.
-/
def caller? (n : Node) (r : Api.Req) : IO (Option String) := do
  let some auth := r.header "authorization" | return none
  let scheme := "bearer "
  if !auth.toLower.startsWith scheme then return none
  let presented := (auth.drop scheme.length).copy
  let now ← nowMillis
  let ss ← n.sessions.get
  let live := ss.find? fun s =>
    s.expires > now && Sha256.constantTimeEq s.token.toUTF8 presented.toUTF8
  return live.map (·.key)

/-- Takes one mutating request from a member's bucket. False when it is empty. -/
def allow (n : Node) (key : String) : IO Bool := do
  takeToken n.buckets key n.limits.burst n.limits.perSecond n.limits (← nowMillis)

/-- Takes one blob upload from a member's blob bucket, which is the larger one. -/
def allowBlob (n : Node) (key : String) : IO Bool := do
  takeToken n.blobBuckets key n.limits.blobBurst n.limits.blobPerSecond n.limits (← nowMillis)

end Node

/-! ## Bodies -/

/--
How many bytes a route will read.

A cap is the only defence that works against the two expensive things a request
can be: bytes to decode and hash, and JSON to parse. Both run before anything
knows who is calling, so the number has to be small where the caller is nobody
in particular and only generous where they have proved they are a member with a
grant.

Three routes are generous, and all three carry the same kind of thing: an
append, whose first entry is a whole store as one snapshot; a checkpoint, which
is that state sealed under a realm key; and a blob, which is a receipt. The
other two — the ones a stranger can reach — read four kilobytes, and everything
else sixty-four.
-/
def bodyLimit (limits : Limits) (method : String) (segments : List String) : Nat :=
  match method, segments with
  | "POST", ["challenge"] => 4 * 1024
  | "POST", ["authenticate"] => 4 * 1024
  | "POST", ["ledgers", _, "events"] => limits.maxAppendBytes
  | "PUT", ["ledgers", _, "realms", _, "checkpoint"] => limits.maxAppendBytes
  | "PUT", ["ledgers", _, "blobs", _] => 16 * 1024 * 1024
  | _, _ => 64 * 1024

/--
Whether a JSON body contains a number whose exponent is a weapon.

Lean's parser accepts any decimal exponent below `USize.size` and materialises
it as `m * 10 ^ n`, so twenty-two unauthenticated bytes buy ten seconds of CPU
and hundreds of megabytes. Nothing this protocol carries needs an exponent at
all, let alone a three-digit one, so anything above `100` is refused before the
parser is asked to evaluate it.

The scan tracks JSON string state, so an `e` inside a name or a base64 blob is
never mistaken for one in a number.

It reads the body where it lies, as bytes, rather than through `toList`. That
was a sixty-fold amplification on the one path this cap was raised for: a list
of characters costs some fifty bytes each, so the eleven megabytes of base64 an
eight-megabyte part arrives as peaked at six hundred megabytes of memory to
answer a question about them, and the server runs handlers in parallel. Nothing
this looks for is anything but ASCII, and every byte of a multi-byte character
is 0x80 or above, so none of them can be mistaken for a quote or an `e`.
-/
def hasHugeExponent (body : ByteArray) : Bool := Id.run do
  let ascii (c : Char) : UInt8 := c.val.toUInt8
  let mut i := 0
  let mut inString := false
  while h : i < body.size do
    let c := body[i]
    if inString then
      if c == ascii '\\' then i := i + 1
      else if c == ascii '"' then inString := false
    else if c == ascii '"' then inString := true
    else if c == ascii 'e' || c == ascii 'E' then
      let mut j := i + 1
      if j < body.size && (body[j]! == ascii '+' || body[j]! == ascii '-') then j := j + 1
      let start := j
      let mut value : Nat := 0
      while j < body.size && ascii '0' ≤ body[j]! && body[j]! ≤ ascii '9' do
        value := min 1000 (value * 10 + (body[j]!.toNat - 48))
        j := j + 1
      if j > start && value > 100 then return true
      i := j - 1
    i := i + 1
  return false

/-- A JSON error reply. -/
private def err (code : Nat) (msg : String) : Api.Reply :=
  .json code (Json.mkObj [("error", msg)])

/--
The marker that says an error message was written for the caller.

Every other `IO.Error` that reaches `handleSafe` came from somewhere inside —
SQLite, which names tables and columns; `IO.FS`, which names paths — and none of
it is any of the caller's business. So the two are told apart by construction:
a route raises a client error through `refuse`, everything else is logged under
a correlation id and answered with a sentence that says nothing.
-/
private def clientTag : String := "resources/client: "

/-- Fails the request with a message meant for whoever sent it. -/
private def refuse (msg : String) : IO α := throw <| IO.userError (clientTag ++ msg)

/--
Everything about a request that is expensive and needs nothing from the store.

The store's lock is taken around the whole of a request, which is what makes the
compare-and-swap and the single-use invite atomic — and which also means that
every byte of decoding done inside it is a byte the rest of the service spends
waiting. A sixteen-megabyte blob is seconds of pure-Lean SHA-256; an append of
the same size is a JSON parse, a base64 decode and a digest per part.
None of it asks the database anything, so none of it belongs under the lock.
-/
structure Prepared where
  /-- The body as JSON, or the sentence its sender gets instead. -/
  json : Except String Json
  /-- The hex SHA-256 of the body, for the one route whose name is that digest. -/
  bodyHash : String
  /--
  The envelope an append carries, decoded and checked, for that route alone.

  `none` means this request was not an append. `some (.error m)` means it was
  one and `m` is what its sender is told, which is a 400: every refusal in here
  is a statement about the bytes rather than about the ledger.
  -/
  envelope : Option (Except String Envelope) := none
  deriving Inhabited

/--
Reads an append's envelope and checks everything about it that needs no store.

This is the expensive half of an append and all of it is arithmetic: a base64
decode and a SHA-256 for every part, against caps that are checked first. The
caps are what make "expensive" a bounded amount of it — a body of any size used
to be allowed to spell tens of thousands of parts, and every one of them cost a
decode and a digest with the whole service waiting behind the lock.

The parts are counted off the JSON before a single one is decoded, because a
cap that is reached after the work it bounds is not a cap.
-/
def envelopeOfBody (limits : Limits) (j : Json) : Except String Envelope := do
  let stated :=
    match (j.getObjVal? "parts").bind Json.getArr? with
    | .ok ps => ps.size
    | .error _ => 0
  if stated > limits.maxParts then
    throw s!"an envelope carries at most {limits.maxParts} parts"
  let e ← Envelope.ofJson? j
  for p in e.parts do
    if !p.visible then
      throw s!"the part for realm '{p.realm}' carries no ciphertext"
    if p.ciphertext.size > limits.maxPartBytes then
      throw s!"the part for realm '{p.realm}' is larger than {limits.maxPartBytes} bytes"
    -- Every part arrives whole, and its stated digest is the one thing the
    -- signature commits to, so it is checked against the bytes: a part whose
    -- digest does not name its ciphertext would be served to every other
    -- reader as something nobody signed.
    if !p.intact then
      throw s!"the part for realm '{p.realm}' does not hash to its 'cipherHash'"
  return e

/-- The body as JSON, without touching anything: an empty body is an empty object. -/
private def parsedBody (body : ByteArray) : Except String Json :=
  let text := (String.fromUTF8? body).getD ""
  if text.trimAscii.isEmpty then .ok (Json.mkObj [])
  else if hasHugeExponent body then
    .error "a number in this body has an exponent no protocol field uses"
  else
    match Json.parse text with
    | .ok j => .ok j
    | .error _ => .error "the body is not JSON"

/--
Does the expensive half of a request, before the store is locked.

Lean is strict, so the work really has happened by the time this returns: the
parse and the digest are values in the structure rather than promises of one.
-/
def prepare (limits : Limits) (r : Api.Req) : IO Prepared := do
  let json := parsedBody r.body
  let bodyHash :=
    match r.method, r.segments with
    | "PUT", ["ledgers", _, "blobs", _] => Sha256.hexBytes r.body
    | _, _ => ""
  let envelope :=
    match r.method, r.segments with
    | "POST", ["ledgers", _, "events"] => some (json.bind (envelopeOfBody limits))
    | _, _ => none
  return { json, bodyHash, envelope }

/-- The prepared body as JSON, or the caller's own error. -/
private def bodyJson (p : Prepared) : IO Json :=
  match p.json with
  | .ok j => pure j
  | .error m => refuse m

/-- Whatever a decoder rejected, as a 400. -/
private def decoded (e : Except String α) : IO α :=
  match e with
  | .ok v => pure v
  | .error m => refuse m

/-! ## Membership and keys -/

/--
Records an agreement key a member published for themselves, or says why not.

The whole of P3 is here: the key is only ever set by the member it belongs to —
their session names the id, and the id is the signing key — and only with that
key's own signature over `memberBytes`. The sequencer stores the signature
beside the key so that every other client can ask the same question again
without trusting the answer this one gave.

`keyGeneration` is what makes the key replaceable. It is inside the signed
bytes, it only goes up, and the same number may not name two different keys —
so a member whose agreement secret has leaked publishes the next generation and
the old attestation is one this sequencer will not serve and no client should
take. Absent means zero, which is what a first key carries and what a client
that has never rotated sends.
-/
private def publishBoxPk (n : Node) (ledger key : String) (j : Json) :
    IO (Except Api.Reply Unit) := do
  let boxPk := (strField? j "boxPk").toLower
  let signature := (strField? j "boxPkSignature").toLower
  let generation := (j.getObjValAs? Nat "keyGeneration").toOption.getD 0
  if boxPk.isEmpty then
    return .error (err 400 "'boxPk' is the agreement key realm keys are sealed to")
  if !isLowerHex boxPk keyHexWidth then
    return .error (err 400 "'boxPk' is 64 hex characters")
  -- The signature first, because "you did not sign this" is an answer that does
  -- not depend on anything the server remembers, and a member who cannot sign
  -- for a key has no business learning which generation somebody else is on.
  if !n.verifier.check key (memberBytes ledger key boxPk generation) signature then
    return .error (err 403 "'boxPkSignature' is the member's own signature over their key")
  let some current ← Log.member? n.log ledger key
    | return .error (err 404 "no such member")
  if !current.boxPk.isEmpty then
    if generation < current.keyGeneration then
      return .error (err 409
        s!"this member's agreement key is at generation {current.keyGeneration}")
    if generation == current.keyGeneration && boxPk != current.boxPk then
      return .error (err 409 "another agreement key carries a higher 'keyGeneration'")
  Log.setBoxPk n.log ledger key boxPk signature generation
  return .ok ()

/--
Whether a caller administers a realm: granting, inviting and revoking.

Two conditions, and the second is what makes a grant's `role` a control rather
than a label. The realm names exactly one administrator, and a grant in the
`viewer` role does not administer anything — so a realm admin who re-grants
themselves as a viewer has stepped down, which is a sentence worth being able
to say. Holding *no* grant yet is allowed, because that is the moment a realm
has just been created and its maker is about to wrap its first key.
-/
private def administers (n : Node) (ledger : String) (rl : Realm) (key : String) : IO Bool := do
  if rl.admin != key then return false
  match ← Log.grant? n.log ledger rl.name key with
  | some g => return mayAdminister g.role
  | none => return true

/-- Everything below `/seq/v2/ledgers/{ledger}`, for a caller already known to be a member. -/
private def ledgerRoutes (n : Node) (key ledger : String) (r : Api.Req) (pre : Prepared) :
    IO Api.Reply := do
  let ledgerAdmin ← Log.isLedgerAdmin n.log ledger key
  match r.method, r.segments with
  | "GET", ["head"] =>
    return .json 200 (← Log.head n.log ledger).toJson

  /- ## The order -/
  | "GET", ["events"] => do
    -- A fetch carries the ciphertext of the parts the caller holds a grant for
    -- and withholds the rest. Every part's realm, generation and digest travel
    -- either way, because those are what the signature and the hash are over:
    -- the order and the chain are not secret, only the payloads are.
    let since := ((r.query "since").bind String.toNat?).getD 0
    let mine := (← Log.grantsOf n.log ledger key).map (·.realm)
    let events ← Log.events n.log ledger since n.limits.eventLimit
    return .json 200 (Json.mkObj [
      ("head", (← Log.head n.log ledger).toJson),
      ("events", Json.arr (events.map (·.filterJson (fun realm => mine.contains realm))))])
  | "GET", ["events", seq] => do
    -- One entry by position, filtered exactly as a fetch is. A checkpoint names
    -- the head it speaks about by hash, and this is how the client that starts
    -- from the snapshot gets hold of that envelope without walking the order
    -- back to it.
    let some pos := seq.toNat? | return err 400 "a position is a number"
    let some e ← Log.envelope? n.log ledger pos | return err 404 "no such entry"
    let mine := (← Log.grantsOf n.log ledger key).map (·.realm)
    return .json 200 (e.filterJson (fun realm => mine.contains realm))
  | "POST", ["events"] => do
    -- The envelope was decoded, capped and checked against its own digests in
    -- `prepare`, outside the lock. What is left here is everything that is a
    -- question about *this ledger*, which is what the lock is held for.
    let e ← decoded (pre.envelope.getD (.error "this request carries no envelope"))
    if e.ledger != ledger then
      return err 400 "the envelope names another ledger"
    if e.author != key then
      return err 403 "an envelope is appended by its own author"
    if !n.verifier.check e.author e.signingBytes e.signature then
      return err 403 "the signature does not verify"
    match ← Log.append n.log e with
    | .ok head => return .json 201 (Json.mkObj [("head", head.toJson)])
    | .conflict head =>
      return .json 409 (Json.mkObj [("error", "the head has moved"), ("head", head.toJson)])
    | .unknownLedger => return err 404 "no such ledger"
    | .notMember => return err 403 "not a member of this ledger"
    | .noGrant realm generation =>
      return err 403 s!"no grant on realm '{realm}' at generation {generation}"
    | .badRole realm role =>
      return err 403 s!"a grant on realm '{realm}' in role '{role}' writes nothing"

  /- ## Membership -/
  | "GET", ["members"] =>
    return .json 200 (Json.arr ((← Log.members n.log ledger).map Member.toJson))
  | "POST", ["members", who] => do
    if !ledgerAdmin then return err 403 "only a ledger admin may add members"
    if !isMemberId who then return err 400 "a member id is 64 lowercase hex characters"
    let j ← bodyJson pre
    -- Absent means "leave it as it is". A missing flag that read as `false` was
    -- a way to demote somebody — including every admin there was, after which
    -- nothing short of editing the database could add a member again.
    let admin := (j.getObjValAs? Bool "admin").toOption
    if admin == some false then
      if let some guard ← lastAdminGuard n ledger who then return guard
    Log.addMember n.log ledger who admin
    let some m ← Log.member? n.log ledger who | return err 404 "no such member"
    return .json 201 m.toJson
  | "PUT", ["members", who, "boxPk"] => do
    -- The one route that writes an agreement key, and it only ever writes the
    -- caller's own. The server supplying the key realm keys are sealed to was
    -- the hole that made every realm readable by whoever ran the server.
    if who.toLower != key then
      return err 403 "a member publishes their own agreement key and nobody else's"
    match ← publishBoxPk n ledger key (← bodyJson pre) with
    | .error reply => return reply
    | .ok _ =>
      let some m ← Log.member? n.log ledger key | return err 404 "no such member"
      return .json 200 m.toJson
  | "DELETE", ["members", who] => do
    if !ledgerAdmin then return err 403 "only a ledger admin may remove members"
    if let some guard ← lastAdminGuard n ledger who then return guard
    if !(← Log.removeMember n.log ledger who) then
      return err 404 "no such member"
    return .json 200 (Json.mkObj [("removed", who)])

  /- ## Realms and grants -/
  | "POST", ["realms"] => do
    -- Creation is first-write-wins and a realm id is a name somebody chose, so
    -- a member who may write anywhere in a ledger could otherwise squat every
    -- name in it: the record would stand in every reader's state, naming the
    -- squatter its sole administrator, and the honest creation of that name
    -- afterwards would be refused for ever. It buys no key and no write, which
    -- is why it is a denial rather than a capture — and it is a denial nobody
    -- but a ledger admin can make.
    if !ledgerAdmin then return err 403 "only a ledger admin may create a realm"
    let realm := (strField? (← bodyJson pre) "realm").trimAscii.toString
    -- A realm id is a name somebody chose, and it travels: into an invite
    -- fragment, into a client's own tables, into a `LIKE` pattern. So the
    -- character set is closed rather than escaped at each of those.
    if !isPlainId realm then
      return err 400 s!"a realm id is 1 to {idMaxLength} characters from [A-Za-z0-9._-]"
    if !(← Log.createRealm n.log ledger realm key) then
      return err 409 "that realm already exists"
    return .json 201 (Json.mkObj [("realm", realm), ("generation", jnat 0), ("admin", key)])
  | "GET", ["realms"] => do
    -- The realms the caller can open, which is not the question "which realms
    -- exist": a realm they hold no grant on is none of their business, down to
    -- its name. The generation is the one they hold a key for, so a client that
    -- sees it fall behind the realm knows it has been re-keyed without it.
    let mine ← Log.grantsOf n.log ledger key
    return .json 200 (Json.arr (mine.map fun g =>
      Json.mkObj [("realm", g.realm), ("generation", jnat g.generation), ("role", g.role)]))
  | "GET", ["realms", realm, "grants"] => do
    -- The whole list is the realm's membership graph, and a realm's membership
    -- is the most revealing thing this server holds about people who are not
    -- the caller. The wrapped keys in it are useless to anybody else, but the
    -- names are not, so the listing belongs to whoever hands them out.
    let some rl ← Log.realm? n.log ledger realm | return err 404 "no such realm"
    if !(← administers n ledger rl key) then
      return err 403 "only the realm's admin may read its grants"
    return .json 200 (Json.arr ((← Log.grants n.log ledger realm).map Grant.toJson))
  | "GET", ["realms", realm, "grants", who] => do
    -- One grant, to the member it belongs to or to the admin who issued it.
    -- The holder needs it — it is how they fetch their own key after a re-key —
    -- and everybody else is told the same thing they would be told about a
    -- grant that does not exist.
    let some rl ← Log.realm? n.log ledger realm | return err 404 "no such realm"
    if who != key && !(← administers n ledger rl key) then
      return err 404 "no such grant"
    let some g ← Log.grant? n.log ledger realm who | return err 404 "no such grant"
    return .json 200 g.toJson
  | "POST", ["realms", realm, "grants", who] => do
    let some rl ← Log.realm? n.log ledger realm | return err 404 "no such realm"
    if !(← administers n ledger rl key) then return err 403 "only the realm's admin may grant"
    if !(← Log.isMember n.log ledger who) then
      return err 400 "not a member of this ledger"
    let body ← bodyJson pre
    let wrapped ← decoded (bytesField body "wrappedKey")
    let role := strField? body "role" "viewer"
    if !isRole role then
      return err 400 s!"'role' is one of {String.intercalate ", " roles}"
    let signature := (strField? body "signature").toLower
    -- The issuer is the caller, and the generation is the realm's: neither is
    -- the body's to state, and both are inside the bytes that were signed, so a
    -- grant cannot be re-dated to a generation its issuer no longer holds.
    let grantedBy := strField? body "grantedBy" key
    if grantedBy != key then
      return err 403 "a grant is signed by whoever issues it"
    if !n.verifier.check key (grantBytes ledger realm rl.generation who role wrapped) signature then
      return err 403 "the grant's signature does not verify"
    let some g ← Log.putGrant n.log ledger realm who wrapped role key signature
      | return err 404 "no such realm"
    return .json 201 g.toJson
  | "DELETE", ["realms", realm, "grants", who] => do
    let some rl ← Log.realm? n.log ledger realm | return err 404 "no such realm"
    if !(← administers n ledger rl key) then return err 403 "only the realm's admin may revoke"
    let some generation ← Log.revokeGrant n.log ledger realm who | return err 404 "no such realm"
    return .json 200 (Json.mkObj [("realm", realm), ("revoked", who),
                                  ("generation", jnat generation)])

  /- ## Invites -/
  | "POST", ["realms", realm, "invites"] => do
    -- An invite is a grant made out to nobody in particular: the realm key
    -- sealed to an ephemeral key whose secret half leaves by another road. The
    -- admin chooses the generation by making it now — it is the realm's current
    -- one, never a number from the body.
    let some rl ← Log.realm? n.log ledger realm | return err 404 "no such realm"
    if !(← administers n ledger rl key) then return err 403 "only the realm's admin may invite"
    let inv ← decoded (Invite.ofJson? (← bodyJson pre) realm rl.generation key)
    -- Both of them are checked for width here rather than at the moment the
    -- proof is verified, because an invite whose signing key is not a key is an
    -- invite nobody can ever redeem: better a 400 now than a 403 later.
    if !isMemberId inv.signPk || !isLowerHex inv.boxPk keyHexWidth then
      return err 400 "an invite carries both of its public keys, 64 hex characters each"
    if !isRole inv.role then
      return err 400 s!"'role' is one of {String.intercalate ", " roles}"
    -- An expiry used to be any string at all, compared with `≤` against a local
    -- naive clock: `"z"` never lapsed, a browser's UTC stamp sorted after every
    -- local one, and an offer could be made to stand for ever. So it is parsed,
    -- normalised to one UTC shape — which is what keeps the lazy sweep's string
    -- comparison a chronological one — and bounded.
    let some expires := isoNormalise? inv.expires
      | return err 400 "'expires' is an ISO-8601 instant in UTC, like 2026-10-01T12:00:00Z"
    let some lapses := isoSeconds? expires | return err 400 "'expires' is not a time"
    let some now := isoSeconds? (← Log.utcNow) | return err 500 "the clock is not readable"
    if lapses ≤ now then
      return err 400 "an invite expires in the future"
    if lapses > now + Int.ofNat (n.limits.inviteMaxDays * 86400) then
      return err 400 s!"an invite may not stand for more than {n.limits.inviteMaxDays} days"
    if !(← Log.putInvite n.log ledger { inv with expires }) then
      return err 409 "an invite under that key is already outstanding"
    return .json 201 { inv with expires }.toJson
  | "GET", ["realms", realm, "invites"] => do
    let some rl ← Log.realm? n.log ledger realm | return err 404 "no such realm"
    if !(← administers n ledger rl key) then
      return err 403 "only the realm's admin may read its invites"
    return .json 200 (Json.arr ((← Log.invites n.log ledger realm).map Invite.toJson))
  | "DELETE", ["realms", realm, "invites", signPk] => do
    let some rl ← Log.realm? n.log ledger realm | return err 404 "no such realm"
    if !(← administers n ledger rl key) then
      return err 403 "only the realm's admin may withdraw an invite"
    if !(← Log.deleteInvite n.log ledger realm signPk.toLower) then
      return err 404 "no such invite"
    return .json 200 (Json.mkObj [("realm", realm), ("withdrawn", signPk.toLower)])

  /- ## Checkpoints -/
  | "PUT", ["realms", realm, "checkpoint"] => do
    let some rl ← Log.realm? n.log ledger realm | return err 404 "no such realm"
    -- Any grant holder may commit, viewers included: a checkpoint is a claim
    -- about what you replayed, and a viewer replays exactly what an admin does.
    -- What is refused, here as on the append, is a role that writes nothing.
    let some g ← Log.grant? n.log ledger realm key | return err 403 "no grant on this realm"
    if !mayWrite g.role then
      return err 403 s!"a grant in role '{g.role}' commits to nothing"
    let c ← decoded (Checkpoint.ofJson? (← bodyJson pre) ledger realm key)
    if c.generation != rl.generation then
      return err 400 "a checkpoint is written under the realm's current generation"
    -- The commitment names the envelope its `seq` stands for, and the server is
    -- the one party that knows which envelope that is. Checking it here is what
    -- stops a signed snapshot from pointing at a link of a chain that never had
    -- one, which a reader starting from the snapshot could not tell apart from
    -- the real thing.
    let some headHash ← Log.hashAt n.log ledger c.seq
      | return err 400 "the ledger has not reached that position"
    if c.headHash != headHash then
      return err 400 "'headHash' is not the hash of the envelope at that position"
    if !n.verifier.check key c.commitmentBytes c.signature then
      return err 403 "the signature does not verify"
    if !(← Log.putCheckpoint n.log c) then
      return err 409 "this author has already committed to a position further along"
    return .json 200 c.toJson
  | "GET", ["realms", realm, "checkpoint"] => do
    if (← Log.grant? n.log ledger realm key).isNone then
      return err 403 "no grant on this realm"
    -- One per author, furthest along first. Which of them is worth anything is
    -- the reader's decision, not the server's: they take the ones signed by a
    -- realm admin their own replayed state records, or by the inviter they
    -- pinned when they joined, and they check the signature themselves.
    return .json 200 (Json.arr ((← Log.checkpoints n.log ledger realm).map Checkpoint.toJson))

  /- ## Blobs -/
  | "PUT", ["blobs", hash] => do
    -- The name is the hash of the ciphertext, so the server can check it without
    -- being able to read it, and two clients that store the same bytes agree.
    -- The digest was taken in `prepare`, before the store was locked: it is a
    -- question about the body alone, and on sixteen megabytes it is seconds.
    if hash.toLower != pre.bodyHash then
      return err 400 "the body does not hash to that name"
    -- Membership is self-serve, so "a member may store bytes" is not a bound on
    -- anything. The quota is, and it is per ledger rather than per member for
    -- the same reason: whoever keeps the ledger is who pays for it.
    match ← Log.putBlob n.log ledger pre.bodyHash r.body n.limits.blobQuotaBytes with
    | .ok held =>
      return .json 201 (Json.mkObj [("hash", pre.bodyHash), ("bytes", jnat r.body.size),
                                    ("held", jnat held), ("quota", jnat n.limits.blobQuotaBytes)])
    | .overQuota held quota =>
      return err 507 s!"this ledger holds {held} of {quota} bytes of blobs"
  | "GET", ["blobs", hash] => do
    let some bytes ← Log.blob? n.log ledger hash.toLower | return err 404 "no such blob"
    return .bytes 200 "application/octet-stream" bytes
  | "DELETE", ["blobs", hash] => do
    -- There is no collector, because the sequencer cannot read an entry and so
    -- cannot know what the order still points at. Somebody who *can* read it
    -- says so instead, and that is an administrator: a ledger admin, or the
    -- admin of a realm here, who are the people a quota is an argument with.
    if !ledgerAdmin && !(← Log.administersAnyRealm n.log ledger key) then
      return err 403 "only an administrator may remove a blob"
    if !(← Log.deleteBlob n.log ledger hash.toLower) then
      return err 404 "no such blob"
    return .json 200 (Json.mkObj [("removed", hash.toLower),
                                  ("held", jnat (← Log.blobBytes n.log ledger))])

  | _, _ => return err 404 "no such route"
where
  /--
  Refuses to take the last admin away from a ledger, by removal or by demotion.

  A ledger with no admin left cannot be repaired from outside: nobody can add a
  member, remove one, or make anybody an admin again. The guard used to be on
  removal only, so re-posting a member with no `admin` field demoted them, and
  two such requests stranded the ledger for good.
  -/
  lastAdminGuard (n : Node) (ledger who : String) : IO (Option Api.Reply) := do
    let admins := (← Log.members n.log ledger).filter (·.admin)
    if admins.size == 1 && admins.any (·.key == who) then
      return some (err 400 "a ledger keeps at least one admin")
    return none

/--
The invite a proof entitles its bearer to, or the reply that turns them away.

Both routes a holder of an invite may call — reading the sealed key and spending
it — ask the same four questions in the same order, so they ask them here. The
proof is checked before the generation so that only somebody who really holds the
invite can cause it to be purged; an invite already past its moment is purged by
anybody who mentions it, which costs nothing, because it was worthless already.
-/
private def provenInvite (n : Node) (key ledger realm signPk proof : String) :
    IO (Except Api.Reply Invite) := do
  let some inv ← Log.invite? n.log ledger realm signPk
    | return .error (err 404 "no such invite")
  if Log.elapsed inv.expires (← Log.utcNow) then
    discard <| Log.deleteInvite n.log ledger realm signPk
    return .error (err 410 "this invite has expired")
  if !n.verifier.check signPk (joinBytes ledger realm key) proof then
    return .error (err 403 "the proof does not verify")
  let some rl ← Log.realm? n.log ledger realm | return .error (err 404 "no such invite")
  if rl.generation != inv.generation then
    discard <| Log.deleteInvite n.log ledger realm signPk
    return .error
      (err 409 s!"this invite was made at an older generation than {rl.generation}")
  return .ok inv

/--
Reading an invite's sealed key: the first half of accepting one.

The invite link is short on purpose — it carries the invite's secret and nothing
else, and that secret never reaches the server — so the sealed realm key has to
be fetchable from here, by whoever can prove they hold the matching invite key.
The proof is the same signature over the same `joinBytes` that the join itself
takes, which is why reading is safe: anybody who could unseal what comes back
could have joined outright.

What comes back is everything the joiner needs and nothing they could get
another way: the sealed key, the key it was sealed to, the generation, the role
their grant will carry, and `inviterSignPk` — the member id of the admin who
made the invite, which is the one key a newcomer has any reason to trust before
they have replayed a single entry.

Nothing is consumed. The joiner unseals the key with the invite's box secret,
re-seals it to their own agreement key, and then joins; two requests, because the
key the grant must hold is one only the joiner can compute.
-/
private def redeemRoute (n : Node) (key ledger realm signPk : String) (pre : Prepared) :
    IO Api.Reply := do
  if (← Log.realm? n.log ledger realm).isNone then return err 404 "no such invite"
  let proof ← decoded (strField (← bodyJson pre) "proof")
  match ← provenInvite n key ledger realm signPk.toLower proof with
  | .error reply => return reply
  | .ok inv =>
    return .json 200 (Json.mkObj [("ledger", ledger), ("realm", realm),
                                  ("wrappedKey", Json.str (toBase64 inv.wrappedKey)),
                                  ("inviteBoxPk", inv.boxPk),
                                  ("inviterSignPk", inv.createdBy),
                                  ("generation", jnat inv.generation), ("role", inv.role)])

/--
Spending an invite: how somebody who is not a member yet becomes one.

The caller is authenticated as themselves — the session names their signing key,
and that key is the member id the grant is made out to — so what the invite adds
is not "who are you" but "who said you could". That is the proof: a signature by
the invite's own key over `joinBytes`, which names this ledger, this realm and
this member and so cannot be lifted off one join and used for another.

The grant that comes out of it is signed by the joiner, over the role the invite
named and the generation the realm is on. That is the one case where a grant's
issuer is its holder, and it is sound because the key inside it is one they
already hold: the invite handed it to them, and re-sealing it to themselves adds
nothing they did not have.

The refusals that are not about the proof are about time passing. An invite is
single-use, so a second attempt finds nothing and is a 404; and a revoke between
the invite and the join has re-keyed the realm, which leaves the sealed key
inside the invite opening nothing, so that is a 409 rather than a grant on a
generation nobody uses any more. The store asks both again inside the
transaction, where they are still true at the moment of the write.
-/
private def joinRoute (n : Node) (key ledger realm : String) (pre : Prepared) : IO Api.Reply := do
  if (← Log.realm? n.log ledger realm).isNone then return err 404 "no such invite"
  let j ← bodyJson pre
  let signPk := (← decoded (strField j "inviteSignPk")).toLower
  let proof ← decoded (strField j "proof")
  let wrapped ← decoded (bytesField j "wrappedKey")
  let signature := (strField? j "signature").toLower
  match ← provenInvite n key ledger realm signPk proof with
  | .error reply => return reply
  | .ok inv =>
    if !n.verifier.check key (grantBytes ledger realm inv.generation key inv.role wrapped)
        signature then
      return err 403 "the grant's signature does not verify"
    match ← Log.spendInvite n.log ledger realm signPk key wrapped signature with
    | .ok g =>
      return .json 201 (Json.mkObj [("grant", g.toJson), ("generation", jnat g.generation)])
    | .unknownInvite => return err 404 "no such invite"
    | .expired => return err 410 "this invite has expired"
    | .staleGeneration generation =>
      return err 409 s!"this invite was made at an older generation than {generation}"

/--
Where a request came from, as far as the transport could tell.

It is one question and it has three answers, because the third is real: the
in-process transport the node's own tests use has no socket at all, and neither
has a call made from inside this binary. `unknown` is not `loopback` and is not
`remote`; what depends on it says what it does with each.
-/
inductive Peer
  /-- The connection came from a loopback address on this machine. -/
  | loopback
  /-- The connection came from somewhere else. -/
  | remote
  /--
  There was no connection at all: the caller is inside this binary.

  It is stated rather than inferred. The absence of a peer address used to mean
  both "nobody dialled anything" and "the transport did not say", and a check
  that trusts the second because it meant the first is a check that fails open
  the moment a socket arrives without one.
  -/
  | inProcess
  /-- A connection whose peer the transport could not name. -/
  | unknown
  deriving Inhabited, BEq, Repr

/--
Whether this is a caller this machine can vouch for.

`unknown` is not one. A transport that could not name its peer is evidence of
nothing, and the in-process caller — the only one with no peer to name — says
so for itself.
-/
def Peer.isLocal : Peer → Bool
  | .loopback | .inProcess => true
  | .remote | .unknown => false

/-- Handles one request below `/seq/v2`. -/
def handle (n : Node) (r : Api.Req) (pre : Prepared) (peer : Peer := .inProcess) :
    IO Api.Reply := do
  -- Before anything is routed: nothing this protocol names contains a control
  -- character, and a path that carries one is a path aimed at something that
  -- writes paths down. Segments arrive percent-*decoded*, so `%0A` is a newline
  -- by the time it gets here.
  if r.segments.any hasControl then
    return err 400 "a path segment carries a control character"
  if r.body.size > bodyLimit n.limits r.method r.segments then
    return err 413 "the body is larger than this route accepts"
  match r.method, r.segments with
  | "GET", ["health"] =>
    return .json 200 (Json.mkObj [("status", "ok"), ("schema", jnat Log.targetVersion),
                                  ("verifier", n.verifier.name), ("origin", n.origin)])
  | "POST", ["challenge"] => do
    let key ← decoded (strField (← bodyJson pre) "key")
    if !isMemberId key then return err 400 "a member id is 64 lowercase hex characters"
    if !(← n.allowAuth key) then return err 429 "too many challenges; slow down"
    let c ← n.challenge key
    return .json 200 (Json.mkObj [("key", key), ("nonce", c.nonce), ("origin", n.origin),
                                  ("expires", Json.num (JsonNumber.fromInt c.expires))])
  | "POST", ["authenticate"] => do
    let j ← bodyJson pre
    let key ← decoded (strField j "key")
    if !isMemberId key then return err 400 "a member id is 64 lowercase hex characters"
    let signature ← decoded (strField j "signature")
    if !(← n.allowAuth key) then return err 429 "too many attempts; slow down"
    let some s ← n.authenticate key signature
      | return err 401 "no outstanding challenge, or the signature does not verify"
    -- The origin is stated again here, on the reply that hands out the token,
    -- so that a client has it from the same exchange it signed and can compare
    -- all three — the origin `health` reported, the one the challenge named and
    -- this one — against the URL it dialled. A relay that fetches challenges
    -- from the real sequencer can repeat the string; what it cannot do is be
    -- the host the client typed.
    return .json 200 (Json.mkObj [("token", s.token), ("key", s.key),
                                  ("origin", n.origin),
                                  ("expires", Json.num (JsonNumber.fromInt s.expires))])
  | _, _ => do
    -- The verifier is no longer what is asked here: one that proves nothing
    -- cannot be built into a sequencer at all (`Node.make`). What is asked is
    -- whether this node was built by a test, because that is the one door to
    -- such a verifier, and a test's node behind a socket should serve nobody.
    -- `unknown` is refused with `remote`: a transport that could not name its
    -- peer is evidence of nothing, and the in-process caller says so itself.
    if n.testOnly && !peer.isLocal then
      return err 403 "this sequencer was built for a test, so it answers \
                      authenticated routes on this machine only"
    let some key ← n.caller? r | return err 401 "missing or expired session token"
    -- Every mutating route a session can reach is metered, not just the append:
    -- membership, realms, grants, invites, checkpoints, joins and blobs all
    -- write, and a member with a burst of tokens spending them on any of them
    -- is the same request queue behind the same lock. Reads are left out, and
    -- the two unauthenticated routes have their own, smaller allowance above.
    if r.method != "GET" then
      let spent ←
        match r.method, r.segments with
        | "PUT", ["ledgers", _, "blobs", _] => n.allowBlob key
        | _, _ => n.allow key
      if !spent then return err 429 "too many requests; slow down"
    match r.segments with
    | ["ledgers"] => do
      if r.method != "POST" then return err 404 "no such route"
      -- Membership of this service is self-serve, so ledger creation is not:
      -- a key on the internet that could make ledgers could make unlimited
      -- ledgers, administrate all of them, and fill the disk through them.
      match n.creators with
      | some allowed => if !allowed.contains key then
          return err 403 "this sequencer does not take new ledgers from that key"
      | none => pure ()
      let ledger := (strField? (← bodyJson pre) "ledger").trimAscii.toString
      -- The same closed character set a realm id has, and for one more reason:
      -- an invite fragment joins its fields with `:`, and a ledger id that
      -- contained one made `(ledger="a", realm="b:c")` and `(ledger="a:b",
      -- realm="c")` the same link.
      if !isPlainId ledger then
        return err 400 s!"a ledger id is 1 to {idMaxLength} characters from [A-Za-z0-9._-]"
      if !(← Log.createLedger n.log ledger key) then
        return err 409 "that ledger already exists"
      -- No agreement key here, not even the creator's own. A member publishes
      -- theirs with their own signature over it, through one route, and there
      -- being exactly one such route is most of what makes the key trustworthy.
      return .json 201 (Json.mkObj [("ledger", ledger), ("admin", key)])
    | "ledgers" :: ledger :: rest => do
      -- "There is no such ledger" and "that one is not yours" are the same
      -- answer, because ledger ids are names people choose and telling the two
      -- apart enumerates who keeps books here.
      if !(← Log.ledgerExists n.log ledger) then return err 404 "no such ledger"
      -- Membership is the gate on everything about a ledger, so it is asked once
      -- here rather than in each route below. The two halves of accepting an
      -- invite are the exception, and have to be: an invite is precisely an
      -- offer to somebody who is not a member.
      match r.method, rest with
      | "POST", ["realms", realm, "invites", signPk, "redeem"] =>
        redeemRoute n key ledger realm signPk pre
      | "POST", ["realms", realm, "join"] => joinRoute n key ledger realm pre
      | _, _ =>
        if !(← Log.isMember n.log ledger key) then
          return err 404 "no such ledger"
        ledgerRoutes n key ledger { r with segments := rest } pre
    | _ => return err 404 "no such route"

/--
Runs a request, and says both what to answer and what to write down.

The two kinds of failure are told apart here. A route that refuses its caller
says so through `refuse`, and that sentence is the reply. Anything else — SQLite
naming a table, `IO.FS` naming a path — is somebody else's business entirely, so
it is logged against a correlation id and answered with a 500 that carries the
id and nothing else. "Which request was that?" is then a question with an
answer, without the answer being on the wire.
-/
private def answer (n : Node) (r : Api.Req) (pre : Prepared) (peer : Peer) (path : String) :
    IO (Api.Reply × String) := do
  try
    let reply ← handle n r pre peer
    return (reply, toString reply.code)
  catch e =>
    match Str.dropPrefix? (toString e) clientTag with
    | some msg => return (err 400 msg, "400")
    | none =>
      let code := toHex (← IO.getRandomBytes 4)
      -- The path is escaped on the way to stderr as well as on the way to the
      -- trail: a log is a log wherever it is being read.
      IO.eprintln s!"sequencer: {logField r.method 16} {path} failed ({code}): {e}"
      return (.json 500 (Json.mkObj [("error", "the request could not be completed"),
                                     ("code", code)]), s!"500 {code}")

/--
Runs a request with the store to itself, answering for it, and writing it down.

This is the only place the store's mutex is taken, and it is taken around the
whole request rather than around each transaction: the checks a route makes
before it writes — a realm's generation, who administrates it, whether an invite
is still there — are as much a part of the decision as the write itself.

Every mutating request leaves a line in the audit trail, refusals included,
because the useful half of an incident record is the attempts that failed. Every
field of that line is escaped where it is assembled: the path and the member id
arrive from whoever sent the request, and a trail somebody else can write lines
into is not a record of anything.

The expensive half of the request — the digest of a blob, the parse of a body,
the decode and the digests of an append's parts — is done by `prepare` before the
lock is taken, and the tables that authentication keeps are swept by `tick` once
it is.
-/
def handleSafe (n : Node) (r : Api.Req) (peer : Peer := .inProcess) : IO Api.Reply := do
  let pre ← prepare n.limits r
  Log.exclusively n.log do
    n.tick
    let path := logField ("/" ++ String.intercalate "/" r.segments)
    let (reply, outcome) ← answer n r pre peer path
    -- A GET changes nothing, so it is not what an incident record is for; and
    -- leaving reads out is what keeps the file readable by a person.
    if r.method != "GET" then
      let who := logField ((← n.caller? r).getD "-") keyHexWidth
      Log.audit n.log s!"{← Log.utcNow} {logField r.method 16} {path} {who} {outcome}"
    return reply

end Sync
end Resources
