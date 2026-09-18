import Resources.Node.Keys

/-!
# Events in, envelopes out

An `Event` is what the ledger writes: an author, a moment, and one part per
realm the write touches. An `Sync.Envelope` is what the sequencer orders: the
same parts, each encrypted under its realm's key, plus a signature over all of
them. This file is the two directions between them, and it is the only place
that knows both.

## What a part's plaintext is

`Codec.encode (eventId, composedAt, basedOn, part)`, as nested products in that
order. The event's three scalars travel *inside every part* rather than beside
them, so that a reader who can open one part of an envelope can rebuild a whole
`Event` from it — which is what makes a part, rather than an event, the unit of
sharing. The cost is that they are repeated; the gain is that a node holding one
realm's key is never handed a fragment it cannot apply.

Readers check that every part they could open agrees about those three. A
disagreement means the author built something incoherent, and the honest
response is to apply none of it: the envelope becomes a no-op, recorded so that
the order stays complete.

## What the ciphertext is

`nonce ++ seal(realmKey[generation], nonce, ad, plaintext)` with

```
ad = seg("resources/part/v1") ++ seg(ledger) ++ seg(realm) ++ seg(generation) ++ seg(author)
```

The realm is inside the plaintext as well as in the associated data, so a part
cannot be re-labelled as another realm's; the author is in the associated data,
so a part cannot be re-attributed; and the generation is there so that a part
sealed under an old key cannot be presented as one sealed under the new.

## What a reader checks

Everything. Version 1 signed each part's *ciphertext*, so a reader who had been
handed a filtered envelope was shown neither the bytes the signature covered nor
the bytes the hash digested, and the protocol had a state called "unverifiable"
in which an event was applied on the sequencer's word. Version 2 signs each
part's `cipherHash`, which travels whether the ciphertext does or not — so there
is one thing to check and every reader can check it:

* the signature over `signingBytes`, against the author, always;
* each received part's bytes against the `cipherHash` the signature covers;
* and, in `Node/Sync.lean`, the position and the chain, against a hash this node
  recomputed rather than one a server stated.

A failure of any of them is a refusal that stops the pull where it is. There is
no state in which an event is applied unverified.

The author of a rebuilt event is the envelope's author — the key that signed it
— and never anything read out of a plaintext. An author inside the ciphertext
would be a claim; the signature is the only claim anybody proved.
-/

open Lean

namespace Resources
namespace Node

/-- The domain a part's ciphertext is bound to. -/
def partTag : String := "resources/part/v1"

/-- The associated data one part is sealed under. -/
def partAd (ledger realm : String) (generation : Nat) (author : String) : ByteArray :=
  Sync.segStr partTag ++ Sync.segStr ledger ++ Sync.segStr realm ++ Sync.segNat generation
    ++ Sync.segStr author

/-- What one part's plaintext encodes: the event's scalars, then the part itself. -/
abbrev PartPlaintext := String × String × Nat × Part

namespace Envelope

/-! ## Composing -/

/--
Encrypts one local event into an envelope at a stated position, and signs it.

`basedOn` is passed in rather than read off the event because the two orders are
different orders. In the local log it is the local sequence number the author had
reached; on the sequencer it has to be the remote one, or a reader has no way to
tell what the author had seen. `Sync.push` passes the remote head it is
appending onto, and passes the new one when a conflict makes it try again.
-/
def compose (suite : CryptoSuite) (kr : Keyring) (ledger : String) (e : Event)
    (seq : Nat) (prevHash : String) (basedOn : Nat) : IO Sync.Envelope := do
  let author := kr.identity.id
  let mut parts : List Sync.Part := []
  for p in e.parts do
    let realm := p.realm.val
    let some (generation, key) ← Keys.latest kr realm
      | throw <| IO.userError s!"this node holds no key for realm '{realm}', so it cannot \
                                 encrypt what it wrote there"
    let nonce ← suite.randomBytes suite.nonceSize
    let plaintext := Codec.encode ((e.id, e.composedAt, basedOn, p) : PartPlaintext)
    let sealed := suite.sealPart key nonce (partAd ledger realm generation author) plaintext
    parts := parts ++ [{ realm, generation, ciphertext := nonce ++ sealed }]
  let unsigned : Sync.Envelope :=
    { ledger, seq, prevHash, author, parts, signature := "" }
  return { unsigned with signature := Identity.signHex suite kr.identity unsigned.signingBytes }

/-! ## Opening -/

/-- What an envelope came to for the node that received it. -/
structure Opened where
  /-- The event rebuilt from the parts this node could open; `none` when it could open none. -/
  event : Option Event
  /-- How many parts came back that this node could not open. -/
  unreadable : Nat
  /--
  The realms those parts belonged to, each once.

  The count says how much was missed and this says *what*, which is a different
  question and the one a checkpoint asks: a projection of a realm is only
  comparable with somebody else's when nothing written in that realm was missed.
  -/
  unreadableRealms : List String
  deriving Inhabited

/-- How reading an envelope ended. -/
inductive Read
  /-- It opened: what this node can see of it, and what it cannot. -/
  | ok (opened : Opened)
  /-- It was coherent bytes saying incoherent things. Recorded as a no-op; the order goes on. -/
  | rejected (why : String)
  /-- Something that had to open did not. The puller stops here and keeps its position. -/
  | refused (why : String)
  deriving Inhabited

/--
Decrypts what this node holds keys for, checks everything, and rebuilds the
event.

The signature comes first, because nothing else in here means anything until the
author is settled: a part opens under a realm key, and a realm key is held by
everybody in the realm, so an envelope whose signature was not checked is one
any grant holder could have written under anybody's name.

The three outcomes are the three kinds of thing that can be wrong, and they are
answered differently on purpose. A part this node holds no key for is not a
problem at all — it is the normal case for a realm somebody else works in. A
part whose bytes do not hash to the digest the signature covers, or whose key
this node *does* hold and which does not open, is a refusal: the bytes were
changed between the author and here. Parts that open and then disagree about
which event they belong to are a rejection: nothing here can be applied, and the
entry stands as a no-op so that the order is not left with a hole.
-/
def read (suite : CryptoSuite) (kr : Keyring) (ledger : String) (env : Sync.Envelope) :
    IO Read := do
  unless suite.checkHex env.author env.signingBytes env.signature do
    return .refused s!"the signature on entry {env.seq} does not verify"
  let mut readable : List Part := []
  let mut unreadable : Nat := 0
  let mut missed : List String := []
  let miss := fun (realm : String) (xs : List String) =>
    if xs.contains realm then xs else xs ++ [realm]
  let mut scalars : Option (String × String × Nat) := none
  let mut disagreed : Option String := none
  for p in env.parts do
    -- A part the sequencer withheld carries its digest and no bytes; one it
    -- handed over has to be the bytes that digest names, which is the whole of
    -- what the signature says about a payload.
    if p.visible && !p.intact then
      return .refused s!"the part for realm '{p.realm}' does not hash to the digest its \
                         author signed"
    match ← (if p.visible then Keys.get kr p.realm p.generation else pure none) with
    | none =>
      unreadable := unreadable + 1
      missed := miss p.realm missed
    | some key =>
      if p.ciphertext.size < suite.nonceSize then
        return .refused s!"the part for realm '{p.realm}' carries no nonce"
      let nonce := take p.ciphertext suite.nonceSize
      let body := drop p.ciphertext suite.nonceSize
      let some plain :=
          suite.openPart key nonce (partAd ledger p.realm p.generation env.author) body
        | return .refused s!"the part for realm '{p.realm}' does not open under the key this \
                             node holds for it"
      match (Codec.decode plain : Option PartPlaintext) with
      | none =>
        -- Authentic bytes this binary cannot read: a newer writer, not a liar.
        unreadable := unreadable + 1
        missed := miss p.realm missed
      | some (id, composedAt, basedOn, part) =>
        match scalars with
        | none => scalars := some (id, composedAt, basedOn)
        | some (id', composedAt', basedOn') =>
          if id != id' || composedAt != composedAt' || basedOn != basedOn' then
            disagreed := some s!"the parts of entry {env.seq} disagree about which event \
                                 they belong to"
        readable := readable ++ [part]
  if let some why := disagreed then
    return .rejected why
  match scalars with
  | none =>
    return .ok { event := none, unreadable, unreadableRealms := missed }
  | some (id, composedAt, basedOn) =>
    return .ok { event := some { id, author := ⟨env.author⟩, composedAt, basedOn,
                                 parts := readable }
                 unreadable, unreadableRealms := missed }

end Envelope

end Node
end Resources
