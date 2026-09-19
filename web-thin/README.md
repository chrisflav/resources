# web-thin

The browser client for one realm of an end-to-end-encrypted ledger.

It holds exactly one realm key, reads the realm out of the sequencer, and shows
the three figures a participant in a shared budget actually wants: what has been
spent, where everybody stands, and what would square them up. It can add a cost,
withdraw one of its own that has not been divided yet, mark a claim met, and
open the receipt behind a cost that carries one.

It is *thin* in one specific sense: the sequencer is a dumb, blind ordering
service, so every fact on the screen is one this client worked out for itself
from bytes it decrypted and checked. It speaks protocol version 2 (`/seq/v2`)
and format version 8.

```
npm ci
npm run dev      # Vite, proxying /seq to a sequencer on 127.0.0.1:8088
npm run build    # tsc --strict, then a production bundle
npx vitest run   # 489 tests: byte format, arithmetic, crypto, blobs, sync, conformance
```

`npx vitest run` reads `../conformance/vectors.json` and
`../conformance/rejects.json`, so it has to be run from a checkout of the whole
repository rather than from this directory alone.

## What is on the screen

Everything, and only what was verified. That sentence used to be false in two
ways at once, and both are worth stating plainly because they are what changed.

Version 1 of the protocol signed and hashed each part's *ciphertext*. A fetch
hands back only the parts the caller holds a grant for, so a reader who could
not open every realm of an envelope was shown neither the bytes the signature
covered nor the bytes the hash digested. They could check nothing. The protocol
had a state called `unverifiable` for that, the client folded those envelopes
into the balances at the top of the page anyway, and mentioned them in a table
at the bottom.

Version 2 signs and hashes each part's `cipherHash` — the hex SHA-256 of the
ciphertext — which is the same string for every reader. So there is no
`unverifiable` any more, and no state on the screen that nothing has checked.
An event is verified and applied, or it is refused.

An envelope is refused unless **all** of this holds:

- its signature verifies against its own author, over
  `seg("resources/seq/v2/envelope-sig") ++ seg(ledger) ++ seg(seq) ++
  seg(prevHash) ++ seg(author) ++ seg(|parts|)` and, for each part,
  `seg(realm) ++ seg(generation) ++ seg(cipherHash)`;
- it names this ledger;
- its `seq` is exactly one more than the entry before it — a dropped envelope
  leaves a gap, and a gap is a refusal;
- its `prevHash` equals the hash **this client recomputed** for the entry before
  it, never a hash the server stated;
- the `hash` the sequencer states, if it states one, is the hash of what it
  actually sent;
- every ciphertext that arrived hashes to that part's `cipherHash`.

The first envelope that fails any of these stops the fold. Nothing after it is
applied, `verified and applied up to seq N` stays at N, and a red line at the
top of the page says which entry stopped it and why.

Two outcomes that are *not* refusals, because they leave the chain intact and
are facts about a part rather than about the order:

- **rejected** — verified, decrypted, understood, and refused on the ledger's
  own authorisation and bounds rules. Somebody's mistake, with the sentence
  beside it.
- **unreadable** — every part belongs to a realm or a key generation this
  member holds no key for. Nobody's mistake, and under version 2 the chain costs
  nothing: the signature and the hash were checked either way. A part of *this*
  realm that will not open is still a gap, and the realm is not displayed until a
  checkpoint covers it — see "Where the state starts".
- **duplicate** — an event id already applied in this run. The envelope is
  signed and linked; applying it twice would double a cost.

## Where the state starts

A checkpoint is one member's claim about what they replayed, so it is worth
exactly as much as the member. The sequencer keeps one per author and hands back
the list; which of them is worth anything is this client's decision.

It takes the newest one whose author it trusts — itself, or an admin of the
realm in the state it already holds, or, *only while that state records nobody
as an admin*, the inviter pinned when the link was accepted — and only after
checking, in this order:

1. that it holds the key for the generation at all;
2. that `snapshotHash` is the digest of the bytes that arrived, so a swapped
   snapshot under a valid signature is caught before anything is done with it;
3. that the commitment's signature verifies over
   `seg("resources/seq/v2/checkpoint") ++ seg(ledger) ++ seg(realm) ++
   seg(generation) ++ seg(seq) ++ seg(stateHash) ++ seg(headHash) ++
   seg(snapshotHash)`;
4. that the snapshot opens under the realm key with the right additional data
   and decodes;
5. that **re-encoding** the decoded state gives exactly `stateHash` — which is a
   question about bytes rather than about fields, and has exactly one answer
   because the decoder refuses every non-canonical spelling;
6. that the envelope at `seq` really is the one `headHash` names, by fetching it,
   verifying its signature and recomputing its hash here.

A checkpoint that fails any of those is ignored, with a sentence saying which,
and the realm is replayed from the beginning instead. What used to happen is
worth remembering: `checkpointBytes` existed and was never called, so any grant
holder could seal a `State` of their own choosing under the realm key, sign it
with their own key, and every thin client would boot from it and print "verified
up to seq N" over it.

**Replaying from the beginning is not always correct, and this client no longer
says it is.** A browser holds the generations it was granted and a node holds
every one, so after a revoke or a key rotation a replay from zero skips every
part written before it — and arrives, part way along, at something that reads
like a different ledger. Two rules follow, and both are the reader's:

- **Where a log starts is a position.** A snapshot is what a log begins from,
  and it counts as a beginning only as the whole first entry of the fold — one
  part in the envelope, and that part a snapshot — when the fold started from
  nothing. `applyOp` refuses a snapshot everywhere, including on an empty
  ledger, so one anywhere else is a part that is skipped like any other invalid
  one; and an event carrying a snapshot beside something else is not a beginning
  at all. This used to be decided by asking whether the state the reader had
  folded *looked* untouched, which is a question about the reader: one snapshot
  by anybody still in the realm then replaced the whole screen, and since a
  snapshot can name its author an admin, every checkpoint they published
  afterwards was trusted too.
- **A hole is not something to fold around.** If any part of this realm between
  where the fold started and the head will not open — a generation this browser
  holds no key for, a ciphertext the sequencer withheld, a payload that does not
  decrypt — the client refuses to display the realm and says so: *cannot verify:
  no checkpoint covers the parts you cannot read*. The way out is a checkpoint
  whose author it trusts, at a position past the gap, or the keys for the
  generations it is missing. It is not a best effort.

  `unverified` is the word for that state, and it is the node's: `GET realms` and
  `resources sync status` mark a realm whose projection folds around a hole
  exactly that way, because no checkpoint can be published for it and nobody
  else's can be checked against it. A node still shows such a realm under the
  mark; this client shows nothing of it, which is the stronger half of the same
  rule.

  The genesis question is asked of the **envelope**, never of what opened: how
  many parts an entry carries is a fact every reader sees, while which of them
  decrypt is a fact about one key ring. A reader that asked the second question
  would adopt a snapshot that an honest reader of the same order applies as an
  ordinary event, the two would hold different states, and checkpoint comparison
  would have them accusing each other of it. So at position 1: one part and it
  opens to a snapshot, that is the beginning; one part this browser cannot open,
  the fold begins from nothing and the hole is recorded; more than one part, an
  ordinary event whatever opened of it.

## Where the keys come from

**The session.** The origin a client signs is the one the sequencer reports
about *itself* (`GET health`), not the one inside the challenge it was handed: a
relay controls the second. A signature over a nonce that named no sequencer was
valid at every sequencer.

That is only half of it, and the server can only do that half. A relay at
`evil.example` can report the real sequencer's origin from every route it
serves, fetch a challenge from the real one, hand it over as its own and pass
the answer back — what it cannot do is be the host this browser dialled. So all
three statements of the origin (on `health`, on the challenge, and on the reply
that hands out the token) are compared against `new URL(base, location.href)`
as well as against each other. An empty origin is configuration rather than
protocol: a sequencer that has not been told its own public name binds nothing,
and both ends then agree on nothing, which is the same agreement.

**The realm key.** `crypto_box_seal` is anonymous — it needs only the
recipient's public key, which the sequencer stores — so a server could seal a
key of its own choosing to this member and hand it over. Three things stop that:

- a grant carries `grantedBy` and that member's signature over
  `seg("resources/grant/v1") ++ seg(ledger) ++ seg(realm) ++ seg(generation) ++
  seg(member) ++ seg(role) ++ seg(wrappedKey)` (the wrapped key as its raw
  bytes, because base64 is not canonical), and a grant whose signature does not
  verify is never used to decrypt anything;
- the issuer has to be somebody this client trusts: itself, an admin of the
  realm in the state it replayed, or — only until that state records an admin at
  all — the pinned inviter. A valid signature by a stranger is still a stranger,
  and the page stays empty;
- the SHA-256 of the realm key is pinned at the generation the invite named, so
  a *second* key at that same generation is refused. A newer generation is a
  revoke, and is allowed;
- **the generation has to be the realm's own.** After the replay, the grant's
  generation is compared with `state.realms[realm].generation`, and a state that
  is ahead is a refusal. A sequencer could otherwise serve an *older* grant —
  validly signed when it was issued — and everything written since the rotation
  would decrypt to nothing and be filed as unreadable, while the status line
  still read "verified and applied up to seq 900 of 900": a ledger frozen at the
  rotation, with a revoked member still in it.

**The pin is a bootstrap, not a root.** The inviter's key is the one thing a
newcomer has any reason to trust before they have replayed a single entry, and
that is all it is for. It used to be honoured unconditionally, with no expiry
and no way to unpin, so an admin who was later demoted or revoked was still
trusted by every browser they ever invited — for grants and for checkpoints
alike, and a checkpoint is an arbitrary `State`, including one that names them an
admin. Once the replayed state records an admin set for the realm, that set is
the whole of the answer; if the pinned key is not in it, the client says so on
the screen and stops trusting it. The pin is shown in the status line so it can
be compared out of band.

`self` is not one of those admins. It is the member a ledger belongs to before
there is a key to sign with, it sits in `State.init` from the start and it
cannot have signed anything — so a realm whose only admin is `self` is one this
browser has not read yet, and the pin is still what it has. `realmAdmins` drops
it, which is the clause `Node/Session.lean`'s `trusts` spells
`m != Member.selfId`: a client that counted it would spend its bootstrap against
a state nobody wrote, and show an empty page.

**The agreement key.** `boxPk` used to be whatever the server said it was, so
whoever ran the server could substitute a key they held and be handed every
realm on the next rotation. A member record now carries the member's own
signature over `seg("resources/member/v1") ++ seg(ledger) ++ seg(member) ++
seg(keyGeneration) ++ seg(boxPk)`; this client publishes its own on every session
open (the one route that writes one refuses anybody else's), and verifies the
signature on any key before sealing anything to it — including its own, using the
generation the row states rather than assuming zero.

`keyGeneration` is what makes the claim replaceable. Without it a member who
published a second key — because the secret half of the first had leaked — left
the first `(boxPk, signature)` pair a perfectly valid self-attestation for ever,
and an untrusted sequencer could go on serving it: the next rotation would seal
the realm key to the compromised one. A key that replaces one is published at the
next generation, the sequencer refuses a lower one, and absent means zero, which
is what every key published before the field existed was signed under.

**And this browser refuses a lower one too.** The sequencer's refusal is the half
that has to be trusted, and every triple `(boxPk, signature, generation)` a
member ever published stays valid on its own terms — so an operator holding a
replaced key can serve the old row and a client with no memory will seal the
realm key to a public half whose secret has since gone. The highest generation
seen for each member is kept, per member, in the stored realm ref
(`RealmRef.keyGenerations`), written only after that member's own signature over
`memberBytes` at that generation has been checked, and never moved backwards. A
row below it is refused with *is serving a key that has been replaced*; a row at
or above it is taken and becomes the new mark. The same floor applies to this
member's own republished key, so a sequencer serving an old row cannot make this
browser publish at a generation it is bound to refuse.

## The invite link

```
https://…/join/#base64url(ledger ':' realm ':' hex(secret) ':' inviterSignPk ':' keyHash ':' genesisHash)
```

Six fields, and `Node/Sync.lean`'s `Invitation.fragment` writes exactly these.
`keyHash` is the first sixteen bytes of the SHA-256 of the realm key, hex.
`inviterSignPk` is the member id of the admin who made it. `genesisHash` is
`genesisFingerprint` of entry 1 of the order — the first sixteen bytes of the
SHA-256 of the UTF-8 of that envelope's hash *string*, a digest of a digest,
because what is being fingerprinted is a value every reader that has taken the
entry in already holds as text — or the literal `none` when there was no entry
to name.

The secret rides as hex rather than as raw bytes, which is what makes the whole
fragment text a colon can be split on: version 1 put the raw secret last
precisely to dodge that question, and there are four fields after it now. So the
parse is `readInvite?`'s — the ledger is the first field, the last four are the
last four, and the realm is everything between them joined again, so a realm id
containing a colon survives the round trip.

What the joiner does with it, in order:

- clears the fragment from the address bar **first**, before the parse that
  might throw. It carries the secret that opens the realm key, and until it is
  gone it is in screenshots, in a shared screen, in the profile's history
  database and in browser sync;
- checks that the inviter the server names is the inviter the link names, and
  pins that key;
- checks that the key it unsealed is the key `keyHash` names;
- publishes its own `boxPk`, re-seals the realm key to it, and signs the grant
  that carries it;
- **checks that this sequencer is serving the order the link meant.** Entry 1 is
  fetched, its hash recomputed here, fingerprinted, and compared with
  `genesisHash`; a mismatch refuses the join before the browser's own store is
  written, and `none` has to meet a sequencer still serving an empty order. This
  is the door the positional-genesis rule left open: a genesis is accepted by the
  fold on its author's signature alone, and that proves only that *some* member
  wrote it — so a member of the realm plus any sequencer willing to serve their
  chain could otherwise decide the whole of a joiner's initial state, including
  who it says administers the realm, which makes the takeover self-sustaining.
  The inviter knows what their order begins with and the fragment never reaches a
  server, so this compares a number the inviter knew against a number the
  sequencer cannot choose.

The digest is then kept in the realm ref and carried on the session, and every
fold that starts from nothing checks it against the entry served at position 1
before that entry is anything — so the refusal costs no request of its own. A
fold that starts from a checkpoint never sees position 1 and so never asks, which
is the answer `linksToGenesis` gives on a node whose store begins at one: what
that fold rests on is the checkpoint's own chain of trust.

**A link that said `none` is backfilled.** There was no entry to name when such
a link was written, so there is nothing to check the order against — and without
a backfill there never would be: the browser re-derives its whole state from an
unchecked entry 1 on every cold open, for ever, while a genesis is accepted by
the fold on its author's signature alone. So the first fold that starts from
nothing and reaches position 1 writes that entry's fingerprint into the stored
ref and onto the session in hand, and every later fold is checked against it.
Trust on first use, and the same backfill `Node/Sync.lean`'s `noteProgress`
makes on a node; it is written once and never moved, and the window it leaves is
the one fold between joining on such a link and seeing an entry 1.

**A second invite asks first.** Accepting one on a browser that already holds an
identity makes a new key pair and writes it over the old one — and the grants on
the old realm are sealed to a public key whose secret half is then gone. There
is no export and no way back, so it takes a deliberate confirmation, and the
"nothing to show yet" screen has a button that forgets stored keys on purpose.

## What it agrees with Lean about

- **223 conformance vectors**, at format version 8. `src/conformance.test.ts`
  reads `conformance/vectors.json` — emitted by `resources gen-vectors` from the
  Lean core's own `step` — and for every vector decodes `stateHex` and
  `eventHex`, re-encodes them to check the codec both ways, applies `step`, and
  insists the result encodes to exactly `expectedHex`, hashes to
  `expectedHash`, refuses exactly the parts `rejected` names, and returns the
  same changes in the same order. The bytes are the contract.
- **17 conformance rejections**, which are the other half and are what make the
  format a *name* rather than merely a shape. `conformance/rejects.json` gives a
  byte string and the decoder that has to refuse it — `nat`, `int`, `string`,
  `date`, `state` or `event` — and the same test file runs every one of them
  through this port's own `decode`. Every vector above is well-formed, so a port
  could reproduce all 223 while accepting bytes no writer produces; and a
  checkpoint is the hash of a state's canonical encoding, so a reader that takes
  a second spelling of one state re-encodes it to something the sender never
  committed to, and two honest peers then disagree about whether a checkpoint
  verifies.
- **A realm on every entity.** At format version 5 the last eight kinds that had
  none gained one: `Label`, `Party`, `PartyGroup`, `Trip`, `Rule`, `ImportBatch`
  and `BlobState` each carry a trailing `realm`, and the invoice counter is keyed
  `<realm>:invoice:<year>`. A part may only speak about an entry of the realm it
  names; a new entry is created in that realm; and `deleteLabel` rewrites only
  transactions with a leg here, refusing outright rather than stranding a label
  id on one that has none. Two exceptions, both stated as rules: a member may
  revise the party record their own spending lands on from any realm they are in,
  and the record keeps the realm it was introduced in; and a `registerBlob` that
  re-seals a known file moves the record into the realm the part names, because a
  receipt filed in one realm and attached to a payment in another has to be
  readable by the people who can read that payment.
- **An invoice's realm, and the last four lookups that went by name.** Format
  version 6 finishes the list with the one kind it missed: `InvoiceState` carries
  a trailing `realm`, written after the outlays the invoice bills for.
  `issueInvoice` records the part's realm; `setInvoiceStatus`, `settleInvoice`
  and `deleteInvoice` refuse an invoice belonging to any other; and the counter a
  delete winds back is keyed on the *invoice's* realm, so a number is only ever
  given back by the realm that handed it out. The per-realm counter made the
  missing field worse rather than better: a draft issued in one realm and deleted
  from another wound back a sequence that had never issued it, so the issuing
  realm kept the burnt number and the next invoice in the other realm duplicated
  one already sent — and the same door marked any invoice in the ledger `paid` or
  `void`.

  The same version scopes the four lookups that still went by name and
  *selected* rather than refused. An invoice's payer is the party of that name in
  the part's realm, and a payer nobody knows is created there — otherwise a member
  whose party id sorted low renamed their own party to a customer's name through
  `putParty`'s self door and every invoice afterwards issued to that name was
  addressed to them, `payerId`, reference, receivable and all. A grant's bridge is
  the account of that name in the realm being granted. The label a budget pins is
  one of that name in the budget's realm, since that label is what the budget's
  claims are read out of. And the account a person settles a budget through is
  looked for among their accounts in the budget's realm, which also means
  `settlementAccount` now says *no such budget* rather than reading one that is
  not there. A name is something anybody who may write an entry can take, so a
  lookup by name across every realm is a lookup an outsider chooses the answer
  to; the unscoped `accountByName` is gone from this port entirely.
- **What a transaction paid for.** Format version 7 gives `Transaction` a
  trailing `items`, an optional list of priced lines written after its
  attachments. `null` is a payment nobody has divided: whatever its receipt says,
  it paid for all of it. Dividing one by the lines on its receipt hands each part
  the lines it claimed and the remainder the units they left, so the two are
  never the same money twice — and a part is divided again by its own list rather
  than by the page, whose lines its siblings have already spent. An empty list is
  therefore a real answer, said by a remainder whose siblings claimed every
  printed line and which keeps only a service charge no line covers. The receipt
  is untouched by all of it: what it says is a fact about the paper.
- **The costs people say were theirs.** Format version 8 gives `BudgetState` a
  trailing `claims` list and adds `claimCost` and `releaseCost`, and it gives
  `LineItem` a leading `id` so that anything pointing at a receipt's line points
  at the line rather than at its position. A claim is not money and moves none:
  it is one person saying that one cost of a budget was theirs to bear. What it
  is for is the division — a cost somebody took is borne by whoever took it,
  split equally when several did, and only what nobody took is divided among
  everybody by weight, which is what a budget did before anybody could take
  anything. Both are a member's right and are checked against the claimant
  themselves: a guest takes costs for nobody but themselves and gives back only
  their own, while an admin of the budget's realm can free anybody's, because
  somebody has to be able to correct a list the people in it filled in
  themselves. The budget is what the people with links are let into; the costs
  are in it because they were re-entered there through a purse, since an account
  stays in the realm it was written in.
- **Every authorisation rule.** `Op.rights` is a total table here as it is in
  `Core/Event.lean`, consulted once at the top of `applyOp` before any state is
  read for effect; `checkBounds` runs next; and what a rule cannot decide is
  decided by the case that knows about it — `checkOwnLegs` leg by leg,
  `putGuard` on a rewrite, `checkClaimParty` for a claim, `checkReceipt` for a
  receipt. `snapshot` is refused everywhere, because where a log starts is a
  position rather than a permission. `payClaim` is the receiver's or an admin's
  and never the payer's; `resolveClaim` passes the claim's own two accounts as
  `allowed`, so the receiver can meet it without post rights on the debtor's
  purse. `putTransaction` refuses an id whose stored transaction is not
  `.posted`. A self-`grant` makes exactly one purse, called
  `Members.<member name>`, of the one kind money is held in, with nobody else on
  it and mirroring nothing, and refuses a name or an id already spoken for in
  that realm. `openBudget` adopts an account of the pot's name only if it is in
  this realm, is equity, is nobody's bridge and names no posters of its own. The
  budget clause of `canPostLeg` is keyed on the budget's own account id and only
  allows money *into* the pot.
- **Every bound.** Postings ≤ 200, participants ≤ 100, receipt lines ≤ 500,
  `|qty|` ≤ 100000, weights in [1, 10000], ids and names ≤ 200 characters,
  narrations ≤ 2000, divisions ≤ 100000 parts — and `maxPostings` again on what
  an intent *computed*, in `putTxn`, because `checkBounds` bounds only what an
  author sent and a split across a hundred thousand targets is far larger than
  anything anybody sent.
- **The three numbers with no type over them.** A `Date`'s year in
  [−999999, 999999], a `Commodity`'s exponent ≤ 18, and an `Amount`'s count of
  minor units below 2^63 — the last of which is a decoder's question only, exactly
  as `boundedAmount` in `Core/Apply.lean` asks only about the commodity.
- **A strict decoder.** Overlong LEB128, integer negative zero, an overlong
  length prefix, map entries not strictly ascending by key, a key that differs
  from the entity's own id, and trailing bytes are all refused. That is
  `CanonicalCodec` in `Core/Codec.lean`, which is proved there and can only be
  tested here.
- **A `wellformed` walk, and the `Op` exception.** `decode` reads the whole byte
  string and then asks whether the value is one this format carries — the year,
  the exponent and the count of minor units, everywhere a value is read for
  itself: a `Date`, a `Commodity`, an `Amount`, anything holding one, and above
  all a `State`, which is what a checkpoint commits to. An `Op` is the exception
  and the exception is the important part: an operation is an *intent*, and an
  intent is refused by `checkBounds` when the part is applied. It has to be that
  way round, because an event is one author's set of parts and a part that cannot
  be applied is skipped rather than failing its neighbours — a reader that refused
  the bytes would throw away every other realm's part in the same event because of
  one it did not like, and which parts those are is chosen by whoever composed it.
  So an event carrying an absurd year decodes, and the part carrying it is then
  refused; `refuses-a-year-out-of-range` is the vector that says so. A `snapshot`
  is the one operation whose payload *is* checked, because it carries a whole
  state and nothing checks a state before it is believed.

One place where this client is deliberately **stricter** than the Lean core, and
it is about `number` rather than about the format: a `Date` whose year is outside
±(2^53 − 1) is refused while the bytes are read rather than when the part is
applied. Every year the format carries is six digits, so this is four hundred
million times wider than anything a conforming writer produces; but it is a
refusal of the bytes, which costs the other parts of the same event, and that is
the shape this file argues against everywhere else. It exists because `Number`
loses precision above 2^53 and becomes `Infinity` near 1e309, and a date that is
`Infinity` in a browser and exact in Lean is a state the two would order, render
and hash differently.

## What it still does not verify

- **Anything about other realms.** The client holds one realm key. Parts for
  other realms are counted, their digests are checked, and their contents are
  nobody's business here. A part of *this* realm that will not open is a
  different matter: it is a gap, and a gap stops the realm being displayed at
  all.
- **That the sequencer is showing it everything.** A gap in the order is caught,
  and so is a rewritten past — but a sequencer that simply stops serving new
  entries looks exactly like a quiet week. The head it reports is compared with
  what was verified, and the difference is on the screen; that is the whole of
  the defence.
- **Re-wrapping a receipt under another realm's key.** That is a node's job. A
  receipt whose `wrappedKey` names another realm is a sentence saying which key
  would have been needed, never a silent failure to decrypt.

## Content Security Policy, and no third parties

`index.html` carries the policy, repeated so that a page opened from a file,
from `vite preview`, or from anything else that does not send the header is
covered too:

```
default-src 'self'; script-src 'self' 'wasm-unsafe-eval'; connect-src 'self';
img-src 'self' blob: data:; style-src 'self' 'unsafe-inline'; frame-ancestors 'none';
base-uri 'none'; object-src 'none'; form-action 'self'
```

The last three do **not** fall back to `default-src`, which is why they are
spelled out: without `base-uri 'none'` a single injected `<base>` retargets every
relative URL on the page, including the one this client fetches the sequencer
through; a plugin and a form action are the other two ways out of a policy that
only names scripts.

The two servers' `securityHeaders` (`Resources/Sync/Server.lean`,
`Resources/Api/Server.lean`) still send the policy without those three, so the
two spellings differ until they are changed in the same words. The header is what
enforces the policy for a page the sequencer serves; the meta tag is what covers
every other way this file is opened, and it is the stricter of the two.

`frame-ancestors` has no effect in a `<meta>` policy and is kept so the two
spellings stay diffable; the header is what enforces it. `<meta name="referrer"
content="no-referrer">` matches the header too.

There is no `font-src`, because there is nothing to fetch: the font stack is the
system's. A stylesheet from a third party told that party, on every load, that a
client holding a realm key had been opened — and a hostile response from it
could restyle or hide the line that says how far the page has verified.

**Receipts.** `Attachment.mime` is a string whoever registered the blob chose,
and it passes every hash check in `blobs.ts` — those are about integrity, not
about type. A `blob:` URL inherits this page's origin, and "open link in a new
tab" navigates to it. So the type handed to `new Blob` is never the ledger's
own: `image/png`, `image/jpeg`, `image/gif` and `image/webp` are rendered
inline, and everything else — `image/svg+xml` included, because the same URL
opened in a tab is a document — becomes `application/octet-stream` and is
offered as a download. `origName` is stripped of path separators and control
characters before it reaches a `download` attribute.

## Where the identity lives

On first use the client makes an Ed25519 pair (its `MemberId` is the lowercase
hex of the public key) and an X25519 pair, and stores them one of two ways:

- **with a passphrase**, in `localStorage`, in the same file shape the node
  writes `identity.json` in (`Resources/Node/Identity.lean`), so the same
  passphrase opens the same identity in either:

  ```json
  { "v": 1, "id": "<hex signPk>", "signPk": "<hex>", "boxPk": "<hex>",
    "kdf": { "alg": "argon2id", "ops": 3, "mem": 268435456, "salt": "<base64>" },
    "nonce": "<base64>", "secret": "<base64>" }
  ```

  The plaintext inside `secret` is `signSk ++ boxSk`, sealed with
  XChaCha20-Poly1305 under an Argon2id key, with the additional data
  `seg("resources/identity/v1") ++ seg(signPkHex)` — so a file's ciphertext
  cannot be lifted onto another file claiming another key. The limits are
  libsodium's **MODERATE**, not INTERACTIVE: what is being protected outlives
  the tab and travels in profile backups, and the cost is paid twice in the life
  of a browser. The minimum passphrase is twelve characters.

  Nothing the record says about itself is taken on its word. The id has to be
  the hex of the signing key it is filed under, `alg` has to be `argon2id`, and
  `ops` and `mem` have to be limits this client is willing to run — a tampered
  record naming a gigabyte of memory would otherwise turn unlocking into a
  crash.

- **without one**, in `sessionStorage`, in the clear. This is the weaker option,
  offered because a guest invited to one weekend is not going to invent a
  passphrase for it. Anything that can read the page can read the keys. Worth
  knowing: `sessionStorage` survives "reopen closed tab" and is written to disk
  by session restore, so "gone when the tab closes" is optimistic.

## The WASM note

The design document said "no WASM" about Lean, not about the primitives.
Re-implementing XChaCha20-Poly1305 or Ed25519 in JavaScript is exactly what
"neither the primitives nor the protocol are reimplemented" forbids, so the
cryptography here is libsodium compiled to WebAssembly, and the bundle carries
it. That is the deliberate deviation, and it is the only one: the protocol —
what is framed, what is signed, what is hashed — is implemented in TypeScript
from the Lean sources, and only the primitives are somebody else's code.

Two consequences worth knowing about.

*The package is `libsodium-wrappers-sumo`, not `libsodium-wrappers`.* The
standard build does not export `crypto_pwhash` or `crypto_hash_sha256`, and the
spec needs both: Argon2id for the identity at rest, SHA-256 for the chain
hashes, the state hash and every `cipherHash`. The sumo build is the same
library with the full symbol set, and it is bigger — the production bundle is
about 1.25 MB, roughly 400 KB gzipped, most of it the WASM.

*The ESM entry point of that package is broken* — it imports a sibling file that
ships in a different package — so `vite.config.ts` aliases it to the CommonJS
entry by path inside `node_modules`, which works in both Vite and Vitest and
would need revisiting if the package were ever hoisted differently.

## The files

| | |
| --- | --- |
| `src/types.ts` | every type of `Core`, hand-written from the Lean sources; declaration order is the wire format, and the bounds |
| `src/bytes.ts` | hex, base64, the `seg` framing, Lean's string order and a stable merge sort |
| `src/codec.ts` | the canonical encoding, and a decoder that refuses every other spelling |
| `src/money.ts` | `Amount`, `splitParts`, `biproportional`, `shareOut` |
| `src/settle.ts` | `Settle.greedy`, `star`, `validate` |
| `src/ledger.ts` | postings, balance, `validate`, reading a claim |
| `src/state.ts` | `State`, sorted iteration, `canPostLeg`, `accountByNameIn`, `realmAdmins` |
| `src/budgets.ts` | `costs`, `remaining`, `standings`, `claims`, `divisionOf`, `settlementOf` — all by id |
| `src/apply.ts` | `Op.rights`, `checkBounds`, `applyOp`, `step`, `stepAt` and `replay`, for every operation there is |
| `src/blobs.ts` | fetching a receipt's ciphertext and opening it |
| `src/crypto.ts` | identities at rest, part sealing, the v2 byte strings, grants, key wrapping, invites |
| `src/sequencer.ts` | the `/seq/v2` client, and nothing that decides what to believe |
| `src/sync.ts` | where an order begins, choosing a checkpoint, verifying the tail, compose-and-submit, the joiner's introduction |
| `src/store.ts` | where the identity lives, what the invite pinned, the entry the order begins with, and the key generations seen |
| `src/App.tsx` | opening a session, the join flow, the realm view and the receipt a cost carries |
| `src/conformance.test.ts` | the 223 vectors and the 17 rejections, run against the codecs and `step` |
| `src/codec.test.ts` | the byte strings of `Test/Encode.lean`, and every spelling the decoder refuses |
| `src/crypto.test.ts` | the byte strings of `Test/Sync.lean`, and the identity file's shape |
| `src/sync.test.ts` | what stops the fold, what it writes down about where the order begins, and which checkpoints are worth anything |
| `src/join.test.ts` | the invite fragment, and what a receipt is allowed to be |
| `src/sequencer.test.ts` | the origin this client dialled, and a member row's key generation |
