# Keeping later proof paths open — design note, 2026-10-06

Status: **proposed** [AGENT], for the user's decisions in section 5.

[USER 2026-10-06] "This isn't work we will do, it's identifying cheap moves we
can make to keep these paths open for later agents or avoid blocking them."
`AGENTS.md` forbids theorems and proof infrastructure; nothing here builds
any. The note (a) says what could reasonably be stated about WireGuard at the
mirror interface later, and (b) names cheap moves, mostly conventions, that
keep those paths open, with the practices that would close them. Evidence is
`main` (eb705b2) and the branches `task/d3-int`, `task/l-m`, `task/a1`,
`task/e-b`; C lines are 6.12.110 in `.deps/linux`.

## 1. The chain, corrected

The coordinator's framing: protocol security (the Tamarin model of Donenfeld
and Milner; the CryptoVerif proof of Lipp, Blanchet and Bhargavan; Dowling
and Paterson's analysis) → refinement (the mirror is an honest Noise IK party
of that model per random tape) → implementation (Linux ≈ mirror: differential
testing now, a separation-logic simulation later). The mirror is the bridge.
Four corrections, each of which changes what a later agent must write:

1. **"Exactly a party of the model" is too strong.** The C, and so the
   mirror, carries policy the protocol models abstract or omit: the TAI64N
   timestamp rounded to 2^24 ns (`Handshake.lean` `tai64n`), the flood and
   rate limits, sender/receiver indices and their hashtable, MAC1/MAC2 and
   cookies, the current/previous/next keypair rotation, `REJECT_AFTER_*`,
   the RFC 6479 window. The refinement is "the mirror's five handshake
   functions implement the model's party *up to a listed abstraction gap*";
   section 3(f) is where the list lives.
2. **The hidden-input stream is more than the random tape.** Its `kind`
   field (`Kernel/Defs.lean` `HiddenSiteInfo.kind`) already separates
   `random` (the party's coins: `.initEphemeral`, `.respEphemeral`,
   `.indexDraw`; E-B's `.cookieNonce`), `clock` (policy inputs the models
   either lack or give the adversary), and `section`/`resched` (A adds
   `alloc`): scheduling and environment, which belong to the adversary's
   control of delivery and interleaving, not to the party. A statement must
   quantify over the clock and scheduling kinds and treat only `random` as
   the tape.
3. **The trace interface is two channels, not one adversary.** `wg_inject`
   and `wg_observe` are the network adversary (injects; sees every datagram
   wg0 sends, including replies and inner packets). `wg_set`, `wg_get`,
   `wg_up`, `wg_xmit` are the honest user's channel: they install keys and
   hand over plaintext, and `wg_get` dumps the PSK and private key
   (`Netlink.lean:348`, as the C does). A refinement must split the
   operations by channel; giving the adversary `wg_get` makes every secrecy
   statement false.
4. **One party.** The mirror is wg0. The other honest party of the model is
   `harness/noise.py`, which is unverified and need not be trusted: for
   claims about wg0 it is part of the adversary. For a two-honest-party
   claim a second mirror instance is needed, which the state shape allows
   (`Kernel.wg` is one device; nothing else is global except the two
   counters) but the runner does not.

## 2. What could be stated at the mirror interface

Three kinds: **R** (refinement to the protocol model), **I** (an invariant of
mirror runs, decidable on recorded traces, so testable now as an instrument
if it pays and provable later), **S** (the Linux ≈ mirror simulation, later).

| # | Statement | Kind | Mirror anchor (`Leanux/WG/`) | Needs |
|---|---|---|---|---|
| 1 | `createInitiation`, `consumeInitiation`, `createResponse`, `consumeResponse`, `beginSession` are the Noise IKpsk2 party's steps as functions of the handshake state and the `random` records, up to the gap list | R | `Handshake.lean`; evidence today: every initiation and response byte-equal to Linux and to `noise.py` (hidden-inputs design, sections 8–9) | 3(b), 3(f) |
| 2 | Inbound cryptokey routing: every inner packet delivered was decrypted under a keypair `k` with `k.peer = allowedips.lookup(src)` | I | `RxData.lean` `consumeDataDone`, `doneDishonestPeer` (receive.c:408) | provenance at the delivery cut, 3(c) |
| 3 | Outbound: every data message in `World.sent` was encrypted under `k` with `k.peer = lookupDst(dst)` of its plaintext, to `k.peer`'s endpoint | I | `Device.lean:77` `wgXmit`; `Send.lean` `sendStagedPackets` (`keypairCurrent` of that peer), `enqueuePerPeerTx` (checks `k.peer`); `Data.lean` `sendSkbToPeer` | — |
| 4 | No data replay: per keypair no counter is accepted twice | I | `RxData.lean` `counterValidate` (receive.c:295-331) | — |
| 5 | Nonce uniqueness: per keypair the sent `(k, nonce)` are distinct and below `REJECT_AFTER_MESSAGES` | I | `Send.lean` `stagedNonceIterate`/`stagedNonceRejected` | — |
| 6 | Key lifetime: no send or accept under a key with `birthdate + 180 s ≤` the recorded clock at that check | I | `Send.lean` `stagedBirthdateExpired`; `RxData.lean` `decKeyExpired` | D3 for the fired arms |
| 7 | Initiation replay and flood: consumption needs a strictly newer TAI64N and ≥ 20 ms since the last | I | `Handshake.lean` `consumeReplay`, `consumeFlood` | — |
| 8 | Rate limit and give-up: ≥ `REKEY_TIMEOUT` between a peer's initiations; after `MAX_TIMER_HANDSHAKES` the staged queue is purged and the zero-key timer armed | I | `Handshake.lean` `initRateLimited`, `Send.lean` `queuedNotExpired`; d3-int `Timers.lean` `expiredRetransmitHandshake` | D3 |
| 9 | Reference and index safety: no run reaches `Stop.invariant`; every index entry, slot and queued packet names a live object | I | already a check outcome (`mirror_invariant`, exit 4) for the dereferenced cases; the eager form is 3(g) | 3(g) |
| 10 | Erasure: after `beginSession`, `handshakeClear` and the clear work, the handshake secrets are zero; after the last put a keypair is absent; every stored keypair is reachable | I | `Peer.lean` `handshakeZero`; `Keypair.lean` `keypairPut`, d3-int `queuedExpiredZeroKeyMaterial` | 3(a), 3(g) |

None of these is to be proved now. 2–10 are the kind of predicate that the
"checks must pay" rule admits only with a defect or mutant each rejects.

## 3. Cheap moves, assessed

### (a) Secrets as first-class state, with faithful erasure

**Audit** of every zeroing or free of key material in the C against the
mirror (`memzero_explicit`, `memset`, `kfree_sensitive`, `handshake_zero`,
the zero-key timer):

| C site | Mirror | Status |
|---|---|---|
| `handshake_zero` noise.c:78-86 (ephemeral, remote ephemeral, hash, chaining key, index, state), from :94 `wg_noise_handshake_clear` and :841 `begin_session` | `Peer.lean` `handshakeZero`, from `Keypair.lean` `expireCurrentPeerKeypairs` (d3-int `handshakeClear`) and `Handshake.lean` `beginSession` after `deriveKeys` | matched, in place |
| `keypair_free_kref`/`_rcu` noise.c:117-129, :112-115: unhash, `call_rcu`, `kfree_sensitive` | `Keypair.lean` `keypairPut`: entry removed, store entry erased at the last put | matched; the RCU grace period is abstracted (the C zeroes later, when nothing can reach the object) |
| `kfree_sensitive(new_keypair)` noise.c:854 (dead peer) | `beginSession`: `unsupported` | out of domain, fail-noisy |
| precomputed static-static zeroed noise.c:54-55 | `Peer.lean` `precomputeStaticStatic` | matched |
| private key set noise.c:294-303 (memcpy, clamp; public unwritten on failure) | `Peer.lean` `setStaticIdentityPrivateKey` | matched |
| `memzero_explicit(peer)` peer.c:196 after `kref_release` :200-221 (PSK, precomputed key, cookie keys go with it) | `Peer.lean` `peerPut`: the peer leaves the store | matched, same RCU abstraction |
| `memzero_explicit(&wg->static_identity)` device.c:263, `wg_destruct` | l-m `Device.lean:250-269`: `wg := none` | matched on l-m; outside the window on main |
| cookie keys zeroed without identity cookie.c:55-57 | `Peer.lean` `cookiePrecomputeDeviceKeys` (e-b adds `cookieEncryptionKey`) | matched |
| zero-key timer → clear work timers.c:105-133 (`handshake_clear`, `keypairs_clear`) | d3-int `Keypair.lean:132-137` `queuedExpiredZeroKeyMaterial` | matched on d3-int; a cut on main (no timer fires) |
| `memzero_explicit(nla_data(...))` netlink.c:488, :605 | `Netlink.lean:145` `.peerZeroPsk`, `:208` `.setDevZeroKey`: the decision only | below the altitude: the attribute is a trace input, there is no buffer; a C-memory fact for the simulation proof |
| stack temporaries noise.c:336-337, 388-389, 415, 451, 579, 658-660, 723, 806-811 | Lean `let` values, no store | below the altitude: "locals dead at return" is discharged on the C side |

Two facts a statement must respect, both faithfully mirrored: expiry
(noise.c:179-196) only clears `is_valid`, the bytes stay until the clear work
or the last put; and an initiation that fails after its draw (noise.c:541
then `goto out`) leaves the ephemeral in place until the next zeroing.

Cost: none beyond this table. Unblocks: statement 10. No `AGENTS.md`
conflict. **[AGENT] Adopt as a convention:** every new secret-bearing field
names its C zeroing or freeing site in its doc comment, and that zeroing is
mirrored in the same function as the C's (in-place zero or store erasure);
the RCU-deferral abstraction is stated once, here.

### (b) Crypto behind a narrow named interface

Status: already true. The primitives are three files and nine names:
`Curve25519.lean` (`curve25519`, `clamp`, `basePoint`, `nullPoint`),
`Blake2s.lean` (`blake2s`), `NoiseCrypto.lean` (`aeadEncrypt`,
`aeadDecrypt`, `hmacBlake2s`, `kdfOutputs`, `noiseHash`; e-b adds
`xchachaEncrypt`/`xchachaDecrypt`). Call sites outside those files: 18 in
`Handshake.lean`, 5 in `Peer.lean`, 1 each in `Receive.lean`, `Data.lean`,
`RxData.lean`; no arithmetic inlined. `kdf` (`Handshake.lean:45-52`) is the
one noise.c helper mirrored with its own decisions, correctly. Vectors from
RFC 8439 and `noise.py` are `#guard`ed at build.

Cost: none. Unblocks: statement 1 (a refinement swaps these names for the
model's abstract functions). **[AGENT] Adopt as a convention:** no primitive
outside these three files; the pure functions are cut points with contracts.

### (c) A semantic event log

The events (delivered-from-peer, encrypted-with-keypair-nonce,
handshake-sent-at-time, key derived/promoted/erased) each have **one** mirror
point already: `Env.deliverInner` via `rxPoll`, `Data.lean` `dataMessage`,
`Handshake.lean` `sendBufferToPeer`, `deriveKeys`, `addNewKeypair`/
`receivedWithKeypair`, `keypairPut`/`handshakeZero`. What is missing is
provenance across the cuts: `deliverInner` receives bytes only, and
`SentDatagram` carries no keypair id, so statements 2 and 3 cannot be read
off a run today.

The tension: `AGENTS.md` keeps the mirror to the C's data and control flow.
But `World` (not `Kernel`) already holds non-C bookkeeping: `steps`,
`envCalls`, `sent`, `hidden`. A ghost log in `World`, written at those six
points, is observation state like `steps`, and the A3 structural review can
treat a one-line `event` call as it treats `branch`.

Cost: ~30 lines; the provenance fields (`SentDatagram.keypair`, an
`InboxDatagram` origin) are the only mirror-adjacent change and are
environment records. Unblocks: 2, 3, 10 as instruments. **[AGENT]
Recommend:** defer the log; adopt now the convention that those six points
stay the unique mirror sites of their events (no inlined duplicates), and
add the two provenance fields when D2/D3 integration next touches them.
Whether a ghost `World.events` is acceptable is **user decision U1**.

### (d) Pure, total cores

Status: `M` is `StateT World (Except Stop)`, no `IO`. Every loop is
fuel-bounded and ends in `invariant`/`unsupported` (`indexInsert` 64,
`jitterBelowRekeyTimeout` 256, the workers' `MAX_QUEUED_*`, `condResched`'s
`SWITCH_DEPTH`). Exceptions: two `partial def`s (`Syscalls.lean:107`
`taskWorkRun`, `AllowedIps.lean:227` `subtree`), and 88 `!` sites, 31 in the
crypto references and the rest in `AllowedIps.lean` (10, `bit[..]!`),
`State.lean:62`, `Handshake.lean:59,67,73,213,325`, `Defs.lean:534`, plus
JSON and hex helpers in `Runner.lean`, `Netlink.lean:267`, `Env.lean:354`.
Runtime panics already fail the check (`evaluator/check.py:70,132`), so none
is fail-open today; they only obscure totality.

Cost: an hour for the audit items. Unblocks: unfolding any mirror function
later (`partial` is opaque). **[AGENT] Adopt as a convention:** no new
`partial` or `!` in `Leanux/WG`, `Leanux/Kernel`, `Leanux/Env.lean` (the
crypto references are exempt). **Audit items:** fuel the two `partial`s; a
bounds-checked `AipNode.bitAt` replacing the `bit[..]!` sites in
`AllowedIps.lean` and `State.lean:62`; see B1 for the `Handshake.lean` sites.

### (e) Protocol logic separable from plumbing

Status: good. One file per C file; the Noise party is five separate
functions; cuts are injected (`checksumHelp`, `needResched`,
`napiCompleteDone`); `grep` finds no `Env.`, port or address constant in
`Leanux/WG`. The one environment fact read from mirror code is
`World.timing` (`Handshake.lean:335,344,377`), which D3's mirrored timers
retire. Hidden reads sit where the C consumes them (noise.c:541, :501,
peerlookup.c:132), which is what the refinement needs: moving them out would
break the tape correspondence, not help it.

Cost: none. **[AGENT] Adopt as a convention:** mirror modules read the
environment only through parameters or the declared oracles (`envOk`,
`hidden`); D3's integration deletes `Timing` rather than keeping both.

### (f) Correspondence table to the protocol models

The C's field names are the whitepaper's, so the mirror maps directly. The
model-specific column (CryptoVerif/Tamarin variable names) is left for the
refinement author to fill against the model sources; nothing is invented
here.

| Mirror (`Types.lean`) | C | Whitepaper symbol |
|---|---|---|
| `Device.staticIdentity.staticPrivate/Public` | `static_identity.static_private/public` | S^priv, S^pub (wg0) |
| `Peer.remoteStatic`, `Peer.presharedKey` | `handshake.remote_static`, `preshared_key` | S^pub_peer, Q |
| `Peer.precomputedStaticStatic` | `precomputed_static_static` | DH(S^priv, S^pub_peer) |
| `Peer.ephemeralPrivate`, `Peer.remoteEphemeral` | `ephemeral_private`, `remote_ephemeral` | E^priv, E^pub_peer |
| `Peer.chainingKey`, `Peer.hash`, `Peer.handshakeState` | `chaining_key`, `hash`, `state` | C_i, H_i, the step |
| `Peer.remoteIndex`, `Device.indexTable` | `remote_index`, `index_hashtable` | I_i, I_r (often omitted by models) |
| `Peer.latestTimestamp`, `tai64n` | `latest_timestamp`, `tai64n_now` | the timestamp (rounding is C-specific) |
| `Keypair.sending/receiving.key` | `sending.key`, `receiving.key` | T^send, T^recv |
| `Keypair.sendingCounter`, `receivingCounter` | `sending_counter`, `receiving_counter` | N^send, N^recv (+ RFC 6479 window) |
| `Keypair.*.birthdate`, `isValid`, slots current/previous/next | same | no symbol: lifetime and rotation policy |
| `Device.mac1Key`, `Peer.cookieMac1Key`, e-b cookie keys and secret | cookie.c | mac1/mac2 keys, cookie secret |
| hidden `random`: `.initEphemeral`, `.respEphemeral`, `.indexDraw` | noise.c:541, :688, peerlookup.c:132 | the party's coins |
| hidden `clock`, `section`, `resched`, `alloc` | — | outside the model (section 1, item 2) |

`Peer` flattens `struct noise_handshake` and `struct cookie` into
`struct wg_peer`, and d3-int, l-m and e-b each add peer fields, so a split
gets dearer by the week. **[AGENT] Recommend** a pure projection
`Peer.handshake : Peer → NoiseHandshake` (ten lines) rather than a refactor;
it is the mirror-side anchor of this table.

### (g) A decidable well-formedness predicate as a test-time assertion

Candidate clauses, all decidable on `Kernel`: (W1) every `IndexEntry.peer`
is in `peers`, and a keypair entry's `keypair` is in `keypairs` with the same
peer; (W2) every stored keypair has `refcount ≥ 1` and a live peer; (W3) a
peer's three slots are distinct and stored; (W4) `numPeers`, `peerList` and
`peerHashtable` agree at operation end; (W5) keys and hashes are 32 bytes,
`latestTimestamp` 12; (W6) `handshakeState = 0` implies the four handshake
secrets are zero (the erasure invariant).

"Checks must pay": the evidence exists. The one wrong state update the
hidden-inputs review found, a released peer's handshake index entry left
behind (peer.c:211; hidden-inputs design, section 9), was caught by review,
not by the check; W1 rejects it at the operation boundary. Cost: ~50 lines
plus a call at `Runner.executeTrace`'s operation end. **[AGENT] Recommend:**
reintroduce that defect as a mutant; adopt W1–W6 only if the predicate alone
rejects it (**user decision U2**).

## 4. Practices that would block later work

- **B1. Fail-open key defaults.** `outs.getD 1 []`, `outs.head!` on `kdf`
  outputs (`Handshake.lean:59,67,73,213`) default a missing key to `[]`,
  caught only by the panic rule. `kdf` returns exactly what was asked, so
  these are `invariant` cases. Minutes. [AGENT] audit item.
- **B2. `partial` and `!`** (3(d)): opaque or defaulting code in the mirror
  proper. Convention plus two audit items.
- **B3. Keys as `List UInt8`** with no length invariant: a wrong-length key
  is representable. W5 covers it cheaply; a `Vector UInt8 32` type is a
  larger change. [AGENT] defer; new code may use fixed-width types.
- **B4. Environment facts in mirror code:** only `World.timing` (3(e));
  D3 must remove it, not add a second clock.
- **B5. Known fail-open spots with owners:** `harnessEnv` says every
  allocation succeeds (`Runner.lean:345`) and `evaluator/protocol.py:116`
  absorbs `ENOMEM` as `environment_failure`: A retires both, and until then `begin_session`'s
  no-keypair arm (statement 10) is dead. `skipCut` consumes any number of cut
  records (a declared weakness, strategy section 5). Domain-mode placeholders
  are gated and non-authoritative.
- **B6. Classification of refcount saturation** as `unsupported`
  (`Refcount.lean`): a C use-after-free would read as "outside domain". The
  exit codes already separate `unsupported_path` (3) from `mirror_invariant`
  (4); a later statement 9 may want a distinct stop kind. Note only.
- **B7. The trace contract does not name channels** (section 1, item 3):
  `wg_get` beside `wg_inject` in one operation set. A one-paragraph note in
  `contracts/trace-v1.md` naming the honest-user and adversary channels
  costs nothing now and prevents a wrong statement later.
- **B8. Provenance lost at the cuts** (3(c)): `deliverInner` gets bytes,
  `SentDatagram` has no keypair. Two fields.
- **B9. Growing `Peer`** (3(f)): the projection, not a refactor.

Not blocking, and worth saying: secrets are never dropped silently (every
free is a store erasure in the C's function), hidden reads are at the C's
sites, and the crypto is already behind names.

## 5. Decisions for the user

- **U1.** May `World` carry a ghost event log written at the six named
  points (3(c)), on the precedent of `steps`? [AGENT] recommends deferring
  the log and adopting the uniqueness convention and the two provenance
  fields now.
- **U2.** Add the well-formedness predicate (3(g)) as a per-operation check,
  conditional on the peer.c:211 mutant being rejected by it alone?
- **U3.** Record the conventions of 3(a), (b), (d), (e) and B7: in this note
  only, or as a short "conventions" paragraph in `AGENTS.md`?
- **U4.** The audit items (B1, the two `partial`s, `AipNode.bitAt`, the
  `Peer.handshake` projection): fold into the next integration branch, or
  leave listed here?
