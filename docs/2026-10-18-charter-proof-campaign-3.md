# Charter: proof campaign 3, the high-consequence group

A long-cycle proof assignment for a Codex agent and its subagents, in the
form of [the first](2026-10-13-charter-proof-campaign.md) and
[the second](2026-10-14-charter-proof-campaign-2.md) campaign's charters:
five WireGuard results over the mirror that neither landed campaign nor
the one in flight covers, chosen for the security consequence of their
failure. It runs beside campaign 2 (Codex#2, `proofs/campaign-2`, the
handshake and configuration group) under the disjointness rule of
section 6.

Provenance: [USER 2026-10-18] the campaign is chartered for the properties
with high security consequences that the mirror's proofs do not yet
cover, everything a good WireGuard proof should cover at the sequential
model level; the lower-consequence items the parallel plan reserved for
this campaign are deferred (section 7). [AGENT, coordinator] wrote the
charter from the coverage table put to the user on 2026-10-18, which set
campaign 1's six results against the protocol's stated behaviour and
found the sending side, silence and handshake freshness uncovered.

## 1. What this is, and what it is not

Mirror to property, as before: properties of WireGuard proved over the
executable mirror's own definitions, with whatever Lean models sit in
between. Code to mirror is not this assignment; neither is the binary
track. Theorems live in the proof tree `Leanux/Proofs/` with its gate and
register ([AGENTS.md](../AGENTS.md), [docs/proofs.md](proofs.md)); proofs
are a validation channel for the models, so a Rule Zero finding is a
success of this campaign.

The mirror is sequential: one CPU, no preemption, the softirq and worker
placements from the records. Every statement below is a statement about
that model, and a result's security sentence names the consequence of the
property failing in the implementation the model mirrors; nothing here is
a claim about the C, about concurrency, or about the cryptographic
primitives, which are contracts.

## 2. Setup

- Repository `/home/dev/projects/lean-ux-proto`. Worktree
  `.worktrees/proofs-campaign-3`, branch `proofs/campaign-3` from `main`,
  created for you on Lean v4.35.0; work only there. Other agents work in
  other `.worktrees/*`; do not touch them, and do not touch `main`.
- Build through `capped -- scripts/in-bundle lake build LeanuxProofs`; the
  gate is `capped -- scripts/in-bundle scripts/proof-gate` (about sixteen
  minutes) and the speedbump beside it
  `capped -- scripts/in-bundle scripts/proof-counterexamples`. No
  differential checks, no guests: the mirror is checked against Linux
  elsewhere; here it is a definition. Use the box: full parallelism, every
  heavy job inside `capped`, a KILLED banner a failure.
- Add files only under `Leanux/Proofs/` and `docs/`. The mirror
  (`Leanux/WG`, `Leanux/Net`, `Leanux/FS`, `Leanux/Seccomp`,
  `Leanux/Kernel`, `Leanux/Env.lean`, `Leanux/Env`, `Leanux/Runner.lean`)
  stays byte-identical to `main` at every commit of yours. Each result is
  its own directory `Leanux/Proofs/WG/<Result>/` with a `Statements.lean`
  imported from `Leanux/Proofs.lean`, plus a row in the register; the
  register's "Adding a result" section is the procedure. Form is
  corrected, never stopped on.
- The mirror's state is a product of per-subsystem worlds
  ([the state split](2026-10-15-design-state-split.md)): WireGuard's
  functions run over `WG.M` on `WGWorld`, routing is a component inside
  it, and three further components (the skb stores, the index table, the
  allowed-IPs trie) have their own monads with one adapter each. Claims
  are stated over a projection of `WGWorld`; frames go in their own files
  and are deleted only when the type gives the fact.
- Read first: `AGENTS.md`; [docs/proofs.md](proofs.md) (campaign 1's
  landed layers and results, with the claim-carrying theorems named per
  result: R1's `runner_uniqueness` and `runner_floor`, R2's
  `runner_initialized_access_safety`, R3's three `parsed_initialized_*`
  theorems, R4's `accepted_runner_all_ingress_fates`, R5's thirteen local
  contracts, R6's two `original_invalid_mac2_*` theorems); the two earlier
  charters and campaign 1's report `docs/2026-10-13-proof-campaign.md`;
  campaign 2's report on its branch
  (`git show proofs/campaign-2:docs/2026-10-14-proof-campaign-2.md`,
  read-only) for what H1 to H6 already establish about the handshake, the
  index, roaming and the timers; the window-proof conventions and the
  reviews (`docs/2026-10-17-review-campaign-1-landing.md`,
  `docs/2026-10-13-review-r5-counterexamples.md`); the send and handshake
  correspondence audits (`docs/2026-10-15-audit-send.md`,
  `docs/2026-10-13-audit-handshake.md`), which walked the modules you will
  reason over line by line against the C; the landed designs the results
  rest on: the exact flood and rate limiter
  ([B4](2026-10-15-design-b4-load-ratelimiter.md)), the handshake ring
  ([B1](2026-10-15-design-b1-handshake-ring.md)), the timer wheel
  ([B3](2026-10-15-design-b3-timer-wheel.md)), the FIB trie
  ([C1](2026-10-15-design-c-fib-trie.md)), the transmit design
  ([W4+W7](2026-10-06-w4-w7-transmit-bulk.md)) and the DoS design
  ([E](2026-10-05-e-dos.md)); and the mirror modules each result names,
  with the C in `.deps/linux/drivers/net/wireguard/`.

## 3. Rule Zero, restated

Rule Zero, in three clauses [USER 2026-10-14]: (1) the mirror might be
wrong; (2) the kernel might contain bugs; (3) the former is much more
likely than the latter. Every discrepancy is read in that order: a mirror
defect first, settled by the differential check against the kernel and
fixed on the mirror lane; a kernel finding only with positive evidence
against the code's stated intent, written up in the tray after
independent review; a statement or relation is never bent to accommodate
either.

A statement below that is false of the mirror gets a concrete
counterexample (a trace and record stream the runner accepts, and the two
events or the divergence), a judgement whether the code's behaviour is a
bug against its intent or a design nuance, and then one of: the statement
proved under a named premise that excludes the trigger and cites the
finding, or the statement left unproved with the counterexample recorded.
The mirror is never edited by this campaign, and neither is the kernel.
Reshaping for a legitimate nuance is allowed and expected: prove the
property the code has, record both wordings and the reason, keep the
meaning. Campaign 1 refuted four literal wordings this way, all statement
artefacts on the C path; test that hypothesis first.

The stakes are higher here than in the earlier campaigns: each result
below names what a failure would mean. That is a reason for care in the
statement, not a reason to weaken it; if the mirror does not have the
property, the user wants to know exactly which trace shows it.

## 4. The campaign

Five results, in the recommended order. Names, statement forms,
intermediate models and refinements are yours. Every C line cited is in
`drivers/net/wireguard/` of the pinned source.

**T1. Sender nonce discipline.** Mirror: `Leanux/WG/Send.lean`
(`sendStagedPackets`, `createData`, the constants `REKEY_AFTER_MESSAGES`
and `REJECT_AFTER_MESSAGES` at `:55-57`), `Leanux/WG/Data.lean`
(`encryptPacket`, `createDataDone`, `keepKeyFresh`), `Leanux/WG/Keypair.lean`
(`keypairCreate`, `addNewKeypair`), `Leanux/WG/Types.lean` (`Keypair.sendingCounter`
at `:135`, documented as the next nonce). C: `send.c:379-382` (the nonce
is `atomic64_inc_return(&keypair->sending_counter) - 1`, assigned to every
packet of the staged batch in order, and a nonce at or past
`REJECT_AFTER_MESSAGES` sends the batch to `out_invalid`, `:391`);
`send.c:124-139` (`keep_key_fresh`: past `REKEY_AFTER_MESSAGES` or past
`REKEY_AFTER_TIME` for the initiator, a new handshake is queued);
`send.c:162-219` (`encrypt_packet` writes the nonce as the header counter,
`:208`, and uses it as the AEAD nonce, `:217`); `noise.c:98-110`
(`keypair_create` allocates zeroed, so the counter starts at 0);
`messages.h:41-42`. Claim: for every keypair, the nonces of the packets
encrypted under it, in the order the mirror encrypts them, are
`0, 1, 2, ...` with no value used twice and none at or above
`REJECT_AFTER_MESSAGES`; the first packet past the limit, and every packet
staged behind it in the same batch, is dropped at the `out_invalid` arm
with no encryption; once a keypair's counter is past
`REKEY_AFTER_MESSAGES`, the next completed send queues a handshake
initiation (`keep_key_fresh`), and no other site increments the counter.
Security consequence: a nonce reused under one key with ChaCha20-Poly1305
breaks confidentiality (keystream reuse) and integrity (forgeable tags)
for that key; a send past the limit is the same failure one step later.
A counterexample is two packets encrypted under one keypair with the same
nonce, a nonce used out of order, or an encryption with a nonce at or
above the limit. Not claimed: anything about the cipher itself, about the
receiving side's counter (R1), or about the wire bytes beyond the header's
counter field.

**T2. Transmit binding and egress conservation.** Mirror:
`Leanux/WG/Device.lean` (`wgXmit` at `:329`: the destination lookup in the
allowed-IPs trie, the no-peer and no-endpoint arms, the staged queue),
`Leanux/WG/AllowedIps.lean` (`lookupDst`), `Leanux/WG/Send.lean`
(`sendStagedPackets`, `createData`, `enqueuePerPeerTx`,
`enqueuePerDeviceAndPeer`, `MAX_STAGED_PACKETS`), `Leanux/WG/Data.lean`
(`encryptIter`, `encryptRingPoll`, `txIter`, `createDataDone`,
`sendSkbToPeer`), `Leanux/WG/Socket.lean` (`setPeerEndpoint`, the endpoint
read at the send, `tunnelXmit`), `Leanux/Net/Fib/` (C1's output route at
`udp_sendmsg`'s level, which the send takes). C: `device.c:137-231`
(`wg_xmit`: `wg_allowedips_lookup_dst` at `:153`, the ICMP unreachable arm
`:162` and `:227`, the no-endpoint arm `:170`, the staged queue's splice
`:215` with the overflow drop counted at `:213`, `tx_errors` at `:231`);
`send.c:342-400` (`wg_packet_send_staged_packets`: the keypair acquired at
`:358` is the peer's current keypair, `out_nokey` `:362-364` and
`out_invalid` `:367`, `:382`, every packet of the batch encrypted under
that one keypair, `:388`); `send.c:311-340` (`wg_packet_create_data`: the
per-peer and per-device queueing, the `-ENOSPC` and `-EPIPE` drop arms);
`send.c:287-309` (the encrypt worker), `send.c:262-285` (the tx worker,
in order per peer); `send.c:242-260` (`wg_packet_create_data_done`: every
packet handed to `wg_socket_send_skb_to_peer` at `:251`);
`socket.c:168-185` (the peer's endpoint read under its lock at the moment
of the send, `send4`/`send6`). Claim: every data packet the mirror hands
to the UDP socket was encrypted under a keypair that was, at the time of
`sendStagedPackets`, the current keypair of the peer that
`lookupDst` returned for the packet's destination, and was sent to that
peer's endpoint as it stood at the send; and every packet that enters the
staged queue is handed to the socket exactly once or dropped at exactly
one named arm (the staged overflow with `tx_dropped`, `out_nokey`,
`out_invalid`, the per-peer and per-device queue drops, the dead-peer and
socket failures) with its counter, never duplicated and never lost
silently; keepalives are bound the same way. Security consequence: a
packet encrypted under another peer's key or sent to another peer's
endpoint is a cross-peer leak of plaintext-equivalent material and a
misdelivery; a duplicated send is a replayed datagram the peer must then
reject. A counterexample is a socket send whose keypair's peer differs
from the destination's owner at the time of the send, a send to an
endpoint other than that peer's current one, or a staged packet that is
sent twice or neither sent nor counted at a named arm. Not claimed: the
order of sends across peers (R4's per-poll result is the receive side),
the IPv6 inner path beyond what the fixture produces, or the ICMP reply's
content (C1's module decides the route, not this campaign).

**T3. Silence.** Mirror: `Leanux/WG/Receive.lean` (`packetReceive` at
`:477`: the type and length arms; `receiveHandshakePacket` at `:263`: the
MAC states, the under-load branch, `sendHandshakeCookie` at `:257`,
`cookieValidatePacket`, `cookieMessageConsume`; `consumeData` at `:419`:
the index miss and the dead-peer arm), `Leanux/WG/RxData.lean` (the decrypt
failure and the keypair-kind arms), `Leanux/WG/Handshake.lean`
(`consumeInitiation`, `consumeResponse`, `sendHandshakeResponse`,
`timersHandshakeComplete`, `sendHandshakeInitiation`), `Leanux/WG/Send.lean`
(`sendKeepalive`, `sendQueuedHandshakeInitiation`), `Leanux/WG/Timers.lean`
(the expiries that send). C: `receive.c:92-190`
(`wg_receive_handshake_packet`: `wg_cookie_validate_packet` at `:121`;
the only reply to a packet that failed authentication is the cookie reply,
`:139-142` for an initiation and `:160-163` for a response, taken only
under load for a valid MAC1 without a valid MAC2; an invalid MAC returns
at `:128-131`; the response at `:154` and the keepalive at `:186` follow
only a consumed, authenticated initiation or response);
`receive.c:509-530` (`wg_packet_consume_data`: an index miss or a dead
peer drops with no reply); `receive.c:242-333` (`decrypt_packet` failure
drops); `receive.c:542-585` (`wg_packet_receive`: wrong type or length
drops); `cookie.c:180-196` (`wg_cookie_message_create`); `send.c:110-122`
(`wg_packet_send_handshake_cookie`). Claim: every transmission the mirror
makes (a handshake initiation, response or cookie reply, a data packet, a
keepalive) is caused either by the fixture's own operations (a configured
send, a timer the device armed itself, a netlink set) or by a received
packet that the mirror authenticated (a consumed initiation or response,
a decrypted data packet under a live keypair), with exactly one
exception: the cookie reply, sent only under load in reply to an
initiation or response whose MAC1 is valid and whose MAC2 is not, and
carrying nothing but the cookie. Equivalently: a datagram the mirror did
not authenticate causes no send, no timer arming and no state change
beyond the under-load bookkeeping and the drop counters. Security
consequence: a reply to unauthenticated input breaks WireGuard's silence
property, which is what makes the device invisible to probing, and a
reply larger than its cause is an amplification vector. A counterexample
is any send, timer arming or peer-state change whose cause in the run is
a packet that failed the MAC, the AEAD or the index lookup, other than
the cookie reply under its stated condition. Not claimed: that the cookie
reply is itself unforgeable (that is the cookie construction, a crypto
contract), or anything about timing side channels.

**T4. Handshake freshness.** Mirror: `Leanux/WG/Handshake.lean`
(`consumeInitiation` at `:93`: the timestamp comparison and the
per-peer flood check; `consumeResponse` at `:302`: the state check;
`beginSession` at `:273`; `createInitiation`, `createResponse`),
`Leanux/WG/Keypair.lean` (`keypairCreate`, `addNewKeypair`),
`Leanux/WG/Peer.lean` (`indexLookup`, `indexReplaceHandshake`). C:
`noise.c:633-640` (an initiation whose TAI64N timestamp is not greater
than the peer's `latest_timestamp` is a replay, and together with the
per-peer flood check at `:635` it is dropped at `:639-640`), `:645-646`
(the timestamp advances only on success), `:653`; `noise.c:763-764` (a
response is consumed only in state `HANDSHAKE_CREATED_INITIATION`, so a
replayed response, or a second response to one initiation, fails at
`fail`), `:790-792` (the state is re-checked under the lock), `:798`;
`noise.c:815-860` (`wg_noise_handshake_begin_session`: one keypair created
at `:827` per completed handshake, the handshake zeroed at `:841`, the
index entry replaced at `:850`); `noise.c:98-110`. Claim: a received
initiation whose timestamp is not strictly greater than the last
successfully consumed one from the same static key is rejected with no
state change, so a replayed initiation never creates a second handshake
state or response; a received response is consumed at most once per
initiation the mirror created, so a replayed response creates no second
session; and every completed handshake (`beginSession` returning true)
creates exactly one keypair, enters it into exactly one slot per H1's
rotation, and zeroes the handshake state. Security consequence: a
replayed initiation or response that was accepted would let an attacker
reset a peer's session, force a rekey or duplicate a session's keys; the
timestamp rule and the state machine are what prevent it. A
counterexample is a consumed initiation with a non-increasing timestamp, a
response consumed twice or outside the created-initiation state, or a
completed handshake that creates zero or two keypairs. Not claimed: the
Noise IK computations themselves (contracts), the cookie-based under-load
gate (R6), or the slot rotation's own invariant, which is campaign 2's H1;
cite H1's theorems rather than re-proving them, and if H1 is not yet
landed when you reach this point, state the rotation facts you need as
named hypotheses and record them for unification at integration.

**T5. Confirmation discipline.** Mirror: `Leanux/WG/Keypair.lean`
(`receivedWithKeypair` at `:93`, `addNewKeypair` at `:70`,
`keypairsClear`, `expireCurrentPeerKeypairs`), `Leanux/WG/Send.lean`
(`sendStagedPackets`: the keypair acquired for a send), `Leanux/WG/Data.lean`
(`keepKeyFresh`), `Leanux/WG/RxData.lean` (`keepKeyFreshRx`, the
consume-data-done path), `Leanux/WG/Handshake.lean` (`beginSession`,
`timersHandshakeComplete`, `timersSessionDerived`). C: `noise.c:253-300`
(`wg_noise_received_with_keypair`: a data packet decrypted under the
`next` keypair promotes it to `current`, the old current to `previous`,
exactly once, `:261-262`, `:269-273`, `:280-286`); `noise.c:815-860`
(`begin_session`: the responder's new keypair goes to `next`, the
initiator's to `current`, per `add_new_keypair`); `send.c:358`
(`wg_packet_send_staged_packets` encrypts under `current_keypair` only);
`receive.c:335-350` (`wg_packet_consume_data_done`: the promotion at
`:345-347`, followed by `wg_timers_handshake_complete`);
`receive.c:176-186` (the initiator, after consuming the response, sends a
keepalive under the new current keypair, which is the confirming packet).
Claim: the responder never encrypts a data packet or keepalive under a
keypair it created as responder until a data packet authenticated under
that keypair has been received (the keypair sits in `next` and the send
path reads only `current`); the initiator's new keypair is `current` from
`beginSession` on, so its first send under it is the confirmation; the
promotion happens exactly once per keypair and only on an authenticated
receive. Security consequence: data encrypted by the responder under an
unconfirmed keypair would be sent to an initiator that may not hold the
key yet and breaks the handshake's ordering guarantee on which its forward
secrecy and key-confirmation arguments rest. A counterexample is a
responder-side send under a keypair in `next`, or a promotion not caused
by an authenticated receive under that keypair. Not claimed: the rotation
invariant itself (H1), the keypair lifetime (R5, T6 deferred), or what the
initiator does with packets received before confirmation on its side.

Dependency order: T1 first (it needs only the keypair counter and the
send path); T2 beside it (the binding half shares the send path, the
conservation half is R4's method on the transmit side); T3 after T2's
send-path inventory, since silence is "no send without an authenticated
cause" and needs the complete list of send sites; T4 and T5 after T3,
with H1's slot facts cited or hypothesised. Work two at once when one is
blocked.

Prerequisites outside this campaign: none. B1's ring, B3's wheel, B4's
exact flood, C1's trie and campaign 1 are on `main`. Campaign 2 is in
flight and owns H1 to H6; T4 and T5 cite H1, as above. Landings that will
move `main` under you and are not prerequisites: campaign 2's results,
the binary track's merges, mirror corrections from the audits; all are the
merge-and-carry regime.

## 5. Success criterion

Per result: its `Statements.lean` holds every terminal statement as a
`theorem` with a docstring in plain words, including the security
sentence; the gate and the counterexample speedbump pass; the register
row names the claim-carrying theorems and the branch and mirror commit it
holds over; one short report per result appended to
`docs/2026-10-18-proof-campaign-3.md` (yours, a progress section at the
top): the architecture, every reshaped statement with both wordings,
every Rule Zero finding with its counterexample and its classification,
the effort, and a ranked list of mirror changes that would have made the
result routine, each marked altitude-preserving or not.

For the campaign: every result current over the `main` commit you end on,
or left with its blocker precisely written after a second architecture
has been tried. A Rule Zero finding with its counterexample and the rest
proved is a success. A reshaped statement that keeps the meaning is a
success. A missed item of the list above is a correction in the next
commit, not a failed result: nothing in this charter is a reason to stop
except the user's word.

## 6. Working conditions

- Three campaign trees, one `main`. Campaign 1's layers (`Framing`,
  `Logged`, `WG/Keypairs`, `WG/CounterWindow` and their files) are landed
  and are `main`'s: you add new files to a layer freely, and never edit an
  existing lemma or definition there; a change you need in a landed layer
  is a request in your report, not an edit. Campaign 2 owns its results
  and the files it created (`WG/Noise`, `WG/Index`, `WG/Roaming`,
  `WG/Config`, `WG/Progress`, `WG/TimerDiscipline` and their companions on
  its branch): read them through `git show proofs/campaign-2:<path>`,
  never edit them, and do not merge its branch; what you need from H1 you
  cite by name if it is on `main` or state as a named hypothesis if it is
  not. Your results live under `Leanux/Proofs/WG/NonceDiscipline/`,
  `TransmitBinding/`, `Silence/`, `HandshakeFreshness/`, `Confirmation/`
  or names you prefer, disjoint from both campaigns' directories.
- `main` will move under you, in two regimes [USER 2026-10-13]: for a
  landing that is not a prerequisite of any result, merge `main` when it
  moves, pay the frame contracts and carry on, without asking; a result
  that holds over a stale commit is "lagging" in the register until you
  do. For a named prerequisite there is none in this charter.
- Claims over a projection of `WGWorld`; frames in their own files;
  deletion of a frame only when the type gives the fact, never because a
  compile failed. The conventions note's five items are the house style.
- No quotation of the user anywhere: decisions, findings and reports are
  paraphrase with provenance tags.
- Multi-week. Subagents freely, on branches off `proofs/campaign-3` or in
  the worktree with one writer at a time.
- No hard stops. A blocked result gets its blocker written in the progress
  section and the next result starts; come back later. Stop only when the
  criterion is met for every result, when a claim refuses to close and is
  recorded as a finding, or when the user says so. Keep the register row
  and the report current as you go rather than stopping to report
  between items.
- One commit per proved result (checkpoint commits per intermediate model
  are fine). Neutral formal-verification framing. Your own commit
  attribution. No merge, no push.

## 7. Deferred, lower security consequence

Three results the parallel plan reserved for this campaign are deferred
to a later charter; their statements are kept short here so the deferral
is a choice, not a loss. None of them has a confidentiality, integrity or
authentication consequence of the kind the five above have; their failure
modes are availability, observability or composition.

- **Key lifetime over the wheel.** With B3's wheel as semantics, the
  zero-key-material timer fires at its bucket's expiry and clears every
  keypair of the peer (`timers.c:203-206`, `:61-62`), after which no
  encryption or decryption uses them; the rekey-after-time check at send
  causes an initiation when due. Stated over the wheel's firing rule, not
  over recorded sections, and not as the unconditional claim R5 refuted.
  Consequence of failure: a key used past its intended lifetime, which
  weakens forward secrecy over time but is bounded by the message limit
  T1 proves.
- **Resource bounds.** The handshake queue never exceeds its ring's
  capacity and a refused producer takes the counted drop; the per-peer
  rings and the crypt queues are bounded by their capacities; the
  ratelimiter's table is bounded by `max_entries` with the over-limit arm
  named; all stated over B4's exact flood. On the uncounted-drop finding
  of tray entries 01 and 02 (ring-full and queue-full drops not counted):
  the judgement is that it is not a security consequence in the sense of
  this charter. A drop that is not counted hides load from the operator
  and so is an observability defect with an availability flavour; it does
  not let any packet through, leak anything, or weaken authentication,
  and the DoS defence proper, the cookie gate, is R6's result. The
  handshake-ring bound therefore stays deferred with the rest.
- **End-to-end routing composition, IPv4 only.** A packet injected toward
  the device reaches the receiving side's stack exactly when the chain of
  C1's route lookup, the trie's peer selection, encryption under T1 and
  T2's binding, delivery, decryption and R3's source check admits it,
  composed over the fixture's single-device traces; the composition of
  landed results with its hypotheses listed, not new local reasoning.
  Consequence of failure: a gap between the landed results' coverage of
  the path, which is a completeness matter rather than a property.

## 8. What comes after

Each landed result is reviewed independently before it merges. When the
three campaigns are current, the model layer covers the protocol's stated
behaviour at the sequential level except the deferred items above; the
concurrency question and the code-to-binary adequacy are the user's
separate tracks.

## Paste for Codex#1

> Proof campaign 3 over the WireGuard mirror: five results, in order, as
> one self-paced grind beside campaign 2. Charter:
> `docs/2026-10-18-charter-proof-campaign-3.md` (read it whole, then
> `docs/proofs.md`, the two earlier charters and campaign 1's report,
> campaign 2's report on its branch read-only, the conventions note, the
> reviews, the send and handshake audits, and the landed designs it names).
> Worktree `.worktrees/proofs-campaign-3`, branch `proofs/campaign-3` from
> `main` on Lean v4.35.0, already created; work only there. T1 sender
> nonce discipline, T2 transmit binding and egress conservation, T3
> silence, T4 handshake freshness, T5 confirmation discipline; each a
> directory under `Leanux/Proofs/WG/` with a `Statements.lean` whose
> theorems carry a docstring with the security sentence, the gate and the
> counterexample speedbump passing, a register row, a short report.
> Campaign 1's layers are main's: add files there, never edit an existing
> lemma; campaign 2 owns H1 to H6 and its files: read them, never edit
> them, cite H1 by name or state what you need as a named hypothesis. Rule
> Zero: the mirror is never edited; a proof that will not close is a
> finding with a counterexample, and that is a success, with "statement
> artefact" the first hypothesis to test. When `main` moves, merge and pay
> the frames without asking; nothing in this charter is a prerequisite.
> Claims over a projection of `WGWorld`, frames in their own files, deleted
> only when the type gives the fact. Keep the register row and the report
> current as you go, stop only when blocked, at a finding, or at the
> campaign's landing. No quotation of the user. No merge, no push;
> `capped` for builds; use the box.
