# Charter: proof campaign 3, the high-consequence group

A long-cycle proof assignment for a Codex agent and its subagents, in the
form of [the first](2026-10-13-charter-proof-campaign.md) and
[the second](2026-10-14-charter-proof-campaign-2.md) campaign's charters:
six WireGuard security outcomes over the mirror that neither landed
campaign nor the one in flight establishes, chosen for the consequence of
their failure. It runs beside campaign 2 (Codex#2, `proofs/campaign-2`,
the handshake and configuration group) under the disjointness rule of
section 6.

Provenance: [USER 2026-10-18] the campaign is chartered for the properties
with high security consequences that the mirror's proofs do not yet
cover, everything a good WireGuard proof should cover at the sequential
model level; the lower-consequence items the parallel plan reserved for
this campaign are deferred (section 7). [AGENT, coordinator] wrote the
first version from the coverage table put to the user on 2026-10-18.
Revision 2 [AGENT, fork of the coordinator, 2026-10-18] follows the
independent review by Codex#1 (`docs/2026-10-18-review-campaign-3-charter.md`,
uncommitted on `task/review-campaign-3` at the time of reading; verdict:
keep the five themes, correct T1 to T3's contracts, promote key retirement
into the high-priority group). Its seven findings are dispositioned in
section 9; its recommended-goals table is the shape the statements now
take: the campaign commits to the security outcomes and leaves theorem
decomposition, intermediate models, instrumentation and work order open.

## 1. What this is, and what it is not

Mirror to property, as before: properties of WireGuard proved over the
executable mirror's own definitions, with whatever Lean models sit in
between. Code to mirror is not this assignment; neither is the binary
track. Theorems live in the proof tree `Leanux/Proofs/` with its gate and
register ([AGENTS.md](../AGENTS.md), [docs/proofs.md](proofs.md)); proofs
are a validation channel for the models, so a Rule Zero finding is a
success of this campaign.

The mirror is sequential: one CPU, no preemption, the softirq and worker
placements from the records. Every outcome below is an outcome about that
model under the cryptographic primitives as contracts, and each names the
consequence of its failure in the implementation the model mirrors.
Nothing here is a claim about the C, about concurrency, about the
primitives, or about physical memory: removal of a key from the mirror's
store is what the mirror can express; zeroisation of bytes is beyond it.

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
  stays byte-identical to `main` at every commit of yours. Results live
  in directories under `Leanux/Proofs/WG/` of your choosing, each with a
  `Statements.lean` imported from `Leanux/Proofs.lean` and a row in the
  register; the register's "Adding a result" section is the procedure.
  Form is corrected, never stopped on.
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
  index, roaming and the timers; the review of this charter
  (`docs/2026-10-18-review-campaign-3-charter.md`, on
  `task/review-campaign-3` until it lands); the window-proof conventions
  and the reviews (`docs/2026-10-17-review-campaign-1-landing.md`,
  `docs/2026-10-13-review-r5-counterexamples.md`); the send and handshake
  correspondence audits (`docs/2026-10-15-audit-send.md`,
  `docs/2026-10-13-audit-handshake.md`), which walked the modules you will
  reason over line by line against the C; the tray entries 01 and 02 for
  the disposal arms that have no counter; the landed designs the results
  rest on: the exact flood and rate limiter
  ([B4](2026-10-15-design-b4-load-ratelimiter.md)), the handshake ring
  ([B1](2026-10-15-design-b1-handshake-ring.md)), the timer wheel
  ([B3](2026-10-15-design-b3-timer-wheel.md)), the FIB trie
  ([C1](2026-10-15-design-c-fib-trie.md)), the transmit design
  ([W4+W7](2026-10-06-w4-w7-transmit-bulk.md)) and the DoS design
  ([E](2026-10-05-e-dos.md)); and the mirror modules each outcome names,
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

A statement that is false of the mirror gets a concrete counterexample (a
trace and record stream the runner accepts, and the two events or the
divergence), a judgement whether the code's behaviour is a bug against
its intent or a design nuance, and then one of: the statement proved
under a named premise that excludes the trigger and cites the finding,
or the statement left unproved with the counterexample recorded. The
mirror is never edited by this campaign, and neither is the kernel.
Reshaping for a legitimate nuance is allowed and expected: prove the
property the code has, record both wordings and the reason, keep the
meaning.

Two cautions specific to this campaign. Campaign 1 refuted four literal
wordings as statement artefacts, and this charter's first version
contained wording errors of the same kind, corrected in revision 2; that
history creates no presumption that the next discrepancy is harmless.
Each is diagnosed on its evidence, mirror first. And a premise that
excludes an actual attack is a restriction on the result, to be stated as
such in the register, not a preservation of the original outcome.

## 4. The campaign

Six security outcomes, each a commitment to what the campaign establishes
and a sentence on the consequence of its failure; the theorem
decomposition, the intermediate models, the instrumentation and the order
of work are yours. The order below is advisory (section 6). Every C line
cited is in `drivers/net/wireguard/` of the pinned source; the mirror
lines are at `main` 77c9b555.

| Outcome | What the campaign establishes |
| --- | --- |
| T1 nonce safety | Every actual transport encryption uses a nonce uniquely allocated for that sending-key lifetime, below the rejection limit; failed or abandoned work never makes an allocated nonce reusable. |
| T2 transmit authorization and conservation | Each emitted ciphertext is tied to the intended packet and peer at the relevant selection points, under the key and to the endpoint selected there; every admitted packet has exactly one accounted disposition, pending included; no packet is duplicated or substituted. |
| T3 authenticated effects and silence | Input the mirror did not accept cannot authorize session establishment, endpoint learning, transport delivery or protocol responses, apart from the explicitly bounded cookie behaviour; every delayed send has a legitimate causal root. |
| T4 handshake replay resistance | A replay cannot advance a retained peer's handshake freshness state or install another session for an already consumed exchange; installation and handshake clearing are connected to that exchange. |
| T5 responder key confirmation | Every responder encryption under a session has an earlier accepted confirming receive under that session; confirmation promotes that allocation at most once. |
| T6 key retirement | The age and invalidation checks prevent new unauthorized uses unconditionally; expiry and lifecycle cleanup retire key material through the actual deferred-work and reference rules, under explicit scheduling assumptions. |

**T1. Nonce safety.** Mirror: `Leanux/WG/Send.lean` (`sendStagedPackets`
`:223-269`: the nonce allocated per staged packet in queue order at
`:250-254` before any queue admission, the rejection arm at `:255-257`
through `outNokey true`, which invalidates the sending key and restores
the whole batch to the head of the staged queue at `:233-243`;
`createData` `:160-174`, the queue admission with its `-ENOSPC` and
`-EPIPE` arms; `sendQueuedHandshakeInitiation` `:59-84` with its guards;
the constants `:55-57`), `Leanux/WG/Data.lean` (`encryptPacket` `:74-98`,
the failure arms before the AEAD and the nonce as the header counter and
the AEAD input; `keepKeyFresh` `:185-197`), `Leanux/WG/Keypair.lean`
(`keypairCreate` `:58`), `Leanux/WG/Types.lean` (`Keypair.sendingCounter`
`:134-135`). C: `send.c:379-382` (the nonce is
`atomic64_inc_return(&sending_counter) - 1`, assigned in batch order
before encryption; at or past `REJECT_AFTER_MESSAGES` the batch goes to
`out_invalid`), `send.c:386-400` (`out_invalid` marks the sending key
invalid, `out_nokey` puts it, the packets are orphaned and spliced back
onto the staged queue, and a handshake is requested), `send.c:162-219`
(`encrypt_packet`: the header counter at `:208`, the AEAD nonce at
`:217`, the allocation and checksum failure arms before them),
`send.c:124-139` (`keep_key_fresh`), `send.c:311-340` (the queue
admission), `noise.c:98-110` (the counter starts at zero),
`messages.h:41-42`. Outcome: for every keypair, no two actual encryptions
(an AEAD call that produces a ciphertext) use the same nonce; every
actual encryption's nonce is the one allocated to that packet, is the
header's counter and the AEAD's nonce, and is below
`REJECT_AFTER_MESSAGES`; a nonce consumed by an allocation whose packet
never reaches the AEAD (queue refusal, an allocation failure in
`encryptPacket`, a batch restored by the rejection arm) is never
allocated again under that key, so a gap in the encrypted sequence is
safe and gaps are expected; reaching the rejection limit invalidates the
key for sending and restores the batch, so no encryption happens under
that key after the limit and the batch is not a counted drop; and
`keepKeyFresh` requests an initiation when the counter is past
`REKEY_AFTER_MESSAGES` or the initiator's key is past `REKEY_AFTER_TIME`,
where "requests" means the call into `sendQueuedHandshakeInitiation`,
whose own guards (the rekey timeout, a dead peer, work already queued)
decide whether a worker is queued and whether a handshake is transmitted.
Consequence of failure: a nonce reused under one key with
ChaCha20-Poly1305 breaks confidentiality (keystream reuse) and integrity
(forgeable tags) for that key. Not required: consecutive encrypted
nonces; unconditional transmission of a rekey initiation; anything about
the receiving counter (R1) or the cipher. Crossing the configured bound
is a policy violation to be shown impossible, not evidence that a nonce
repeated.

**T2. Transmit authorization and conservation.** Mirror:
`Leanux/WG/Device.lean` (`wgXmit` `:329-388`: the destination's peer from
`lookupDst` at `:384`, the no-peer and no-endpoint arms with their ICMP
cuts, the staged-queue overflow drop with its counter), `Leanux/WG/AllowedIps.lean`
(`lookupDst`), `Leanux/WG/Send.lean` (`sendStagedPackets` `:223-269`: the
peer's current keypair read when staging is drained at `:230`;
`createData` `:160-174`; `enqueuePerPeerTx` `:108`,
`enqueuePerDeviceAndPeer` `:132`; `sendKeepalive` `:273-281`, bound to
the peer its caller names), `Leanux/WG/Data.lean` (`encryptIter`,
`encryptRingPoll`, `txIter`; `createDataDone` `:200`; `sendSkbToPeer`
`:170-178`, the endpoint read at the socket send), `Leanux/WG/Socket.lean`
(`setPeerEndpoint`, `tunnelXmit`), `Leanux/Net/Fib/` (C1's output route).
C: `device.c:137-231` (`wg_allowedips_lookup_dst` at `:153`, the arms at
`:162`, `:170`, `:183`, the overflow drop counted at `:213`, the splice
`:215`, `tx_errors` `:231`), `send.c:342-400` (the current keypair at
`:358`, the whole batch under that one keypair at `:388`, the restore
arms), `send.c:311-340` (`wg_packet_create_data`: the `-ENOSPC` and
`-EPIPE` queue arms), `send.c:287-309` and `:262-285` (the workers, per
peer in order), `send.c:242-260` (every packet handed to
`wg_socket_send_skb_to_peer` at `:251`, `data_sent` and the timers),
`socket.c:168-185` (the endpoint read under its lock at the send). There
are three selection times and the outcome is stated at each: the peer is
the one `lookupDst` returned for the packet's inner destination at
`wgXmit` (for a keepalive, the peer its caller names); the key is that
peer's current keypair when the staging queue is drained; the endpoint is
that peer's endpoint as read at the socket send. Outcome: every emitted
ciphertext is the AEAD of the packet admitted at `wgXmit` under the key
selected for it at staging, carrying that key's allocated nonce, handed
to the socket for the endpoint selected at the send, and the peer of the
key is the peer selected at `wgXmit`; R3's outgoing authorization
(`parsed_initialized_transmit_authorization`) is reused where it applies
and not re-proved. Conservation: every packet admitted at `wgXmit` has,
at every point of the run, exactly one logical obligation, which may be
represented in several queues (staged, the per-peer and per-device rings,
the tx queue), or exactly one terminal outcome among: handed to the
socket (then succeeded or failed, each once, never counted twice), or
disposed at a named arm; the named arms list the ones with a counter
(the staged overflow, `tx_errors`) and the ones with none (the queue
refusal and the encryption-failure paths, as tray entry 01 records),
and a run may end with obligations pending (a packet staged while a
handshake is awaited is legitimately pending); no packet is duplicated
and none substituted for another. Consequence of failure: a packet
encrypted under an unintended peer's key discloses its plaintext to that
peer; a packet sent to a wrong endpoint under the right key discloses
nothing by itself but misdelivers; a duplicated handoff is a replayed
datagram the peer must reject, not a second encryption. Not required:
eventual completion of pending obligations (a progress property under
extra assumptions, which may be a separate result); a counter at arms the
C does not count; the destination's ownership re-tested at the send
(allowed-IPs may change while a packet waits; that is a different
policy, not this outcome); the IPv6 inner path beyond what the fixture
produces; the ICMP reply's content.

**T3. Authenticated effects and silence.** Mirror: `Leanux/WG/Receive.lean`
(`packetReceive` `:477`; `receiveHandshakePacket` `:263`: the under-load
bookkeeping `:292-320`, `cookieValidatePacket` `:201-216` with the
secret rotation, the MAC states, `sendHandshakeCookie` `:257`;
`cookieMessageConsume` `:80-99`: the cookie, its birthdate, validity and
`haveSentMac1`; `consumeData` `:419`: the index miss and the dead-peer
arm), `Leanux/WG/RxData.lean` (the age and validity check before
decryption `:63-76`, which may mark an expired receiving key invalid
before the AEAD; `decDecryptFailed`; the replay window at `:589-595`
before `consumeDataDone` `:290-297`, which sets the endpoint, confirms,
and arms the timers), `Leanux/WG/Handshake.lean` (`consumeInitiation`,
`consumeResponse`, `sendHandshakeResponse`, `sendHandshakeInitiation`,
the timer arming calls), `Leanux/WG/Send.lean` (`sendKeepalive`,
`sendQueuedHandshakeInitiation`), `Leanux/WG/Timers.lean` (the expiries
that send or queue work), `Leanux/Env.lean` (the dispatch of queued work).
C: `receive.c:92-190` (`wg_cookie_validate_packet` at `:121`; the cookie
reply at `:139-142` and `:160-163`, only under load for a valid MAC1
without a valid MAC2; an invalid MAC returns at `:128-131`; the response
at `:154` and the keepalive at `:186` follow only a consumed exchange),
`receive.c:509-530`, `receive.c:242-333`, `receive.c:542-585`,
`cookie.c:198-236` (`wg_cookie_message_consume`), `cookie.c:180-196`,
`send.c:110-122`, `timers.c` (the arming sites). The authentication
boundary has three distinct acceptance events, kept distinct: a consumed
handshake exchange (an initiation or response that passed its MACs and
the Noise consumption); an accepted transport packet (decrypted under a
live keypair and admitted by the replay window, which is the event that
authorizes endpoint learning, confirmation and timer activity; inner
source authorization and delivery to the stack come later and are not
required for confirmation); and a consumed cookie message (a separately
checked control message that updates the peer's cookie state and nothing
else). The causal roots are: trusted local actions (a configured send
through `wgXmit`, a netlink set, device up and down), the three
acceptance events, and timers and queued work traced back through their
arming and queueing to one of those; packet injection is not a root, and
a timer armed by rejected input is not a root. Outcome: input the mirror
did not accept authorizes no session establishment, no endpoint change,
no transport delivery and no protocol response, and causes no timer
arming and no queued work whose later effect is one of those; the only
transmission in reply to unaccepted input is the cookie reply, at most
one fixed-format 64-byte message to the input's source per qualifying
input, under the actual load and MAC conditions, installing no session
and smaller than either handshake input (148 or 92 bytes), which bounds
packet and payload amplification for this exception; the bookkeeping
that rejected input may change is named narrowly (the under-load clock
and counters, the cookie checker's secret rotation and rate-limit state,
queue occupancy and reference accounting before authentication, the
invalidation of an expired receiving key, the drop counters) and nothing
else. Consequence of failure: a reply or a state effect authorized by
unaccepted input breaks silence, which is what keeps the device invisible
to a scanner that does not hold the peer's public key (MAC1 is derived
from the public key, so this is invisibility to those without it, not
authentication of a configured peer), and a reply larger than its cause
is an amplification vector. Not required: equality of the whole world
after a rejection; a CPU-exhaustion bound (the deferred DoS item);
unforgeability of the cookie itself (a contract); timing side channels.

**T4. Handshake replay resistance.** Mirror: `Leanux/WG/Handshake.lean`
(`consumeInitiation` `:93`: the timestamp comparison and the per-peer
flood check; `consumeResponse` `:302`: the state check; `beginSession`
`:273-297`: the keypair allocation, which can fail and return false, and
the handshake clearing), `Leanux/WG/Peer.lean` (`handshakeZero` `:232-236`,
which preserves `latestTimestamp`; `indexLookup`,
`indexReplaceHandshake`), `Leanux/WG/Types.lean` (`latestTimestamp`
`:320`, zero for a newly created peer), `Leanux/WG/Keypair.lean`
(`keypairCreate`, `addNewKeypair`). C: `noise.c:633-640` (an initiation
whose TAI64N timestamp is not greater than the peer's `latest_timestamp`,
or one inside the per-peer flood interval, is dropped), `:645-646` (the
timestamp advances only on success), `:653`; `noise.c:763-764` and
`:790-792` (a response is consumed only in the created-initiation state,
re-checked under the lock), `:798`; `noise.c:815-860`
(`begin_session`: one keypair at `:827`, the handshake zeroed at `:841`,
the index entry replaced at `:850`); `noise.c:98-110`. The identities are
lifetimes, not byte strings: freshness state belongs to a retained peer
(it survives `handshakeZero`, and a peer created anew starts at zero, so
peer removal and device recreation are the reset boundaries and the
outcome is stated within a retained peer's lifetime with those boundaries
named); an exchange is the actual occurrence of a created initiation and
its consumed response, not a wire index alone. Outcome: within a retained
peer's lifetime, a received initiation whose timestamp is not strictly
greater than the last successfully consumed one leaves the handshake and
session state unchanged (the surrounding queue, clock-record and cookie
state are not claimed unchanged), so a replayed initiation advances no
freshness state and produces no response; a response is consumed at most
once per created initiation, so a replay installs no second session; and
when `beginSession` succeeds for an exchange it allocates exactly one
keypair for it, installs it into the slots per H1's rotation, and clears
the handshake, while an allocation failure installs nothing and leaves
the handshake for retry, so an observed exchange does not by itself
guarantee installation. Consequence of failure: an accepted replayed
initiation or response lets an attacker reset a peer's session, force a
rekey or duplicate a session's keys. Not required: uniqueness of key
bytes across exchanges (the Noise derivation and the randomness are
contracts to be named, not proved); the cookie gate under load (R6); the
slot rotation itself (campaign 2's H1: cite its theorems if landed, or
state the rotation facts as named hypotheses that remain visible in the
final claim).

**T5. Responder key confirmation.** Mirror: `Leanux/WG/Keypair.lean`
(`receivedWithKeypair` `:93-116`, `addNewKeypair` `:70-86`: a pending
responder key can be replaced or cleared before confirmation;
`keypairsClear`, `expireCurrentPeerKeypairs`), `Leanux/WG/Send.lean`
(`sendStagedPackets` `:230`: only `keypairCurrent` is read for a send),
`Leanux/WG/RxData.lean` (`consumeDataDone` `:290-297`: the promotion on an
accepted transport packet, after the replay window), `Leanux/WG/Data.lean`
(`keepKeyFresh`), `Leanux/WG/Handshake.lean` (`beginSession`,
`timersHandshakeComplete`, `timersSessionDerived`). C: `noise.c:253-300`
(`wg_noise_received_with_keypair`: the promotion of `next` to `current`,
exactly once, under the lock), `noise.c:815-860` (the responder's new
keypair to `next`, the initiator's to `current`), `send.c:358`,
`receive.c:335-350` (the promotion after a packet is accepted), and
`receive.c:176-186` (the initiator's keepalive under the new current
keypair is the confirming packet). Identities are allocations: a
keypair's identity is its allocation in the store, not its raw id (which
campaign 2's checkpoint reports repeating across device recreations) and
not its wire index. Outcome: every responder-side encryption under a
keypair allocated for a session has an earlier accepted transport receive
under that same allocation (the key sits in `next` and the send path
reads `current` until the promotion); the promotion of an allocation
happens at most once and only on an accepted transport packet under it,
where accepted includes the replay window; an old current key remaining
in use while a new responder key waits is permitted, as the protocol
permits; a pending responder key may be replaced or cleared without ever
being confirmed. Consequence of failure: data encrypted by the responder
under an unconfirmed key is sent to an initiator that may not hold it
and breaks the handshake's ordering guarantee on which its key
confirmation and forward secrecy rest. Not required: the rotation
invariant (H1); the initiator's handling of packets before confirmation;
key retirement (T6).

**T6. Key retirement.** Mirror: `Leanux/WG/Send.lean` (`sendStagedPackets`
`:244-261`: the sending key's validity and age checked at batch
admission), `Leanux/WG/RxData.lean` (`:63-76`: the receiving key's
validity, age and counter limit checked before decryption, with the key
marked invalid on failure), `Leanux/WG/Timers.lean` (`expiredZeroKeyMaterial`
`:57-72`: the zero-key timer queues the clear work on the handshake-send
queue and does not clear keys itself), `Leanux/WG/Keypair.lean`
(`queuedExpiredZeroKeyMaterial` `:143-149` and `keypairsClear`
`:105-116`: the worker clears the three slots; `keypairPut` `:38-49`:
reference release removes the keypair from the store; `addNewKeypair`
`:70-86`; `expireCurrentPeerKeypairs`), `Leanux/Kernel/TimerWheel.lean`
and `Leanux/Env.lean` (B3's wheel and the dispatch of the clear work),
`Leanux/WG/Data.lean` (`keepKeyFresh`). C: `send.c:365-367`
(`REJECT_AFTER_TIME` at batch admission), `receive.c:242-260`
(`decrypt_packet`'s validity, age and counter checks), `timers.c:105-120`
(`wg_expired_zero_key_material` queues `clear_peer_work`),
`timers.c:203-206` (`wg_timers_session_derived` arms it at
`REJECT_AFTER_TIME * 3`), `noise.c` (`wg_noise_keypairs_clear`, the puts
and the RCU release), `send.c:124-139`. Two obligations, kept separate.
Unconditional safety at the use checks: no transport encryption under a
sending key that is invalid or older than `REJECT_AFTER_TIME`, and no
decryption under a receiving key that is invalid, older than
`REJECT_AFTER_TIME` or past its counter limit, with a failed check
marking the key invalid; these hold for every accepted run with no
scheduling assumption. Conditional operational retirement: under stated
assumptions about the clock reads and the dispatch of queued work (the
wheel's firing rule and the worker's run, as the records place them), the
zero-key timer armed at session derivation queues the clear work when it
fires, the worker clears all three slots, and reference release removes
each cleared keypair from the mirror's store once its last reference
drops, so that after retirement no path can obtain the keypair from the
store; already admitted work and retained references are given an
explicit disposition (what still holds a reference, and that it cannot
start a new encryption past the checks above). What removal from the
abstract store establishes is exactly that: no further lookup or slot
read yields the keypair; zeroisation of physical memory is beyond the
mirror and is said so. Consequence of failure: a key retained past its
lifetime is one a captured key can still authenticate or decrypt traffic
with, which is the time-based part of WireGuard's forward-secrecy design
(whitepaper sections 6.2 and 6.3); the message bound of T1 does not
protect an idle key. Not required: an instantaneous wall-clock erasure;
R5's refuted unconditional wording; the rekey transmission itself (T1's
request clause).

Relations between the outcomes, so the decomposition can share: T6's use
checks are the companions of T1's bound and T5's confirmation; T2's
conservation supports T2's binding and T3's causal tracing of queued
work; T3's accepted-transport event is T5's confirming receive; H1's
rotation facts serve T4 and T5. The six need not be six directories or
six independent projects.

Prerequisites outside this campaign: none. B1's ring, B3's wheel, B4's
exact flood, C1's trie and campaign 1 are on `main`. Campaign 2 is in
flight and owns H1 to H6. Landings that will move `main` under you and
are not prerequisites: campaign 2's results, the binary track's merges,
mirror corrections from the audits; all are the merge-and-carry regime.

## 5. Success criterion

A result is landed when its `Statements.lean` holds its terminal
statements as theorems with docstrings in plain words, including the
security sentence; the gate and the counterexample speedbump pass; the
register row names the claim-carrying theorems, the branch and mirror
commit it holds over, every assumption and boundary (named hypotheses,
scheduling assumptions, contracts) and what remains conditional or
excluded; and one short report per result is appended to
`docs/2026-10-18-proof-campaign-3.md` (yours, a progress section at the
top): the architecture, every reshaped statement with both wordings,
every Rule Zero finding with its counterexample and its classification,
the effort, and a ranked list of mirror changes that would have made the
result routine, each marked altitude-preserving or not.

What counts, and what does not: a landed result is an actual mirror-path
theorem for initialized, reachable executions with its assumptions
explicit, or a precisely classified counterexample or open obligation.
Local helper lemmas and imported hypotheses are progress and are reported
as such; they do not by themselves establish the headline, and an
undischarged hypothesis stays visible in the final claim. A failure or
stop prefix of a run must not erase earlier security-relevant events from
the claim's scope.

For the campaign: every result current over the `main` commit you end on,
or left with its blocker precisely written. A Rule Zero finding with its
counterexample and the rest proved is a success. A reshaped statement
that keeps the meaning is a success. A missed item of the list above is
a correction in the next commit, not a failed result: nothing in this
charter is a reason to stop except the user's word.

## 6. Working conditions

- Three campaign trees, one `main`. Campaign 1's layers (`Framing`,
  `Logged`, `WG/Keypairs`, `WG/CounterWindow` and their files) are landed
  and are `main`'s: you add new files to a layer freely, and never edit an
  existing lemma or definition there; a change you need in a landed layer
  is proposed separately in your report, not edited. Campaign 2 owns its
  results and the files it created (`WG/Noise`, `WG/Index`, `WG/Roaming`,
  `WG/Config`, `WG/Progress`, `WG/TimerDiscipline` and their companions on
  its branch): read them through `git show proofs/campaign-2:<path>`,
  never edit them, and do not merge its branch; what you need from H1 you
  cite by name if it is on `main` or state as a named hypothesis if it is
  not. Your results live under `Leanux/Proofs/WG/` in directories of your
  choosing, disjoint from both campaigns'.
- Implementation freedom: the order of section 4 is advisory; T4 and T5
  may start before T2's inventory of send sites; results may be split or
  combined; trying a second architecture is a diagnostic option, not a
  prerequisite for recording a well-understood blocker; a counterexample
  settles a false statement as before.
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
- One commit per landed result (checkpoint commits per intermediate model
  are fine). Neutral formal-verification framing. Your own commit
  attribution. No merge, no push.

## 7. Deferred, with the exposure named

Two items the parallel plan reserved for this campaign are deferred to a
later charter. Each is stated short, with what remains exposed while it is
deferred; neither is deferred because it is harmless.

- **DoS resistance: resource bounds.** The handshake queue never exceeds
  its ring's capacity and a refused producer takes the counted drop
  (B1's ring); the per-peer rings, the crypt queues and the receive queues
  are bounded by their capacities, the receive queues filling before
  transport authentication as tray entry 02 explains; the ratelimiter's
  table is bounded by `max_entries` with the over-limit arm named; all
  stated over B4's exact flood. This is deferred DoS resistance: the
  cookie gate (R6) is one part of the defence, not a proof of it, and
  while this is deferred the bound on attacker-controlled memory and
  expensive work in the receive queues stays unproved. That exposure is
  availability, not confidentiality or authentication, which is why it
  yields to T1 to T6; it is not low consequence.
- **Missing drop statistics.** Separately from the bounds: the disposal
  arms that have no counter (tray entries 01 and 02: the transmit queue
  refusal and encryption-failure paths, the receive queue-full drops).
  This is an observability defect in the C, already in the tray, and the
  reason it is not a campaign result is that a proof cannot supply a
  counter the code does not have; T2 names those arms as counterless.
- **End-to-end routing composition, IPv4 only.** A packet injected toward
  the device reaches the receiving side's stack exactly when the chain of
  C1's route lookup, the trie's peer selection, encryption under T1 and
  T2's binding, delivery, decryption and R3's source check admits it,
  composed over the fixture's single-device traces; the composition of
  landed results with its hypotheses listed. It can wait provided T2
  actually closes the authorization-to-encryption connection, which is
  why T2 is stated at all three selection points; a composition failure
  found later would be a gap in that connection, not a harmless
  completeness matter.

## 8. What the campaigns will have established

When campaign 2 and this campaign are current, the sequential model will
carry: replay freedom on the receive side (R1) and nonce safety on the
sending side (T1); cryptokey routing both ways (R3, T2); lifetime safety
of identities (R2) and key retirement at the use checks and, under
scheduling assumptions, through the cleanup (T6); the handshake state
machine (H1), index uniqueness (H2), roaming on authentication only (H3),
replay resistance (T4) and responder confirmation (T5); silence with the
bounded cookie exception (T3) and the cookie gate's local behaviour (R6);
ingress conservation and the per-poll order (R4) and egress conservation
(T2); configuration readback (H4), progress relative to the records (H5)
and timer discipline (H6). Conditional or excluded: everything about the
cryptographic primitives and the Noise derivation (contracts);
cryptographic forward secrecy as such (T6 gives the time-based retirement
the design relies on, not the cryptographic argument); global
availability and DoS resistance (section 7); run-wide pre-GRO order;
anything about concurrency or the C itself; and whatever named
hypotheses remain undischarged in a result's final claim. Campaign 2's
results are in progress at the time of writing and are listed as they
are chartered, not as landed.

## 9. Dispositions of the review's findings

The review is Codex#1's, read uncommitted on `task/review-campaign-3`.

- **F1, high, key retirement is a security goal.** Fixed: T6 added to the
  high-priority group with the split the review draws, unconditional
  safety at the use checks (`Send.lean:244-261`, `RxData.lean:63-76`)
  separate from conditional operational retirement (the timer queuing the
  clear work `Timers.lean:57-72`, the worker clearing the slots
  `Keypair.lean:105-116`, `:143-149`, reference release removing the
  keypair `Keypair.lean:38-49`) under stated clock and worker
  assumptions; what removal from the abstract store establishes is named;
  physical zeroisation is named as beyond the mirror; the claim that T1's
  message bound protects an idle key is withdrawn (it does not). The
  deferred section loses it.
- **F2, high, T1 confused allocation, encryption and transmission.**
  Fixed: the outcome is uniqueness per allocation, no reuse after failed
  or abandoned work, the hard bound, and the link from the allocated nonce
  to the header counter and the AEAD input; gaps are expected and safe
  (the allocation at `Send.lean:250-254` precedes queue admission and the
  failure arms of `encryptPacket`); the rejection arm invalidates the key
  and restores the whole batch (`send.c:386-400`, `Send.lean:233-243,
  255-257`), not a counted suffix drop; the rekey clause distinguishes the
  request into `sendQueuedHandshakeInitiation` from its guards and from
  transmission; consecutive encrypted nonces and unconditional rekey
  transmission are not required.
- **F3, high, T2 needed pending work, historical selection and the
  actual drop semantics.** Fixed: the three selection times are stated
  and the binding holds at each; conservation allows one pending logical
  obligation across several queues or one terminal outcome; socket
  handoff, socket failure and success are distinguished so nothing counts
  twice; the arms with and without a counter are named (tray entry 01);
  eventual completion is a separate progress property; the consequence
  sentence is calibrated (a wrong key discloses plaintext to the wrong
  peer, a wrong endpoint under the right key does not by itself, a
  duplicated handoff is a replayed datagram and not a second encryption);
  re-testing destination ownership at the send is dropped as a different
  policy.
- **F4, high, T3 needed a real authentication boundary and causal roots.**
  Fixed: three acceptance events kept distinct (consumed exchange,
  accepted transport packet after the replay window, consumed cookie
  message); roots defined (trusted local actions, the acceptance events,
  timers and queued work traced back to them), with injection not a root
  and a timer armed by rejected input not a root; the permitted
  bookkeeping of rejected input named narrowly (`Receive.lean:80-99,
  123-129, 201-216, 292-320`; `RxData.lean:63-86`); the cookie exception
  bounded (at most one 64-byte fixed-format reply to the source per
  qualifying input, no session, smaller than either input); the
  equivalence between no response and no state change withdrawn; the
  invisibility claim qualified to scanners without the public key, with
  the CPU-exhaustion bound left to the deferred DoS item.
- **F5, medium, lifetimes for T4 and T5.** Fixed: freshness state is the
  retained peer's, surviving `handshakeZero` (`Peer.lean:232-236`) and
  reset at peer creation (`Types.lean:320`), with removal and recreation
  as the stated boundaries; rejection preserves handshake and session
  state, not the surrounding queue, clock-record and cookie state;
  installation is connected to the actual exchange, with `beginSession`'s
  allocation failure (`Handshake.lean:273-297`) installing nothing; key
  uniqueness across exchanges is a named contract, not a claim; T5 uses
  allocation identity rather than raw ids or wire indices, requires at
  most one promotion and an earlier accepted confirming receive for every
  responder encryption, allows the previous session in use while a new
  responder key waits, and allows a pending key to be replaced or cleared
  unconfirmed (`Keypair.lean:82-86, 93-116`); undischarged H1 hypotheses
  stay visible in the final claim.
- **F6, medium, resource protection versus missing statistics.** Fixed:
  section 7 separates deferred DoS resistance, with the exposure named
  and not called low consequence, from the missing drop statistics,
  which are an observability defect the tray already holds; the earlier
  reasoning that used the counters' low consequence to defer the bounds
  is withdrawn; tray entries 01 and 02 are cited for what they are, the
  transmit and receive data queues, not a handshake-ring counter defect;
  the routing composition's deferral is conditioned on T2 closing the
  authorization-to-encryption connection.
- **F7, medium, freedom with honest completion.** Fixed: the order is
  advisory, T4 and T5 may precede the send-site inventory, results may be
  split or combined, a second architecture is a diagnostic option rather
  than a prerequisite for a recorded blocker, the counterexample route
  stays; section 5 states what counts as a landed result (an actual
  mirror-path theorem for initialized, reachable executions with explicit
  assumptions, or a classified counterexample or open obligation),
  helper lemmas and imported hypotheses as progress only, stop prefixes
  not erasing earlier events; section 3 adds the two cautions (no
  presumption from earlier artefacts; an attack-excluding premise is a
  restriction on the result); section 8 replaces the completeness
  assertion with the enumeration of what is established, conditional and
  excluded, with campaign 2's results marked as in progress.

Raised for the user: nothing; every finding was either fixed in the
charter or answered above with its reason.

## Paste for Codex#1

> Proof campaign 3 over the WireGuard mirror: six security outcomes, as
> one self-paced grind beside campaign 2. Charter:
> `docs/2026-10-18-charter-proof-campaign-3.md` (read it whole, including
> section 9's dispositions of your own review, then `docs/proofs.md`, the
> two earlier charters and campaign 1's report, campaign 2's report on its
> branch read-only, the conventions note, the reviews, the send and
> handshake audits, tray entries 01 and 02, and the landed designs it
> names). Worktree `.worktrees/proofs-campaign-3`, branch
> `proofs/campaign-3` from `main` on Lean v4.35.0, already created; work
> only there. T1 nonce safety, T2 transmit authorization and conservation,
> T3 authenticated effects and silence, T4 handshake replay resistance,
> T5 responder key confirmation, T6 key retirement: the outcomes are the
> commitment, the decomposition, the models and the order are yours
> (section 4's order is advisory); each landed result has a
> `Statements.lean` whose theorems carry a docstring with the security
> sentence, the gate and the counterexample speedbump passing, a register
> row naming its assumptions and boundaries, a short report. Campaign 1's
> layers are main's: add files there, never edit an existing lemma;
> campaign 2 owns H1 to H6 and its files: read them, never edit them, cite
> H1 by name or state what you need as a named hypothesis that stays
> visible in the final claim. Rule Zero: the mirror is never edited; a
> proof that will not close is a finding with a counterexample, diagnosed
> mirror first on its own evidence, and that is a success. When `main`
> moves, merge and pay the frames without asking; nothing in this charter
> is a prerequisite. Claims over a projection of `WGWorld`, frames in
> their own files, deleted only when the type gives the fact. Keep the
> register row and the report current as you go, stop only when blocked,
> at a finding, or at the campaign's landing. No quotation of the user. No
> merge, no push; `capped` for builds; use the box.
