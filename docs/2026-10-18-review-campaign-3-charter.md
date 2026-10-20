# Review of campaign 3's security goals

[AGENT, Codex reviewer, 2026-10-18]. Reviewed charter: `35fed994` on
`task/charter-campaign-3`. Review branch: `task/review-campaign-3`, based on
that commit. [USER 2026-10-18] requested a separate-worktree review focused
on the choice of goals, with freedom in how the campaign achieves them.
The recommendations below are proposals, not adopted charter changes.

**Verdict: retain the five themes, revise their contracts before launch,
and promote key retirement into the security priorities.** Nonce safety,
peer binding, authenticated effects, replay resistance and confirmation
are good targets. Several current clauses instead demand properties the
implementation intentionally does not have. Those clauses would consume
proof effort rediscovering known behavior, without improving security.
The strongest problem in the selection itself is treating key lifetime
as lower consequence and claiming message limits bound its risk.

This is a source and specification review, not a proof or kernel result.
I read the full charter, the relevant mirror definitions and pinned C,
the earlier charters and result register, the send audit, and campaign 2's
checkpoint at `8874ccd6`. The observations below are source-level arguments;
I did not execute new counterexample traces or run the proof gate. No new
kernel defect is claimed. Mirror sources referenced here are identical
between the charter commit and `main` at `77c9b555`.

## Recommended goals

The campaign should commit to these outcomes while leaving theorem
decomposition, intermediate models, instrumentation and work order open.

| Target | Security outcome worth establishing |
| --- | --- |
| T1: nonce safety | Every actual transport encryption uses a uniquely allocated nonce for that sending-key lifetime, below the rejection limit. Failed or abandoned work never makes an allocated nonce reusable. |
| T2: transmit authorization and conservation | Each emitted ciphertext is tied to the intended packet and peer at the relevant selection points, with the correct key and endpoint. Every admitted packet has one accounted disposition, including remaining pending; no packet is duplicated or substituted. |
| T3: authenticated effects and silence | Unaccepted network input cannot authorize session establishment, endpoint learning, transport delivery or protocol responses, apart from explicitly bounded cookie behavior. Delayed sends retain a legitimate causal origin. |
| T4: handshake replay resistance | Replays cannot advance a retained peer's handshake freshness state or install another session for an already consumed exchange. Successful installation and handshake-state clearing are connected to that exchange. |
| T5: responder key confirmation | Every responder encryption under a session has an earlier accepted confirming receive under that session. Confirmation promotes that allocation at most once. |
| Additional priority: key retirement | Age and invalidation checks prevent new unauthorized uses; expiry and lifecycle cleanup retire key material through the actual deferred-work and reference rules, under explicit scheduling assumptions where needed. |

These need not be six directories or six independent projects. Retirement
can extend T1 and T5; conservation can support binding; H1 can supply
rotation facts. A useful ordering is to prioritize nonce safety and peer
binding, then the remaining security outcomes, before exhaustive drop
statistics. This is a recommendation about value, not a prescribed schedule.

## Findings and proposed dispositions

### F1 — High: key retirement is a security goal, not an observability remainder

Charter lines 380–396 classify the deferred group as having no comparable
confidentiality or authentication consequence, then acknowledge a forward
secrecy consequence for key lifetime. The suggested protection from T1's
message bound does not follow: an idle key can remain retained indefinitely
while its message count stays small. Nonce uniqueness also says nothing
about the age at which a captured key can still authenticate traffic.

Time-based rejection and eventual removal are distinct obligations. The
mirror checks age when admitting a staged batch
([Send.lean](../Leanux/WG/Send.lean), lines 244–261), and before decryption
([RxData.lean](../Leanux/WG/RxData.lean), lines 63–76). The zero-key timer
queues work rather than clearing keys itself
([Timers.lean](../Leanux/WG/Timers.lean), lines 57–72). That worker clears
slots; reference release determines when the keypair leaves the store
([Keypair.lean](../Leanux/WG/Keypair.lean), lines 38–49, 105–116, 143–149).
Already admitted work and retained references therefore need an explicit
disposition, not an instantaneous wall-clock erasure promise.

**Recommendation:** include the operational retirement obligation in the
high-priority group. Allow conditional progress under stated clock and
worker assumptions, but separate it from unconditional safety at the use
checks. State exactly what removal from the abstract store establishes;
physical memory zeroization is beyond this mirror's representation. If
retirement remains deferred, describe it as an unresolved security
obligation. WireGuard's whitepaper treats time-based rotation and discarding
old session material as part of its forward-secrecy design
([sections 6.2–6.3](https://www.wireguard.com/papers/wireguard.pdf)).

### F2 — High: T1 confuses nonce allocation, encryption and successful transmission

Charter lines 139–151 require a gapless encrypted sequence starting at zero
and describe the limit arm as a drop. Neither is the right security contract.

Nonces are allocated before queue admission and encryption. Queue refusal
or an allocation failure in `encryptPacket` can consume a nonce without
encrypting a packet. For example, failure before the AEAD call for nonce 0
can leave nonce 1 as the first actual encryption. This is safe nonce use,
not keystream reuse. See [Send.lean](../Leanux/WG/Send.lean), lines 160–174
and 250–269, and [Data.lean](../Leanux/WG/Data.lean), lines 74–98.

On encountering the rejection limit, `sendStagedPackets` invalidates the
sending key and restores the **whole batch** to the staging queue. This
includes earlier packets in the batch that already received provisional
nonces. None of that batch enters encryption under this attempt. The pinned
C explicitly does this at `send.c:369–413`; the mirror does it at
`Send.lean:233–243,261`. It is not a counted disposal of the suffix.

The rekey clause also needs to distinguish requesting an initiation from
queueing a new worker or transmitting a handshake. `keepKeyFresh` reads
the current key at completion; `sendQueuedHandshakeInitiation` can return
because of its time guard, a dead peer or already pending work
(`Data.lean:185–197`, `Send.lean:61–84`). It need not inspect the key that
encrypted an earlier queued batch.

**Recommendation:** target uniqueness, non-reuse after failure, the hard
nonce bound, and the link between the allocated nonce and the actual AEAD
input/header. Treat the allocation sequence and rejection/rekey branches
as supporting contracts. Do not require consecutive encrypted nonces or
unconditional rekey transmission. Crossing the configured bound violates
the usage policy; it is not itself proof that a nonce has already repeated.

### F3 — High: T2 needs pending work, historical selection and actual drop semantics

Charter lines 178–194 require every staged packet to be sent or counted as
dropped. A packet awaiting a handshake is legitimately still staged; a
finite run can end with work pending. Both `out_nokey` and `out_invalid`
restore packets to the queue. Several genuine disposal paths have no
device drop counter. This is already documented in
[tray entry 01](upstream-tray/01-send-ring-full-drops-uncounted.md), including
the queue-refusal and encryption-failure paths. Requiring a counter would
contradict a known behavior without strengthening peer isolation.

There are three distinct selection times: the destination's peer at
`wgXmit`'s lookup, that peer's current key when staging is drained, and its
endpoint when the socket send occurs. The charter's counterexample clause
instead tests destination ownership at send time. Allowed-IPs can change
while a packet waits; that is a different policy. Keepalives have no inner
IP destination and must be bound to the peer selected by their caller.
See [Device.lean](../Leanux/WG/Device.lean), lines 348–388,
`Send.lean:223–230,273–281`, and `Data.lean:170–178`.

**Recommendation:** retain binding as the main security target. Connect
the actual payload, lookup occurrence, peer identity, key allocation and
endpoint read; reuse R3's outgoing authorization where applicable. For
conservation, allow one pending logical obligation (possibly represented
in multiple queues) or one terminal outcome.
Distinguish socket handoff, socket failure and successful emission, so a
failed socket call does not count twice. Name actual disposal arms and
their actual statistics, including an explicit absence of a counter.
Eventual completion requires extra progress assumptions and can be separate.

The security explanation also needs calibration: encrypting plaintext
under an unintended peer's key can disclose it to that peer. Sending
correctly encrypted bytes to the wrong endpoint does not, by itself,
disclose plaintext. Duplicating a datagram is not a second encryption and
does not by itself reuse a nonce for a different plaintext.

### F4 — High: T3 needs a meaningful authentication boundary and causal roots

The goal is valuable, but the equivalence at charter lines 219–235 is not
valid as written. No protocol response and no state mutation are different
properties, and the listed authentication cases omit cookie consumption.

The mirror already contains intended effects that the literal wording
would reject:

- A consumed cookie updates `cookie`, its birthdate, validity and
  `haveSentMac1` (`Receive.lean:80–99`). It is a separately checked control
  message, not a Noise handshake or an authenticated transport packet.
- Cookie-secret rotation and rate-limit bookkeeping precede successful
  Noise consumption (`Receive.lean:123–129,201–216,292–320`).
- A packet naming an expired receiving key can mark that key invalid
  before the AEAD check (`RxData.lean:63–86`).
- Input occupies queues and changes reference/accounting state before
  authentication; rejection does not imply equality of the whole world.

Conversely, successful AEAD decryption alone is too weak an authorization
event for transport-triggered effects. The receive path checks the replay
window before endpoint learning, confirmation and timer activity
(`RxData.lean:589–595,290–297`). Inner source authorization occurs later;
a confirmed packet need not be delivered to the IP stack to confirm a key.
These acceptance stages should stay distinct.

The causal roots also need tightening. Packet injection is itself a fixture
operation; treating every fixture operation as authorization makes silence
vacuous. Treating any timer the device armed as an independent trusted
cause can hide a delayed response armed by rejected traffic.

**Recommendation:** define trusted local configuration/application actions,
accepted handshake/transport events, and cookie control events separately.
Follow timer and queued-work causality back to those roots. State which
security-relevant effects rejected input cannot authorize, and name the
permitted bookkeeping and expiry effects narrowly. The proof may use an
event invariant, a projection or another architecture; the charter need
not choose one.

For the cookie exception, target at most one fixed-format reply to the
input source, under the actual load/MAC conditions, with no session
installation. Its 64-byte payload is smaller than either handshake input
(148 or 92 bytes; `Receive.lean:45–60,249–260`). That addresses packet and
payload amplification for this exception; it is not a CPU-exhaustion proof.
MAC1 is derived from a public key, so it is not configured-peer identity
authentication. Qualify scanner invisibility accordingly
([WireGuard whitepaper, section 5.3](https://www.wireguard.com/papers/wireguard.pdf)).

### F5 — Medium: T4 and T5 should identify exchange and allocation lifetimes

Both are good goals. The missing precision is which identity survives
retries, replacement, peer removal and device recreation.

T4's timestamp history belongs to retained peer state, not permanently to
a static-key byte string. `handshakeZero` preserves `latestTimestamp`
(`Peer.lean:232–236`), while a newly created peer starts with a zero
timestamp (`Types.lean:320`). The charter should cover replay rejection
within that retained lifetime and explicitly describe reset boundaries.
It should preserve handshake/session state on rejection, not all queue,
clock-record and cookie state surrounding the check.

For responses, connect at-most-once consumption and installation to an
actual initiation occurrence. A successful `beginSession` allocates a
keypair and clears the handshake (`Handshake.lean:273–297`), but allocation
failure returns false. An observed handshake exchange does not guarantee
successful installation. One allocation also does not prove unique key
bytes across exchanges: cryptographic derivation and randomness assumptions
must be named separately.

T5 should require **at most one** promotion, and an earlier accepted
confirming receive for every responder encryption. A pending responder key
can be replaced or cleared without ever being confirmed
(`Keypair.lean:82–86,93–116`). Confirmation must include transport replay
acceptance; an old key remaining current while a new responder key waits
is permitted. The protocol explicitly permits use of the previous session
while waiting for confirmation
([Protocol & Cryptography](https://www.wireguard.com/protocol/)).

Use allocation/exchange identity, not raw store or wire index alone.
Campaign 2's checkpoint at `8874ccd6` already reports repeated raw keypair
IDs across initialized device recreations and leaves broader H1 closure
open. T5's added value is connecting the real receive authentication path
to every real responder encryption, beyond H1's local slot transitions.
Named H1 hypotheses are reasonable during development; an undischarged
hypothesis must remain visible in the final claim.

### F6 — Medium: resource protection and missing drop statistics are different priorities

The deferral at charter lines 397–408 conflates the absence of counters
with bounded resource consumption. Missing statistics can be primarily
an observability defect; a failure to bound attacker-controlled memory
or expensive work is an availability/security problem. Cookie gating is
one part of that defense, not a proof of the whole defense. The receive
queues fill before transport authentication, as
[tray entry 02](upstream-tray/02-receive-queue-full-drops-uncounted.md)
already explains. Tray entries 01 and 02 concern transmit and receive data
queues, not a demonstrated handshake-ring counter defect.

**Recommendation:** deferring a separate resource proof is defensible for
scope, but describe it as deferred DoS resistance, with the remaining
exposure named. Do not use the low consequence of missing counters as the
reason to defer capacity bounds. Likewise, routing composition can wait,
provided T2 actually closes the authorization-to-encryption connection;
composition failures are not inherently harmless completeness issues.

### F7 — Medium: preserve implementation freedom, but keep completion honest

The opening flexibility is good. The charter can give much more freedom
without weakening its outcomes: make the dependency order advisory, permit
T4/T5 work before the send-site inventory, and let the campaign split or
combine results. Make trying another architecture a diagnostic option,
rather than a prerequisite to recording a well-understood blocker; retain
the existing route for a counterexample to settle a false statement.
Ownership boundaries and the restriction on editing the mirror remain
useful; a necessary shared-layer improvement can be proposed separately.

Retain Rule Zero's mirror-first investigation. Earlier statement artifacts
should not create a presumption that another false security property is
harmless. Correct the known wording errors before launch and diagnose new
discrepancies on their evidence. A premise that excludes an actual attack is a
restriction on the result, not preservation of the original security goal.

Completion should mean an actual mirror-path result for initialized,
reachable executions, with explicit assumptions and boundaries, or a
precisely classified counterexample/open obligation. Local helper lemmas
and imported hypotheses are useful progress, but do not alone establish
the security headline. Failure/Stop prefixes must not erase earlier
security-relevant events. This is a statement of the intended claim, not
a demand for a particular observer or a new audit framework.

Finally, replace the completeness assertion at lines 420–424 with an
enumeration of what the campaigns establish and what remains conditional
or excluded. The five goals are valuable operational obligations under
crypto contracts; proving them does not establish all sequential protocol
security, cryptographic forward secrecy, or global availability. Campaign
2's named results also remain in progress at the inspected checkpoint.

## Proposed launch disposition

Revise T1–T3's known mismatches, clarify lifetime identity for T4/T5, and
resolve the priority of retirement before launching the long campaign.
Keep proof architecture and scheduling discretionary. No new machinery
or exhaustive checklist is needed: the short goal table above, explicit
security assumptions, and honest dispositions would make a stronger charter.

This review does not approve landing the charter, advancing `main`, or
integrating the separate campaign-1 carry. Those require the user's
signoff for their concrete changes.
