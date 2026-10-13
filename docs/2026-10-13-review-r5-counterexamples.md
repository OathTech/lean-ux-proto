# Independent review of R5's Rule Zero counterexamples (`proofs/campaign` at 7fc444d)

[AGENT, independent review 2026-10-13]. Reviewed against the campaign
charter's R5 (`docs/2026-10-13-charter-proof-campaign.md`), the campaign
report's R5 section (`docs/2026-10-13-proof-campaign.md`, working copy in
`.worktrees/proofs-campaign`), the committed proof tree at 7fc444d, the
mirror at that commit, and the C in `.deps/linux` 6.12.110
(`drivers/net/wireguard/receive.c`, `send.c`, `noise.c`, `timers.c`,
`messages.h`). Nothing in Codex's worktree was edited; the proof target was
rebuilt in a detached copy.

Prior carried explicitly [USER 2026-10-13]: "Given that this is very heavily
audited code, it's most likely that this is a false positive (i.e. a proof /
statement artifact)." For each counterexample the first hypothesis tested is
that the charter's statement is stronger than what the implementation claims.

## Verdict

All three are statement artefacts, and the evidence supports that hypothesis
strongly for the first and third and strongly on the kernel side, with a
mirror-domain caveat, for the second. None should become a tray entry; each
stays a documented refinement in the campaign's report, where it already is.

1. **Nonce past the reject limit authenticates before it is rejected.**
   Statement artefact, strong. The C checks the receiver's *stored* counter
   before the AEAD and the packet's *wire* nonce after it, which is the only
   order an AEAD permits; the packet is dropped with no state change. The
   behaviour at nonce R is already in the differential corpus
   (`d2_rx_reject_after_messages`, whose own comment says so), so it is the
   kernel's, not the mirror's. The charter's "past `REJECT_AFTER_MESSAGES` on
   its counter" read as the wire nonce was too strong; read as the stored
   counter it is proved.
2. **A queued transport keepalive encrypted after the key's recorded
   expiry.** Statement artefact, strong on the C (the age check is at staging
   by design, `send.c:356-373`, and the encrypt worker uses the keypair the
   packet carries), with the caveat that the witness's schedule, a crypt
   worker running after a timer that fires at least ten seconds later, is one
   the mirror's environment model admits and Linux does not realise in
   practice; the report says so. The receiver enforces its own age bound
   independently (`receive.c:253`). Not a tray entry; the mirror's timer
   model should note that its worker latency is unbounded by virtual time.
3. **Packet-held key material used after a zero or clear request before a
   new handshake.** Statement artefact, strong. The clear drops the peer's
   three references and removes the index entries (`noise.c:151-177`); a
   queued packet's own reference keeps the struct until it is put, and the
   free is `kfree_sensitive` on the last reference (`noise.c:112-128`). That
   is the documented design (the comment at `noise.c:157-160` reasons about
   exactly this ordering). The witness additionally needs a packet in the
   crypt queue 540 s after the session was derived, which the staging and
   decryption age checks (180 s) make unreachable under any realistic worker
   latency. The charter's "no key material of that peer is used again"
   after the timer fires was stronger than "the peer holds no reference".

The 13 positive contracts are true of the implementation as proved, and they
are the charter's claims cut down to the boundaries the code enforces, with
both wordings recorded in the report; two of them are erasure results rather
than key-lifetime claims (section 3). Axioms: all 13 depend only on
`propext`, `Classical.choice`, `Quot.sound` (section 4).

## 0. The reviewed state

- `proofs/campaign` HEAD 7fc444d (2026-10-13 18:41 UTC), 30 commits since
  its base. Its mirror is byte-identical to `main` 2c7a076: the only diff
  under `Leanux/` outside `Leanux/Proofs/` is the five-line root
  `Leanux/Proofs.lean`. The lakefile adds `LeanuxProofs` as a non-default
  target.
- The campaign worktree is mid-merge with `main` f45bde8 (a `MERGE_HEAD` is
  present; the staged versions of `Env.lean`, `Decision.lean`, `Defs.lean`,
  `Runner.lean`, `WG/Device.lean`, `Handshake.lean`, `Keypair.lean`,
  `Netlink.lean` are byte-identical to `main` f45bde8's). That is the
  "audit carry pending" of the report; nothing in it is reviewed here.
- Of the report's three time witnesses, only two scripts are committed:
  `Replay.lean` (`r5-rx-wire-limit`, nonce exactly R) and
  `ReplayPostClear.lean` (`r5-post-clear-transport`, the "legacy" post-clear
  case). `ReplayDelayed.lean` (`r5-delayed-encryption` and
  `r5-coherent-post-clear`) and the `r5-rx-wire-past-limit` (nonce R+1) case
  exist only in the index and working copy, as does the 176-line extension
  of `docs/proof-campaign-replay.py`. I ran the two committed cases; the
  three uncommitted ones are described from the report and the staged source
  and were not executed here.
- `Statements.lean` at HEAD has 13 theorems; the working copy changes two
  lines of docstring.

## 1. The three counterexamples

### 1.1 A nonce past the reject limit authenticates before it is rejected

**What it is.** `r5-rx-wire-limit`: a five-operation trace, `wg_set`,
`wg_up`, `wg_observe`, the handshake-response `wg_inject`, then a transport
`wg_inject`. Operations 0-3 and their record streams come from the recorded
fixture `CONTENDED_ROAM_CMP` (`evaluator/test_model_replay.py:46`, a Linux
capture of `rx_roam_v6`); operation 4 is operation 4 of the differential
corpus trace `corpus/wireguard/d2_rx_reject_after_messages.json`, a data
packet with wire nonce R = `REJECT_AFTER_MESSAGES` = 18446744073709543486,
with that operation's records reconstructed (the second clock read removed,
since rejection skips receive completion). Reconstructed, not a Linux
capture of this exact splice; but the corpus trace it takes the packet from
is in the `wireguard` suite and is differentially checked. Its generator
comment (`scripts/wg-d2-corpus.py:257-261`) reads: "The receive-side message
limit: REJECT_AFTER_MESSAGES decrypts but counter_validate rejects it;
REJECT_AFTER_MESSAGES − 1 is accepted and delivered, leaving the counter at
REJECT_AFTER_MESSAGES; then counter 5 is DEAD in decrypt_packet (the counter
limit), which invalidates the receiving key." The behaviour was known and
checked against the kernel's branch coverage when the D2 corpus was written.

The two events, re-run here from the committed state (0.9 s):

```
decrypt_packet.counter_limit=0      operands [0, 18446744073709543486]
decrypt_packet.decrypt_failed=0
wg_packet_decrypt_worker.decrypted=1
counter_validate.counter_at_limit=0 operands [0, 18446744073709543487]
counter_validate.theirs_at_limit=1  operands [18446744073709543486, 18446744073709543486]
wg_packet_rx_poll.counter_invalid=1
validator_acceptances 0; original and observed runner JSON equal
```

The uncommitted `r5-rx-wire-past-limit` does the same at R+1 with a packet
the harness's Noise helper generates; I did not run it.

**Mirror against the C.** `decrypt_packet` (`receive.c:242-281`) rejects on
`!receiving.is_valid`, `wg_birthdate_has_expired(receiving.birthdate,
REJECT_AFTER_TIME)` or `receiving_counter.counter >= REJECT_AFTER_MESSAGES`
(:252-257, the stored high-water mark), then reads the packet's nonce (:259)
and runs the AEAD (:278-281). The wire nonce is checked only in
`counter_validate` (:295-303, `their_counter >= REJECT_AFTER_MESSAGES`),
called from `wg_packet_rx_poll` (:461) after decryption; on rejection
`goto next` (:467) skips `wg_packet_consume_data_done` (:473), so no
timer, counter, stats or keypair promotion is touched, and the packet is
freed (:478-481). The mirror's `decryptPacket` (`RxData.lean:63-90`) has the
same guard in the same order (`decKeyInvalid`, `decKeyExpired`,
`decCounterLimit` on the stored counter), then the AEAD; `rxPoll` calls
`counterValidate` afterwards and skips `consumeDataDone` on rejection. Not a
mirror artefact.

### 1.2 A queued transport keepalive encrypted after the key's recorded expiry

**What it is.** `r5-delayed-encryption` (uncommitted): a seven-operation
generated trace with coherent coarse-clock and jiffies records and arm
records. A session is born at 132 s; two nonempty receives set the
keepalive timer's second-fire flag; the first keepalive callback stages a
keepalive at 311 s (age operands `[312000000000, 311000000000]`, admitted
with one second to spare) and re-arms; the second callback at 322 s records
expiry (`[312000000000, 322000000000]`), invalidates sending, stages another
keepalive and queues a handshake; the crypt worker then encrypts and
transmits the packet staged at 311 s under the unchanged key. The mirror's
timer-window rule accepts the second callback long after its due time, and
the crypt worker's run is placed by the records after that callback. The
report says plainly that this "does not establish kernel scheduling
reachability". It is a mirror-domain witness: generated records, never run
on Linux.

**Mirror against the C.** `wg_packet_send_staged_packets` (`send.c:342-394`)
takes a reference to the current keypair (:358), checks `sending.is_valid`
(:363) and `REJECT_AFTER_TIME` on `sending.birthdate` (:365-367), assigns
nonces with `nonce >= REJECT_AFTER_MESSAGES` as a failure (:379-382), stores
the keypair in the packet (:387) and hands the batch to
`wg_packet_create_data` (:388). `wg_packet_encrypt_worker` (:287-309)
encrypts each packet with `PACKET_CB(first)->keypair`; `encrypt_packet`
(:162) makes no age check. The code's own comment at :369-373 says the
nonces are assigned "after we know we have a somewhat valid key". The
mirror's `sendStagedPackets` (`Send.lean:211-258`) has the same checks
(`stagedKeyInvalid`, `stagedBirthdateExpired`, `stagedNonceRejected`) and
hands the packet with its `keypair` id to `createData`; `encryptPacket`
(`Data.lean:70`) reads `k.sending.key` by that id with no age check. Not a
mirror artefact in the code path. The artefact, if any, is in the
environment model: the gap between staging and encryption is a workqueue
latency that Linux measures in microseconds, and the witness makes it
exceed a keepalive interval.

### 1.3 Packet-held key material used after a zero or clear request

**What it is.** `r5-post-clear-transport` (committed): operations 0-3 as in
1.1, then a `wg_observe` whose record stream is synthetic ("deliberately
incoherent coarse/jiffies clocks; no arm records"), ordering a persistent
keepalive timer, the zero-key timer, the clear worker, a crypt scheduler
call, and the send worker. Re-run here from the committed state (2.1 s):
after the clear worker, the peer's three keypair slots are empty, the index
entry is gone, the handshake state is zero, and the one allocated transmit
packet still holds a reference to keypair lifetime 1 (`refcount` 1); the
crypt scheduler then produces the ciphertext under that key and the
transmission releases the last reference, erasing the keypair. The branch
sequence the witness checks:

```
wg_expired_zero_key_material.alive=1
wg_noise_keypair_put.unreference_now=1     (the clear's puts)
wg_noise_keypair_put.kref_put_released=0   (a reference survives)
wg_packet_encrypt_worker.encrypted=1
wg_packet_create_data_done.sent=1
wg_noise_keypair_put.unreference_now=0
wg_noise_keypair_put.kref_put_released=1   (the packet's put frees it)
```

`r5-coherent-post-clear` (uncommitted) is the same shape with coherent
clocks: the zero timer at 132 + 540 = 672 s, the clear worker, then the
crypt worker encrypting a packet staged earlier. Mirror-domain witnesses,
never run on Linux.

**Mirror against the C.** `wg_expired_zero_key_material` (`timers.c:105-120`)
queues `clear_peer_work`; `wg_queued_expired_zero_key_material` (:122-133)
runs `wg_noise_handshake_clear` and `wg_noise_keypairs_clear`.
`wg_noise_keypairs_clear` (`noise.c:151-177`) nulls `next`, `previous`,
`current` in that order and puts each with `unreference_now = true`, which
removes the index-table entry at once (:135-138) and drops the slot's
reference (:139). A packet in the crypt queue holds its own reference from
`wg_noise_keypair_get` at staging; the struct is freed by
`keypair_free_kref` → `call_rcu` → `kfree_sensitive` only when the last
reference is put (:112-128). The comment at :157-160 ("We zero the
next_keypair before zeroing the others, so that
wg_noise_received_with_keypair returns early before subsequent ones are
zeroed") shows the authors reasoning about in-flight users during the clear.
The mirror's `keypairsClear` (`Keypair.lean:98-107`) and `keypairPut`
(:31-41) do the same: the index entry goes on `unreferenceNow`, the store
entry only when `refcount` reaches zero; `expiredZeroKeyMaterial`
(`Timers.lean:60-67`) queues the clear work and
`queuedExpiredZeroKeyMaterial` (`Keypair.lean:136-139`) runs it. Not a
mirror artefact.

## 2. Classification for the upstream tray

The vocabulary is cerberus-lean's (`lem-lean/doc/upstream-tray/`): TRUE
BUG, DESIGN NUANCE, OBSERVABILITY GAP, QUESTION, each with an argument, a
reproducer and verbatim output. A tray entry needs positive evidence that
the behaviour contradicts a guarantee the paper or the code's comments make,
or that the window can be widened from outside.

What the guarantees are. The constants are `messages.h:40-47`:
`REKEY_AFTER_MESSAGES = 2^60`, `REJECT_AFTER_MESSAGES = U64_MAX −
COUNTER_WINDOW_SIZE − 1`, `REKEY_AFTER_TIME = 120`, `REJECT_AFTER_TIME =
180`, and the zero-key timer is armed at `REJECT_AFTER_TIME * 3` after
each session derivation (`timers.c:203-206`). The whitepaper's limits
section says, to my recollection (the sandbox cannot fetch the paper; the
user should check the exact words against section 6 of the paper), that
after Reject-After-Messages messages or Reject-After-Time seconds,
whichever comes first, WireGuard refuses to send or receive further
transport data under the session until a new handshake, and that after
Reject-After-Time × 3 seconds without a new session the session's keys are
zeroed. Those are the guarantees the counterexamples are measured against.

**1.1, the wire nonce.** Not a violation. "Refuse to receive" is
implemented as: refuse to *accept*, and a packet's nonce cannot be trusted
until the AEAD has authenticated it, so authenticate-then-check is the only
order available; the dropped packet changes nothing (section 1.1). A peer
that could produce such a packet would hold the session key and could
equally send under the window; the limit's purpose, keeping the sender's
nonce space from wrapping, is enforced on the sender at staging
(`send.c:379-382`) and on the receiver's stored counter at decryption. No
window to widen. **Classification: DESIGN NUANCE, not a tray entry**, and
really not even a nuance of the implementation, only of the charter's
wording; the differential corpus has documented it since D2.

**1.2, in-flight encryption after expiry.** Not a violation. The check is
at staging by design, and the code says so (`send.c:369-373`); what
completes afterwards is bounded by what was already admitted: at most
`MAX_STAGED_PACKETS` = 128 packets per peer per staging call and the crypt
ring's `MAX_QUEUED_PACKETS` = 1024 per device (`messages.h:52-53`), all with
nonces assigned below R, all completing within the worker's latency. The
receiver checks `REJECT_AFTER_TIME` against its own copy of the key's
birthdate before decrypting (`receive.c:253`), so a packet encrypted after
the sender's expiry is accepted only if the receiver's clock still admits
the key, and the session is already being replaced (the second callback
queued a handshake). Nothing outside the host controls the worker's
latency. **Classification: DESIGN NUANCE, not a tray entry.** The one
thing worth recording is on our side: the mirror's environment model admits
worker latencies unbounded by virtual time, which is what makes the witness
accepted; that belongs to the timer-model review items (7 and 8) the
charter already names, not upstream.

**1.3, use after the zero timer.** Not a violation. The timer's effect is
to drop the peer's references and the index entries so that no *new* use
can find the key; a packet that already holds a reference completes, and
the key is zeroed (`kfree_sensitive`) when that reference is put. That is
the refcount design, documented in the comment at `noise.c:157-160` and in
the `unreference_now` flag's existence. The bound is the same queue depth
and latency as 1.2, and here the window is empty in practice: the zero
timer fires 540 s after derivation, and staging (`send.c:365-367`) and
decryption (`receive.c:253`) have refused the key since 180 s, so a packet
would have to wait in a crypt queue for six minutes. Peer removal, the other
clear path, flushes the crypt workqueue before freeing (`peer.c:101-129`).
**Classification: DESIGN NUANCE, not a tray entry.** There is no
OBSERVABILITY GAP either: the mirror observes the retained reference and
its release exactly, and the C's `kref` makes the same thing observable.

None of the three is a QUESTION: the code's comments answer each.

## 3. The 13 positive contracts

Each was read against the C and the mirror; all are true of the
implementation at the boundary they name, and each docstring says what it
does not claim.

| Theorem | What it states | True of the implementation |
| --- | --- | --- |
| `original_age_test`, `original_age_branch` | the mirror's age test is exactly the signed 64-bit `deadline ≤ now` on the recorded clock, with both operands recorded; equality counts as expired | `wg_birthdate_has_expired` (`timers.h:24-29`) is `(s64)(birthday + seconds·NSEC_PER_SEC) <= (s64)ktime_get_coarse_boottime_ns()`, a signed inclusive compare; yes |
| `receive_guard`, `original_decryption_admission` | a successful decryption used a valid receiving key, an unexpired clock read and a *stored* counter below R | `receive.c:252-257`; yes, and this is the correct reading of the charter's counter clause |
| `original_accepted_wire_nonce` | the validator accepts only wire nonces below R | `receive.c:302-303`; yes |
| `original_zero_timer_preserves_transport_keys` | the zero-key timer callback itself changes no keypair | `timers.c:105-120` only queues work; yes (and the docstring says it asserts nothing about the queued work) |
| `original_staging_erasure`, `original_staging_admissions` | the staging observer is exact, and every observed batch had a valid, unexpired key and nonces below R at submission | `send.c:356-388`; yes; the docstring says it does not cover the later encryption |
| `original_timer_pass_erasure` | the timer-pass observer is exact | an erasure result, not a key-lifetime claim |
| `original_receive_attempt_erasure`, `_admission`, `_coverage`, `_failed_authentication` | every AEAD attempt follows a valid, unexpired key and stored counter below R; exactly one event per attempt; failed tags are recorded | `receive.c:252-281`; yes |

Against the charter's R5 ("no data packet is encrypted or decrypted under a
keypair older than `REJECT_AFTER_TIME` or past `REJECT_AFTER_MESSAGES` on
its counter, with time from the recorded clock reads; and after the
zero-key timer fires, no key material of that peer is used again until a new
handshake"): the proved set is that claim cut at the boundaries the code
enforces, namely admission to decryption, admission to staging, and the
timer's own effect, with the three gaps (wire nonce after AEAD, encryption
after staging, references after the clear) each named as a gap and each
matched by a witness. The report's table records the original wording beside
the proved one for all three clauses. That is the legitimate reshape the
charter's Rule Zero describes ("prove the property the code has, record the
original wording, the proved wording and the reason side by side"). What is
not proved, and the report says so: that the admitted certificates survive to
the encryption (the "transport" theorem), and whole-run coverage of AEAD
attempts. Those would be the follow-on, and they would close the gap only up
to the same granularity, since the C itself has no later check.

Two of the thirteen (`original_staging_erasure`,
`original_timer_pass_erasure`) are observer-exactness results that the
others rest on rather than contracts about key lifetime; counting them as
"positive local contracts" is generous but not wrong.

## 4. Build, gate, axioms, admissions

Detached copy of 7fc444d, `capped -- scripts/in-bundle lake build
LeanuxProofs` from an empty cache: 246 jobs, 8 min 16 s wall, 3.65 GB peak,
exit 0. `scripts/proof-gate` on the same copy: PASS, 206 terminal
statements, axioms within the three, the token scan clean, the root importing
every `Statements.lean`, `LeanuxProofs` not a default target.

The 13 statements, from a scratch file importing only
`Leanux.Proofs.WG.KeyLifetime.Statements`:

```
'Leanux.Proofs.WG.KeyLifetime.original_age_test' depends on axioms: [propext, Classical.choice, Quot.sound]
'Leanux.Proofs.WG.KeyLifetime.original_age_branch' depends on axioms: [propext, Classical.choice, Quot.sound]
'Leanux.Proofs.WG.KeyLifetime.receive_guard' depends on axioms: [propext, Classical.choice, Quot.sound]
'Leanux.Proofs.WG.KeyLifetime.original_decryption_admission' depends on axioms: [propext, Classical.choice, Quot.sound]
'Leanux.Proofs.WG.KeyLifetime.original_accepted_wire_nonce' depends on axioms: [propext, Classical.choice, Quot.sound]
'Leanux.Proofs.WG.KeyLifetime.original_zero_timer_preserves_transport_keys' depends on axioms: [propext, Classical.choice, Quot.sound]
'Leanux.Proofs.WG.KeyLifetime.original_staging_erasure' depends on axioms: [propext, Classical.choice, Quot.sound]
'Leanux.Proofs.WG.KeyLifetime.original_staging_admissions' depends on axioms: [propext, Classical.choice, Quot.sound]
'Leanux.Proofs.WG.KeyLifetime.original_timer_pass_erasure' depends on axioms: [propext, Classical.choice, Quot.sound]
'Leanux.Proofs.WG.KeyLifetime.original_receive_attempt_erasure' depends on axioms: [propext, Classical.choice, Quot.sound]
'Leanux.Proofs.WG.KeyLifetime.original_receive_attempt_admission' depends on axioms: [propext, Classical.choice, Quot.sound]
'Leanux.Proofs.WG.KeyLifetime.original_receive_attempt_coverage' depends on axioms: [propext, Classical.choice, Quot.sound]
'Leanux.Proofs.WG.KeyLifetime.original_receive_failed_authentication' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Token scan over the R5 modules at HEAD (`KeyLifetime/*.lean`,
`KeyTimes/*.lean`, `Logged/TimerPass.lean`, 1,146 lines): no `sorry`,
`admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, `extern`,
`partial`, `opaque`.

The two committed replays reproduce from the committed script and files
(section 1); the three uncommitted ones were not run.

## 5. What should go where

- Report: the three findings stay as the refinements they are, with their
  classification sentence tightened to the one in section 2 (statement
  artefact; the kernel's documented granularity). Add the environment-model
  note of 1.2 (worker latency unbounded by virtual time) to the timer-model
  review items. Commit the three uncommitted witnesses or drop their
  mention; the report currently describes replays the branch does not hold.
- Tray: no entry. The bar for one, a contradicted guarantee or a window an
  outsider can widen, is not met by any of the three, and the first was
  already in the differential corpus with the correct explanation.

## Reproduce

```sh
git worktree add --detach <copy> 7fc444d && cd <copy>
capped -- scripts/in-bundle lake build LeanuxProofs          # 246 jobs
capped -- scripts/in-bundle scripts/proof-gate               # PASS, 206 statements
python3 -B docs/proof-campaign-replay.py r5-rx-wire-limit |
  capped -- scripts/in-bundle lake env lean --run Leanux/Proofs/WG/KeyLifetime/Replay.lean
python3 -B docs/proof-campaign-replay.py r5-post-clear-transport |
  capped -- scripts/in-bundle lake env lean --run Leanux/Proofs/WG/KeyLifetime/ReplayPostClear.lean
git diff --stat 2c7a076 7fc444d -- Leanux ':!Leanux/Proofs'    # Leanux/Proofs.lean only
```
