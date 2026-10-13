# Charter: the WireGuard proof campaign over the mirror

A long-cycle proof assignment for a Codex agent and its subagents: one
self-paced campaign over every WireGuard property of interest, weeks if it
takes weeks, left alone to cook. It follows the form of
[the window-proof charter](2026-10-12-charter-window-proof.md), whose result
is landed and current in [the register](proofs.md); this charter sets six
further results in dependency order and leaves the proof architecture to the
agent.

Provenance: [USER 2026-10-13] "I think we should try giving Codex#2 *all*
of the properties of interest, not just one", as one very long grind
campaign. [AGENT, coordinator] wrote the charter from the property table put
to the user on 2026-10-12.

## 1. What this is, and what it is not

Mirror to property, as before: properties of WireGuard proved over the
executable mirror's own definitions, with whatever Lean models sit in between.
Code to mirror, the simulation against the C, is still not this assignment.

What changed since the first charter: theorems now live on `main`, in the
proof tree `Leanux/Proofs/` with its gate and register ([AGENTS.md](../AGENTS.md),
[docs/proofs.md](proofs.md)). Proofs are a validation channel for the models
beside the differential check. So a Rule Zero finding is a success of this
campaign, not a failure: the mirror follows the kernel, the proof says what
the kernel's state machine really guarantees, and the difference is what the
user wants to know.

## 2. Setup

- The repository's main checkout. Worktree
  `.worktrees/proofs-campaign`, branch `proofs/campaign` from `main`, created
  for you; work only there. Other agents work in other `.worktrees/*`; do not
  touch them, and do not touch `main`.
- Build through `capped -- scripts/in-bundle lake build LeanuxProofs`; the gate
  is `capped -- scripts/in-bundle scripts/proof-gate`. No differential checks,
  no QEMU guests: the mirror is checked against Linux elsewhere; here it is a
  definition.
- Add files only under `Leanux/Proofs/` and `docs/`. The mirror (`Leanux/FS`,
  `Leanux/WG`, `Leanux/Kernel`, `Leanux/Env`, `Leanux/Runner.lean`) stays
  byte-identical to `main` at every commit of yours. Each result is its own
  directory `Leanux/Proofs/WG/<Result>/` with a `Statements.lean`, imported
  from `Leanux/Proofs.lean`, plus a row in the register; material another
  result could use goes in a layer (`Framing`, `Logged`, `WG/Keypairs`, or a
  new one), not in the result. The register's "Adding a result" section is
  the procedure. Form is corrected, never stopped on: a result in the wrong
  place, a missing import or register row, a layer that should have been a
  result or the reverse, is fixed in your next commit when you or the gate
  notice it; the gate is the checker of form, not the judge of the campaign.
- Read first: `AGENTS.md`; [docs/proofs.md](proofs.md) (the layers, the first
  result, lag and repair); [the window-proof conventions](2026-10-13-window-proof-conventions.md)
  (five items, all proof-side or altitude-preserving); the independent
  review's second part ([docs/2026-10-12-spike-window-review.md](2026-10-12-spike-window-review.md),
  what the first result established and how the scheduler loop was framed);
  and the mirror modules each result touches, named below, with the C they
  mirror in `.deps/linux/drivers/net/wireguard/`.

## 3. Rule Zero, restated

The kernel code may contain bugs, and the mirror follows the code.

- The mirror is the authority on what the code does; the WireGuard paper, the
  protocol description and the code's comments are the authority on what it
  is meant to do. When they disagree, that is a finding.
- A statement below that is false of the mirror gets a concrete counterexample
  (a trace and record stream the runner accepts, and the two events or the
  divergence), a judgement whether the code's behaviour is a bug against its
  intent or a design nuance, and then one of: the statement proved under a
  named premise that excludes the trigger and cites the finding, or the
  statement left unproved with the counterexample recorded. The mirror is
  never edited by this campaign, and neither is the kernel; findings go to the
  user through the report.
- Reshaping for a legitimate nuance is allowed and expected: prove the
  property the code has, record the original wording, the proved wording and
  the reason side by side, and keep the meaning.

## 4. The campaign

Six results, in the recommended order. Each names the mirror modules it rests
on, says plainly what it claims, what a counterexample would look like, and
what the gate checks. Names, statement forms, intermediate models and
refinements are yours, as in the first charter.

**R1. Anti-replay uniqueness.** On `Leanux/Proofs/WG/CounterWindow/` and the
ReplayWindow result. Claim: under one keypair lifetime, no wire counter is
accepted twice, and nothing at or below the window's floor (the highest seen
minus `COUNTER_WINDOW_SIZE`) is accepted. S1 already gives the first half as
the acceptance-history statement; R1 states it as a property of the pure
window model's runs and of the mirror through S2, and adds the floor. A
counterexample is two validator calls under one lifetime returning true for
one counter, or a true return for a counter at or below the floor. The
shortest result; start here to learn the tree.

**R2. Lifetime safety.** `Leanux/WG/Types.lean` (`Keypair.internalId`,
`Peer.internalId`, `SkbId`, the `txSkbs`/`rxSkbs` stores), `Keypair.lean`,
`Peer.lean`, `PeerRemove.lean`, `State.lean`. Claim: the mirror never resolves
a dead identity: after a keypair, a peer or a packet id is released, no later
step of any run reads or writes it, and a reused slot is a new identity. The
first result's `WG/Keypairs` lifetime layer is the base; extend it to peers and
the packet store. A counterexample is a run in which a lookup after a release
returns the old object or a write lands on it. R3 and R4 build on this.

**R3. Cryptokey routing.** `Leanux/WG/AllowedIps.lean` (`add`, `insert`,
`removeByPeer`, `findNode`, the node lists), `RxData.lean` (`lookupSrc`,
`decryptPacket`), `Device.lean` (`lookupDst`, the transmit entry). Two halves.
The trie half: longest-prefix lookup agrees with the history of inserts and
removes, including the cleanup `removeByPeer` performs, for both families. The
path halves: a decrypted packet reaches the stack only if its inner source
address is in the sending peer's allowed IPs (the `lookupSrc` check in
`decryptPacket`), and an outgoing packet is handed to a peer only if that peer
owns the longest matching prefix for its destination. Counterexamples: a
lookup answering a peer the history does not justify; a delivered packet whose
inner source resolves to another peer or to none; a transmitted packet routed
to a peer that does not own the destination. This is the defining WireGuard
security property, binding identity to address; the trie half is the bulk of
the cost and is independent of everything else.

**R4. In-order delivery under any recorded schedule.** `Leanux/WG/PtrRing.lean`,
`PrevQueue.lean`, `Receive.lean` and `Send.lean` (the enqueue arms, `-EPIPE`
at `PtrRing.full`), `RxData.lean` (`rxPoll`), `Leanux/Env/Batch.lean`
(`Activation`, `Activation.run`, `schedule`, `dispatch`, `nestedResched`).
Claim: per peer and per keypair, decrypted packets reach the stack in the order
their datagrams were received, for every schedule the records can replay
through the scheduler loop; and a packet is dropped only at an explicit drop
arm (ring full, dead packet, a failed validation), never lost or duplicated in
the pipeline. The schedule is the records; the statement quantifies over every
record stream the loop accepts. Counterexamples: two packets delivered out of
receive order under one keypair; a packet that entered the pipeline and
neither reached the stack nor hit a named drop arm; a packet delivered twice.
One open finding belongs to this result: at the 1024-item ring wrap Linux
drops two items silently where the model predicts one (`w7_ring_wrap`,
`scripts/wg-w7-tier-probe.py`, the W7 tier in
[docs/2026-10-06-w4-w7-transmit-bulk.md](2026-10-06-w4-w7-transmit-bulk.md)).
Characterise the full-ring behaviour exactly; if the mirror and the kernel
disagree there, that is a Rule Zero report with the trace. Prerequisite,
for the drop characterisation only: the W7 full-ring tier's explanation of
the two drops, open mirror work; the ordering and no-loss halves have none.

**R5. Key lifetime enforcement.** `Leanux/WG/Types.lean` (`birthdate`,
`sendingCounter`, the counters), `Send.lean` and `RxData.lean` (the
`REJECT_AFTER_TIME` and `REJECT_AFTER_MESSAGES` checks), `Timers.lean`
(`expiredZeroKeyMaterial`, the retransmit and new-handshake timers),
`Leanux/Kernel/Defs.lean` (virtual time, the timer sections and arm records).
Claim: no data packet is encrypted or decrypted under a keypair older than
`REJECT_AFTER_TIME` or past `REJECT_AFTER_MESSAGES` on its counter, with time
taken from the recorded clock reads; and after the zero-key-material timer
fires, no key material of that peer is used again until a new handshake.
Counterexamples: a transport encrypt or decrypt under a keypair whose recorded
age or counter is past the limit; a use of material after its zeroing.
Prerequisites: review items 7 and 8 (runner budgets versus semantics; timer
operands and wrap), open mirror work on the timer model; the counter half of
the claim has none.

**R6. Flood resistance.** `Leanux/WG/Receive.lean` (`cookieValidatePacket`,
the `hsUnderLoad` decision, the load decay against the recorded clock),
`Cookie.lean`, `Timers.lean` (`expiredRetransmitHandshake`,
`MAX_TIMER_HANDSHAKES`). Claim: while the device is under load, a handshake
initiation without a valid second MAC never gets past the cookie reply (no
handshake state is created or consumed for it); and handshake retransmission
stops after `MAX_TIMER_HANDSHAKES` attempts. Counterexamples: handshake state
created for an initiation that failed the cookie check under load; a
retransmit timer re-armed past the limit. Last, because its value is bounded by
the load model's fidelity (the decay is an exact rule over the recorded clock,
but the under-load threshold is a fixture of the traces).

Dependency order: R1 first; R2 before R3's path halves and before R4; R3's
trie half any time; R5 after R4's scheduler framing exists; R6 last. Work two
at once when one is blocked.

Prerequisites outside this campaign, by result (the two regimes of section 6
turn on these):

| Result | Named prerequisite still to land on `main` |
| --- | --- |
| R1 anti-replay, R2 lifetimes, R3 routing, R6 flood | none |
| R4 delivery | the W7 full-ring tier's explanation of the two drops, for the drop characterisation only |
| R5 key lifetime | review items 7 and 8 on the timer model, for the time half only |

## 5. Success criterion

Per result, all required:

1. Its `Statements.lean` holds every terminal statement as a `theorem` with a
   docstring saying in plain words what it claims; the gate passes (the build,
   every statement on exactly `propext`, `Classical.choice`, `Quot.sound`, no
   forbidden token, the root importing it).
2. The register row: statements in a sentence, directory, this charter, the
   mirror commit the result holds over, status current.
3. One short report per result, appended to `docs/2026-10-13-proof-campaign.md`
   (yours, with a progress section at the top): the architecture (each
   intermediate model, what it abstracts, its refinement theorem), every
   reshaped statement with the original and the reason, every Rule Zero
   finding with its counterexample, the effort, and a ranked list of mirror
   changes that would have made the result routine, each marked
   altitude-preserving or not.

For the campaign: every result current over the `main` commit you end on, or
left with its blocker precisely written after a second architecture has been
tried. A Rule Zero finding with its counterexample and the rest proved is a
success. A reshaped statement that keeps the meaning is a success. A missed
item of the list above is a correction in the next commit, not a failed
result: nothing in this charter is a reason to stop except the user's word.

## 6. Working conditions

- `main` will move under you, in two regimes [USER 2026-10-13], split by
  what the landing is:
  - A landing that is not a prerequisite of any result (seccomp, which lands
    within hours and touches `Leanux/Kernel/Defs.lean`, `Runner.lean`,
    `Syscalls.lean`, `Env.lean` and adds `Leanux/Seccomp/`; docs; harness
    work): merge `main` when it moves, pay the frame contracts and carry on,
    without asking. For a mirror area that never touches a result's state
    they are the trivial projection, one line each, as the epoll carry-over
    showed (883 lines, no statement changed). A result that holds over a
    stale commit is "lagging" in the register until you do.
  - A named prerequisite of a result (the table in section 4: review items 7
    and 8 for R5's time half; the W7 tier's explanation of the two drops for
    R4's drop characterisation): do every part of that result that does not
    depend on it, then pause that part with a one-line "waiting on
    <prerequisite>" in the progress section, and move to the next result.
    Do not guess at the prerequisite's eventual shape, and do not merge
    `main` for it on your own: the user sends a paste when it has landed,
    with the instruction to rebase; merge then and finish the part.
- The conventions note's five items are the house style: properties over a
  small semantic projection, explicit effect contracts for callbacks, history
  on the proof side only, local framing of resumable operations, end-to-end
  relations exported from each result.
- Multi-week. Subagents freely, on branches off `proofs/campaign` or in the
  worktree with one writer at a time; the single-writer rule is the process
  rule the first spike broke and then kept.
- No hard stops. A blocked result gets its blocker written in the progress
  section and the next result starts; come back later. Stop only when the
  criterion is met for every result or when the user says so.
- One commit per proved result (checkpoint commits per intermediate model are
  fine), one short report per result; the user relays. Neutral formal-
  verification framing. Your own commit attribution. No merge, no push.

## 7. What comes after

Each landed result is reviewed independently before it merges, as the first
was. The findings lists feed the mirror's altitude review and the decision
census. When the six are current, the remaining property of interest is the
code-to-mirror simulation, which the user opens separately.

## Paste for Codex#2

> Proof campaign over the WireGuard mirror: six results, in order, as one
> self-paced grind. Charter: `docs/2026-10-13-charter-proof-campaign.md`
> (read it whole, then `docs/proofs.md`, the conventions note, and part 2 of
> the independent review). Worktree `.worktrees/proofs-campaign`, branch
> `proofs/campaign` from `main`, already created; work only there. R1
> anti-replay uniqueness, R2 lifetime safety, R3 cryptokey routing, R4
> in-order delivery under any recorded schedule, R5 key lifetime enforcement,
> R6 flood resistance; each a directory under `Leanux/Proofs/WG/` with a
> `Statements.lean`, the gate passing, a register row, a short report. Rule
> Zero: the mirror is never edited; a proof that will not close is a finding
> with a counterexample, and that is a success. When `main` moves for
> something no result needs (seccomp, docs, harness), merge and pay the
> frames without asking; for a named prerequisite (section 4's table), do the
> independent parts, pause that part with "waiting on <prerequisite>", move
> on, and merge only when I send the paste saying it landed. Mistakes in form
> are yours to correct in the next commit; nothing in the charter is a reason
> to stop. No merge, no push; `capped` for builds.
