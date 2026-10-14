# Charter: proof campaign 2, the handshake and configuration group

A long-cycle proof assignment for a Codex agent and its subagents, in the
form of [the first campaign's charter](2026-10-13-charter-proof-campaign.md):
six further WireGuard results over the mirror, on the handshake, the session
index, endpoint roaming, the configuration surface, progress and the timers'
discipline, left alone to cook. It runs beside campaign 1 (Codex#2,
`proofs/campaign`, the data path and lifetimes) under a disjointness rule
stated in section 6.

Provenance: [USER 2026-10-14] the parallel plan
([docs/2026-10-14-wireguard-parallel-plan.md](2026-10-14-wireguard-parallel-plan.md)):
proof carries are a cost we bear, lanes start as early as their inputs
allow, and campaign 2 starts on the bumped toolchain. [AGENT, coordinator]
wrote the charter from the apex table put to the user on 2026-10-14.

## 1. What this is, and what it is not

Mirror to property, as before: properties of WireGuard proved over the
executable mirror's own definitions, with whatever Lean models sit in
between. Code to mirror is not this assignment. Theorems live in the proof
tree `Leanux/Proofs/` with its gate and register ([AGENTS.md](../AGENTS.md),
[docs/proofs.md](proofs.md)); proofs are a validation channel for the
models, so a Rule Zero finding is a success of this campaign.

## 2. Setup

- Repository `/home/dev/projects/lean-ux-proto`. Worktree
  `.worktrees/proofs-campaign-2`, branch `proofs/campaign-2` from `main`,
  created for you on Lean v4.35.0; work only there. Other agents work in
  other `.worktrees/*`; do not touch them, and do not touch `main`.
- Build through `capped -- scripts/in-bundle lake build LeanuxProofs`; the
  gate is `capped -- scripts/in-bundle scripts/proof-gate`. No differential
  checks, no guests: the mirror is checked against Linux elsewhere; here it
  is a definition.
- Add files only under `Leanux/Proofs/` and `docs/`. The mirror
  (`Leanux/FS`, `Leanux/WG`, `Leanux/Kernel`, `Leanux/Env`,
  `Leanux/Runner.lean`) stays byte-identical to `main` at every commit of
  yours. Each result is its own directory `Leanux/Proofs/WG/<Result>/` with
  a `Statements.lean` imported from `Leanux/Proofs.lean`, plus a row in the
  register; the register's "Adding a result" section is the procedure. Form
  is corrected, never stopped on.
- Read first: `AGENTS.md`; [docs/proofs.md](proofs.md); the first charter
  and the campaign's report `docs/2026-10-13-proof-campaign.md` on
  `proofs/campaign` (read-only, `git show proofs/campaign:<path>`), for the
  layers that exist (`Framing`, `Logged`, `WG/Keypairs` with its `Frames`
  and `Evolution`, `WG/CounterWindow`) and how a result is composed; the
  window-proof conventions; the independent reviews
  (`docs/2026-10-12-spike-window-review.md` both parts,
  `docs/2026-10-13-review-r5-counterexamples.md`); the handshake and
  netlink correspondence audits (`docs/2026-10-13-audit-handshake.md`,
  `docs/2026-10-13-audit-netlink.md`), which walked the modules you will
  reason over line by line against the C; and the mirror modules each
  result names, with the C in `.deps/linux/drivers/net/wireguard/`.

## 3. Rule Zero, restated

Rule Zero, in three clauses [USER 2026-10-14]: (1) the mirror might be
wrong; (2) the kernel might contain bugs; (3) the former is much more likely
than the latter. Every discrepancy is read in that order: a mirror defect
first, settled by the differential check against the kernel and fixed on the
mirror lane; a kernel finding only with positive evidence against the code's
stated intent, written up in the tray; a statement or relation is never bent
to accommodate either.

The kernel code may contain bugs, and the mirror follows the code. The
mirror is the authority on what the code does; the WireGuard paper, the
protocol description and the code's comments are the authority on what it
is meant to do; a disagreement is a finding. A statement below that is
false of the mirror gets a concrete counterexample (a trace and record
stream the runner accepts, and the two events or the divergence), a
judgement whether the code's behaviour is a bug against its intent or a
design nuance, and then one of: the statement proved under a named premise
that excludes the trigger and cites the finding, or the statement left
unproved with the counterexample recorded. The mirror is never edited by
this campaign, and neither is the kernel; findings go to the user through
the report, and a finding that might concern the kernel's maintainers is a
candidate for `docs/upstream-tray/` after independent review. Reshaping for
a legitimate nuance is allowed and expected: prove the property the code
has, record both wordings and the reason, keep the meaning. The user's
prior, stated for campaign 1's R5 and borne out: this code is heavily
audited, so a counterexample is most likely a statement artefact; test that
hypothesis first.

## 4. The campaign

Six results, in the recommended order. Names, statement forms, intermediate
models and refinements are yours.

**H1. Noise session state machine.** `Leanux/WG/Handshake.lean` (the
handshake states, `handshakeState`, the create and consume functions, the
`begin_session` rotation), `Keypair.lean` (the three slots and their
puts), `Types.lean`. Claim: the per-peer handshake state only moves along
the IK pattern's edges as the code implements them (zeroed, created
initiation, consumed initiation, created response, consumed response, and
back to zeroed), each edge taken only by the function that owns it; the
keypair store holds at most one keypair per slot, previous, current and
next, and `begin_session` performs exactly the rotation the C does (the
responder's new keypair to next, the initiator's to current with the old
current to previous, the displaced one put); key confirmation
(`received_with_keypair`) promotes next to current exactly once per
keypair; expiry and clearing leave the slots in the states the C leaves
them. A counterexample is a run in which a state edge is taken by a
function that does not own it, a slot holds two keypairs, or a rotation
differs from the C's.

**H2. Session index uniqueness.** `Peer.lean`'s index hashtable
(`indexInsert`, `indexRemove`, `indexRemoveKeypair`, the collision retry),
`Handshake.lean`'s draws. Claim: no two live sessions, handshake or keypair,
share an index; a lookup by index returns the entry whose identity owns it
or nothing; a draw that collides is retried as the C retries it (the
`s2_index_collision` trace is in the corpus, and the index draw is a
recorded hidden input). A counterexample is a lookup returning an entry
whose identity is not the index's owner, or two live entries under one
index.

**H3. Endpoint roaming on authentication only.** `Handshake.lean`
(`endpointFromSkb`, `setPeerEndpointFromSkb`), its callers in
`Receive.lean` (after the handshake MACs and the AEAD succeed), and the
netlink set. Claim: a peer's endpoint changes only at those callers or at a
netlink set, so an unauthenticated datagram never moves an endpoint, and
the endpoint a packet roams to is that packet's source. A counterexample is
an endpoint change on a path where no MAC or AEAD succeeded.

**H4. Configuration semantics.** `Netlink.lean`, `NetlinkDump.lean`,
`PeerRemove.lean`, `AllowedIps.lean`'s add and remove. Claim: a dump after a
set reflects the set (get-after-set) for the fields the dump carries;
replace-peers, remove, update-only and the allowed-IP removal flag have the
semantics the C gives them; a listen-port, fwmark or private-key change has
exactly the side effects the C performs (the socket re-init, the per-peer
precompute and expiry). A counterexample is a dump disagreeing with the
state the preceding sets established, or a flag producing a state the C
would not.

**H5. Termination and progress.** `Leanux/Env/Batch.lean` (`schedule`,
`Activation.run`, the record-driven measures), `Leanux/Runner.lean`
(`executeTrace`). Claim: every operation terminates on every record stream
the loop accepts (the budgets are now derived from the records and the C's
bounds, review item 7); and progress relative to the records: a unit the
records dispatch runs, a suspended activation the records resume resumes,
and an operation ends with no pending unit unless the run stops
`unsupported` naming it. A counterexample is an accepted run with a pending
unit at its end and no stop, or a loop that does not terminate on an
accepted stream.

**H6. Timer discipline.** `Timers.lean`, `Handshake.lean`'s and
`Send.lean`'s arming sites, `Leanux/Kernel/Defs.lean` (the arm rule with the
caller's recorded read, kinds 310 and 311). Claim: each of a peer's timers
is armed only at its C arming sites with the C's delay, the persistent
keepalive re-arms on every authenticated packet traversal, handshake
retransmission re-arms until the attempt limit as the code counts it (the
19-retry episode campaign 1 found is the measured count), and the zero-key
timer is armed once per session. This is discipline, not firing time:
firing order stays the records' until the timer-wheel extension lands, and
a later result re-poses key lifetime over it.

Dependency order: H1 first; H2 beside it; H3 after H1's state edges; H4 any
time; H5 any time; H6 after H1. Work two at once when one is blocked.

Prerequisites outside this campaign: none for H1 to H6. Landings that will
move `main` under you and are not prerequisites: the handshake ring as a
`PtrRing` (changes the type the Noise invariants frame), the W13 device map,
the timer wheel (which H6 deliberately does not depend on), the rate
limiter's GC and the recorded under-load input, the FIB trie module, and
campaign 1's own landings. All of these are the merge-and-carry regime.

## 5. Success criterion

Per result: its `Statements.lean` holds every terminal statement as a
`theorem` with a docstring in plain words; the gate passes; the register
row; one short report per result appended to
`docs/2026-10-14-proof-campaign-2.md` (yours, a progress section at the
top): the architecture, every reshaped statement with both wordings, every
Rule Zero finding with its counterexample, the effort, and a ranked list of
mirror changes that would have made the result routine, each marked
altitude-preserving or not.

For the campaign: every result current over the `main` commit you end on,
or left with its blocker precisely written after a second architecture has
been tried. A Rule Zero finding with its counterexample and the rest proved
is a success. A reshaped statement that keeps the meaning is a success. A
missed item of the list above is a correction in the next commit, not a
failed result: nothing in this charter is a reason to stop except the
user's word.

## 6. Working conditions

- Two campaigns, one tree. Campaign 1 owns the shared layers it built
  (`Framing`, `Logged`, `WG/Keypairs` and their files): you add new files to
  a shared layer freely, and never edit an existing lemma or definition
  there. When you need a change to an existing shared lemma, write your
  variant inside your result's directory and note it in your report for
  the coordinator to unify at integration. Your results live under
  `Leanux/Proofs/WG/Noise/`, `Index/`, `Roaming/`, `Config/`, `Progress/`,
  `TimerDiscipline/` or names you prefer, disjoint from campaign 1's
  `ReplayWindow`, `AntiReplay`, `LifetimeSafety`, `CryptokeyRouting`,
  `DeliveryOrder`, `KeyLifetime`, `FloodResistance`. Each campaign merges
  `main`; neither merges the other.
- `main` will move under you, in two regimes [USER 2026-10-13]: for a
  landing that is not a prerequisite of any result (everything listed in
  section 4), merge `main` when it moves, pay the frame contracts and carry
  on, without asking; a result that holds over a stale commit is "lagging"
  in the register until you do. For a named prerequisite there is none in
  this charter; if one appears in a later paste, do the independent parts,
  pause that part with "waiting on <prerequisite>", and merge only when the
  user's paste says it landed.
- The conventions note's five items are the house style.
- Multi-week. Subagents freely, on branches off `proofs/campaign-2` or in
  the worktree with one writer at a time; the single-writer rule is the
  process rule the first spike broke and then kept.
- No hard stops. A blocked result gets its blocker written in the progress
  section and the next result starts; come back later. Stop only when the
  criterion is met for every result or when the user says so.
- One commit per proved result (checkpoint commits per intermediate model
  are fine), one short report per result; the user relays. Neutral
  formal-verification framing. Your own commit attribution. No merge, no
  push.

## 7. What comes after

Each landed result is reviewed independently before it merges. Campaign 3,
the data-path group (sender-side counters, conservation, the drop-arm
characterisation, resource bounds, key lifetime over the timer wheel, the
end-to-end routing composition), starts when campaign 1 lands and its
prerequisites are in. When the three campaigns are current, the model layer
covers the apex table's reachable rows; the code-to-mirror simulation is
the user's separate track.

## Paste for Codex#1

> Proof campaign 2 over the WireGuard mirror: six results, in order, as one
> self-paced grind beside campaign 1. Charter:
> `docs/2026-10-14-charter-proof-campaign-2.md` (read it whole, then
> `docs/proofs.md`, the first campaign's charter and report, the conventions
> note, the reviews, and the handshake and netlink audits). Worktree
> `.worktrees/proofs-campaign-2`, branch `proofs/campaign-2` from `main` on
> Lean v4.35.0, already created; work only there. H1 Noise session state
> machine, H2 session index uniqueness, H3 endpoint roaming on
> authentication only, H4 configuration semantics, H5 termination and
> progress, H6 timer discipline; each a directory under `Leanux/Proofs/WG/`
> with a `Statements.lean`, the gate passing, a register row, a short
> report. Campaign 1 owns the shared layers: add files there, never edit an
> existing lemma; your variants live in your results. Rule Zero: the mirror
> is never edited; a proof that will not close is a finding with a
> counterexample, and that is a success, with "statement artefact" the first
> hypothesis to test. When `main` moves (the representation streams, the
> FIB module, campaign 1's landings, none of them prerequisites), merge and
> pay the frames without asking. Mistakes in form are yours to correct in
> the next commit; nothing in the charter is a reason to stop. No merge, no
> push; `capped` for builds.
