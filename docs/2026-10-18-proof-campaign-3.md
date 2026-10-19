# WireGuard proof campaign 3

## Progress

[AGENT 2026-10-18] Work begins on `proofs/campaign-3` at `783510e8`, under
the [revised charter](2026-10-18-charter-proof-campaign-3.md). The inherited
proof tree includes campaign 1's GRO carry. No mirror definition or landed
proof has been changed. The source contracts now cover staged nonce allocation, encryption receipts,
cookie egress, native handshake histories and session reference payments. No
complete campaign outcome is claimed.

**C3-F1 is dispositioned as a statement artefact.** The original T6 wording
excluded behavior already represented by R5's coherent initialized replays.
Both reproduce on this branch. [USER 2026-10-18] Resume with the actual TX
admission/RX decryption checks and reference-aware retirement, retaining the
counterexamples. Further wording artefacts are corrected while work continues;
only a blocker, substantive finding, completed campaign or user instruction
stops the work. Validation for the current source-contract checkpoint is recorded below.

| Outcome | Status and remaining obligation |
| --- | --- |
| T1 nonce safety | Open. Initialized native counter reservations are unique through Stop, and admitted counters have injective encoding. Every actual initialized AEAD now has a below-limit nonce and strict earlier reservation evidence. Initialized global packet-identity non-reuse now closes through the same driver and exact causal-journal projection. Each initialized AEAD now has an exclusive allocation-stamped reservation token matching its packet nonce, with no two AEAD occurrences sharing an assigned token. Historical key-material continuity remains open. |
| T2 transmit authorization and conservation | Open. R3 supplies initialized selection-time authorization; packet/material transport to actual encryption and socket emission, and complete TX dispositions, remain to prove. |
| T3 authenticated effects and silence | Open. R6 supplies the cookie gate's local contracts, not causal closure of all delayed effects. |
| T4 handshake replay resistance | Open. Initialized retained-peer timestamps and exchange epochs are derived. Successful sessions have one actual allocation and clear their handshake; refused sessions preserve the whole WireGuard state. Final role-slot residency now follows the actual final-journal session entry. Direct initialized stale-refusal/no-response remains. Named C2 source assumptions stay visible. |
| T5 responder confirmation | Open. Initialized responder selections have earlier successful confirmations, each immediately preceded by a certified replay and earlier AEAD publication in the same journal. Key-allocation continuity and the actual encryption prohibition remain open. |
| T6 key retirement | C3-F1 concerns the literal actual-encryption clause. R5 supplies the admission/attempt checks. New native put/clear contracts prove exact reference payment, retention and final removal; initialized holder accounting and conditional cleanup remain open. |

## C3-F1: invalidation and clearing do not cancel previously admitted encryption

**Claim under examination.** Charter section 4, T6, lines 395–409 at
`783510e8`, prohibits transport encryption using an invalid or expired
sending key and extends that prohibition to retained work. Its introductory
reference to use checks supports a narrower, admission-time interpretation,
but the actual-encryption and retained-work sentences are stronger.

**Mirror-first diagnosis.** The checks occur in
`Leanux/WG/Send.lean:247–261`, before `createData` submits the batch.
`Leanux/WG/Data.lean:74–103` subsequently encrypts using the stored key's
bytes and the packet's assigned nonce, without checking validity, age or
the current sending counter. `keypairsClear` drops slot references and
removes index entries; a packet-held reference can preserve the object
until the TX worker releases it (`Keypair.lean:38–49,105–116` and
`Data.lean:221–249`).

The pristine C has the same boundaries: `send.c:356–388` checks at staging;
`send.c:162–219,287–309` encrypts later; `noise.c:112–177` retains material
until the last reference. Campaign 1's
[R5 report](2026-10-13-proof-campaign.md#r5--key-lifetime-enforcement-rule-zero-findings)
and [independent review](2026-10-13-review-r5-counterexamples.md) already
identify this distinction. The review's claim that Linux cannot realize
the delayed schedule was not adopted by the campaign report: kernel
scheduling reachability remains unestablished.

**Concrete existing recipes.** Both run the original initialized runner,
check its acceptance and equality with the observer, and inspect the
intervening native states in
`Leanux/Proofs/WG/KeyLifetime/ReplayDelayed.lean`. They use generated record
streams with coherent coarse clocks, jiffies and timer-arm records; they
are not Linux captures. The encrypted packet is a transport keepalive
with empty plaintext.

| Recipe | Relevant events and checked outcome |
| --- | --- |
| `r5-delayed-encryption` | Session material is derived at 132 seconds. Nonce 1 is staged at 311 seconds, before the 312-second deadline. At 322 seconds, a later staging attempt invalidates the same sending key. The earlier packet then produces its expected ciphertext before queued handshake work runs. |
| `r5-coherent-post-clear` | The later expiry check occurs at 679 seconds, after the zero timer's bucket becomes due at 678.832 seconds. The clear worker empties the slots and removes the index entry. One queued packet retains the same key allocation and then encrypts; transmission releases the packet and final key reference. |

Reproduction from the campaign worktree:

```sh
set -o pipefail
python3 -B docs/proof-campaign-replay.py r5-delayed-encryption |
  capped -- scripts/in-bundle lake env lean --run Leanux/Proofs/WG/KeyLifetime/ReplayDelayed.lean
python3 -B docs/proof-campaign-replay.py r5-coherent-post-clear |
  capped -- scripts/in-bundle lake env lean --run Leanux/Proofs/WG/KeyLifetime/ReplayDelayed.lean
```

**Classification and disposition.** This is a recurrence of an established
statement mismatch, not a newly discovered Linux security defect. It does
not establish a nonce collision, a bound violation in an encrypted nonce,
or a use after the allocation's final release. No upstream-tray entry is
warranted. The six security outcomes remain unfinished.

The supported contract records validity and age **at the original TX
admission**, retains that historical certificate with the queued packet,
and permits later encryption under its retained reference. RX enforces its
own checks at the decryption attempt. Retirement distinguishes stopping
new admission, unpublishing slots/index entries, and final store removal.
Those distinctions are needed even with a deterministic timer wheel.

The charter now adopts this clarification. Unpublication from slots and the
index is distinct from final removal from the store: a packet reference keeps
the object resident until release. R2's initialized access-safety theorem
supplies the released-allocation discipline; holder/credit contracts are
needed separately for ownership and reference accounting.
A worker-latency premise would restrict the
claim's domain and must be stated explicitly; it is not needed for the
historical admission contract. Adding a recheck to the mirror would alter
the C's control flow and is not an acceptable proof repair.

T1's section 4 sentence at lines 178–180 has a related source-level concern:
limit rejection blocks further admission, but does not cancel earlier
queued packets. The core nonce-safety goal does not require cancellation.
No initialized nonce-limit counterexample has been reproduced here, so this
was a wording concern, not a second established replay finding. The charter
now distinguishes the limit's admission refusal from already admitted work.

## Existing proof boundaries and follow-on work

The following are reused facts, not new campaign-3 results:

- `KeyLifetime.original_staging_admissions` establishes actual historical
  key/clock/allocation certificates and bounded submitted nonces, including
  prefixes before a later Stop. It does not transport those facts to every
  encryption or prove non-reuse of abandoned allocations.
- `KeyLifetime.original_receive_attempt_admission` establishes validity,
  the actual unexpired clock comparison and stored-counter bounds at the
  AEAD boundary, whether or not authentication succeeds. Its counter is
  distinct from the incoming wire nonce.
- `CryptokeyRouting.parsed_initialized_transmit_authorization` establishes
  the original selection-time authorization, not subsequent emission.
- Campaign 2 at `3407cbff` has `Noise.original_slot_rotation`,
  `original_confirmation`, `original_begin_session_ordered`, and
  `original_session_allocation_refusal`, plus
  `original_initialized_driver_tags`,
  `original_initialized_confirmation_order` and
  `original_initialized_confirmation_unique`. The initialized uniqueness
  theorem records completed confirmations even before a later Stop and
  distinguishes allocation identity across device recreation. These remain
  unlanded dependencies; no claim here silently imports or discharges them.
  Tag coverage alone does not establish retained-peer exchange identity.

The next useful proof boundaries are a sending-key projection plus nonce
allocation events (including abandoned attempts), packet allocation and
consumption identity through the existing queue observers, and retained-peer
timestamp/exchange histories. The sending projection must not reuse the RX
window or receiving-key-material projection as if it described sending
state. Existing session receipts and actual receive-poll cuts provide the
starting points for confirmation; a slot invariant alone is insufficient.

The design reading adds three constraints to that follow-on work. AEAD coverage
must include `Env.cryptAhead` as well as ordinary encrypt activations, keeping
copied consistency trials separate from committed execution. B3's retirement
premise must use the actual wheel bucket and dispatch, with deletion and
replacement explicit, rather than a fixed delay bound. T3's cookie exception
bounds a reply per qualifying input; the rate limiter runs only after valid
MAC2, so it does not bound the rate of cookie replies.

Three read-only agents independently inspected the statement/source fit,
nonce architecture, and handshake/confirmation interfaces. Their shared
T6 observation is supported by the source references above; the replay is
the concrete check. No shared proof definition requires alteration for this
finding. Ranked mirror changes: none recommended; adding encryption-time
retirement guards would not preserve the mirror's altitude or C behavior.
An independent review of this documentation checkpoint found no actionable
issue after checking the mirror/replay boundaries, registered recipes,
campaign-2 theorem names and unchanged mirror pin. Its C assessment relied on
the earlier audits; the campaign's source inspection used the pinned pristine C.

## Current proof tranche

[AGENT 2026-10-18] The shared parameterized driver retains actual source cuts
and checked internal event projections; equal native endpoints alone do not
establish chronology. Its history-only theorem now composes through every
native callback, configuration/traffic/lifecycle wrapper and the initialized
Runner, including both timer modes and indexed Stops. State-dependent ownership
and authentication invariants remain separate obligations.

- T1/T2: every initialized execution has duplicate-free actual counter
  reservations, with no entry-invariant or successful-run premise. Local
  allocation/encryption contracts bind packet IDs, material, key reads and
  ciphertext. The combined journal preserves exact nonce and responder
  projections. Its initialized handshake callbacks have strictly earlier
  valid native authentication admissions. Every retained transport socket
  receipt describes the actual packet/peer reads and socket call; cached
  IPv4/IPv6 calls in both loopback modes append at most one datagram bound to
  the observed endpoint, bytes and DS. Receipts survive later Stop. The
  resident packet-origin carrier now transports through allocation, staging,
  native disposal, indexed receive polls, stack replies, NAPI, all workers,
  scheduling, timer/deferred dispatch, all configuration/traffic/lifecycle
  callers and the initialized Runner. Every native worker AEAD receipt has a
  matching allocation in its strict preceding journal prefix, with no incoming
  carrier premise, including later Stop. Every actual AEAD nonce is below the
  message limit and has a strict earlier native reservation with its matching
  allocation-stamped nonce event. The full staging boundary preserves this
  relationship through packet construction and allocation. Normal native
  encryption completion marks the selected head crypted or dead. A historical
  exclusion carrier now proves local worker non-repetition through Stop and
  keeps every old/new encrypted identity out of pending aliases on normal return.
  Native poll transfers an alias; native batch allocation returns IDs separate
  from that history; complete native staged send preserves the exclusion through
  admission, every refusal and cleanup arm. Full outgoing transmission, timers,
  receive completion and RX polls with actual Stack/GRO replies retain the same
  supplied historical exclusion. Full native ingress, decryption with actual NAPI
  placements, handshake receive, queued send/clear drains and timer shutdown now
  preserve it as well. Native peer/device configuration, removal, creation,
  open/down/delete and TX completion now retain the same carrier.
  These cuts retain their incoming carrier until the whole-driver transport
  is proved. Historical key-material continuity, routing linkage, global
  encryption non-reuse, complete egress
  coverage and TX conservation remain open.
- T3: native MAC/Noise refusal and cookie-response contracts retain their
  exact state/egress boundaries. Acceptance receipts precede protocol writes.
  Initialized C1 replay entries have earlier matching AEAD evidence. Native
  RX preparation now transports its packet/stamp publication carrier without
  ownership assumptions. Timer arms and ordered queued-work tickets preserve
  their own earlier callback causes through the local receivers/workers.
  Indexed replay receipts now join the selected crypted packet to a strictly
  earlier native publication; the actual poll supplies confirmation-entry
  provenance. UDP ingress, staging and receive-tail carrier frames are proved.
  Shared Stack/NAPI/worker/scheduler, deferred timer, traffic, configuration,
  lifecycle and initialized Runner composition exposes the actual-hook
  contracts used by concrete Journal specialization. That specialization now
  closes initialized replay-to-AEAD provenance and immediate successful replay
  attribution for every confirmation, including later Stop, without callback or
  reachability premises. Receiving-key allocation continuity and delayed
  timer/work cause inheritance remain open. Exact callback-parametric timer
  sources and candidate scopes now preserve native returns and Stops; a
  candidate label alone does not authorize its effects. Buffered GRO packets
  need their own causal occurrence carrier. The new arm/send-queue callback
  carrier is checked through the outer driver, and concrete Journal instances
  retain earlier initialized claims. Completion effect decoration preserves
  the original lifetime journal. Actual timer scopes close after normal callback
  completion; handshake scope/effect wrappers preserve both matching and unrelated
  journals with visible effect contracts. Causal arm/queue wrappers retain the RX
  carrier under their stated event quietness/history conditions. Owned implementations through
  `6b300d30` are copied without a branch merge. Guarded fixture scopes preserve
  all existing initialized projections. Concrete completion decoration preserves
  the full old completion journal, including Stops. Unified causal metadata
  distinguishes roots from inherited causes and stores only the required
  send-work queue/incarnation projection.
- T4/T5: timestamp and response/session replay contracts remain explicit;
  H1 projections are named dependencies, not silently discharged. Native
  confirmation cuts precede later Stop. Shared responder authorization now
  transports through staging, Stack/GRO polls, NAPI, workers, scheduling,
  timer/deferred work, configuration, traffic and lifecycle. Its initialized
  specialization derives the entry carrier and retains only the named
  `H1ResponderCurrentEdges` dependency. Every responder selection has a prior
  native confirmation. Each such confirmation now joins the same initialized
  Journal's immediate successful replay and earlier AEAD publication. The H1
  premise remains visible; equality of numeric receiving slots is not silently
  strengthened to historical allocation identity. Local strict timestamp
  increases are transported through the initialized driver. The allocation-aware
  retained-peer archive now covers receive/poll/Stack/NAPI, handshake/encryption/
  decryption/TX workers, scheduling, timer actors, configuration, lifecycle and
  the initialized outer Runner, including stopped histories. No entry/archive
  premise remains for retained-peer timestamp advancement. Native handshake
  send/drain callback factors now cover scheduled work, direct configuration
  drains and nested timer/lifecycle drains. Five actual callback receipts identify
  native exchange starts, strictly increasing successful response/install epochs,
  and one allocation per completed session. Their history carrier and H1 edges
  stay visible until initialized exchange transport closes. Actual queued-send
  and complete handshake-receive workers now preserve that carrier under named
  operational C2 tag frames; native session and keepalive callbacks are now
  discharged. Actual data/NAPI, all four workers and scheduling transport the
  same supplied exchange carrier with named native C2 frame dependencies.
  `H1HandshakeTagFrames` cites eleven native declarations at read-only C2 pin
  `5177bd9cbcaffb16dcf8290d88c0e5e0544a0939`; it does not assume initialized
  exchange history, reachability or a security conclusion. Complete exchange identity and prohibition on premature encryption
  remain open. Native deferred work, advance, nested lifecycle drains and
  environment up/down/delete now transport the exchange carrier, with the
  additional named operational C2 free frame. Owned implementations through
  `461b44ea` are copied; fixture-neutral adapter scoped validation passes.
- T6: allocation-stamped credits distinguish slot unpublication from final
  store removal. Native creation, acquisition, clearing, rotation, session
  installation and disposal retain exact reference payments. Actual
  wgXmit/receive entry and completion derive internal loans and release
  funding where proved. Physical and crypt occurrence inventories derive
  selected uniqueness/residency/disjointness; native polls with Stack/GRO
  replies, all four draining workers, scheduling and all fourteen native
  deferred calls transport them with independent C1 allocation freshness.
  Separate wire frames cover non-staging timer and deferred-worker actions.
  Native peer creation and complete peer removal preserve physical ownership;
  removal includes the actual allowed-IP teardown and final payments.
  Configuration, traffic, all syscalls and device lifecycle now transport
  physical ownership; initialized Runner acceptance derives it at each syscall
  entry and the returned world without incoming inventory or per-call premises.
  Current/key compatibility and slot affiliation remain visible where needed.
  Exact shared-driver poll/softirq/tail cuts carry the selected active alias
  under the incoming physical inventory. Native send-work dispatch and complete
  response/session work now preserve the key-holder accounts under stated C1
  funding and slot-affiliation inputs. Both native handshake consumers derive
  the acquired peer credit used by failure cleanup; session publication derives
  slot funding from the actual selected base reference. Actual initialized
  shared-journal poll receipts now carry physical ownership of both their
  native input and transferred active batch, including receipts before Stop.
  Successful handshake consumers retain the actual acquired peer credit through
  staging/keepalive, supplying the final put without an independent funding
  premise. Full native handshake receive, send/clear drains, timer shutdown and
  single/bulk peer removal now transport the exact key account with explicit
  peer funding and slot anchors. Native successful configuration lookup supplies
  the acquired caller credit and base selection. Configured identity supplies
  successful session base funding; native shutdown and peer creation preserve
  holder accounting. Actual lookup and handshake consumption preserve stamped
  slot anchors. The full native peer command now composes lookup or creation,
  both update/removal branches, early cleanup and final caller payment under
  its explicit incoming holder/slot/configured carriers. Initialized key-holder accounting, historical selection uniqueness,
  orphan completeness and conditional retirement progress remain open. Owned
  implementations through `f005e76a` are copied. A separate native slot-liveness
  carrier now covers consumers, publication, send/clear drains, staging, removal,
  receive/handshake, timers, peer/device configuration, lifecycle and data
  completion. It supplies slot affiliation from the stated holder/configuration
  accounts; their initialized closure remains open.

[AGENT 2026-10-19] Historical encryption identities pair a device epoch with
a packet ID. Pending-alias exclusion and allocation-frontier bounds transport
this history through allocation and device recreation; numeric IDs alone would
conflate different device lifetimes. The carrier now closes over the initialized
whole driver; key-material continuity remains a separate obligation.

The register names each module's assumptions and boundaries. All six campaign
outcomes remain open; these are compositional results toward those outcomes.

The nineteenth source checkpoint passes all 1848 proof-build jobs and the
1271-declaration gate across thirteen root modules, with only standard axioms.
All twelve witness recipes and fresh-root kernel replay pass at the default
cap. The model executable build passes 130 jobs, and the unit suite
completes 131 tests with one kernel-build-dependent skip. This checkpoint
adds initialized encryption-identity non-reuse, exact final causal-journal
projection, initialized exchange epochs and concrete session allocation/clearing,
initialized slot protection and stronger native joint holder contracts.
All six outcomes remain open.
No differential guest run is needed for this proof-only checkpoint: the mirror
and its pin are unchanged. The inherited Env deprecation warning remains outside
the permitted edit scope; campaign-owned code has no compiler warning.

A supplemental kernel replay invoked without `--fresh` failed at the 32 GiB
cap and again at 64 GiB (exit 137); neither is a pass. Inspection of the shipped
`LeanChecker.lean` showed that this form launches one task per matching module.
An attempted `--help` likewise had no help behavior and selected the default
module prefix, failing at 32 GiB. Dirty worktrees were snapshotted to project
refs with branches untouched. The bounded replacement command is
`capped -- scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs`, which
replays the root's complete environment in one task. It passed at 32 GiB
over the 1000-job checkpoint (before the subsequent timestamp extensions).

[AGENT 2026-10-19] Use one shared
flushed-send callback through scheduled work, direct drains, timer shutdown,
device down and device deletion. The source audit found nested drains beneath
`timersStop` and lifecycle calls that the earlier observer left opaque; these
are observer coverage gaps, not mirror defects. Namespace pre-exit contains
no send drain. Exact neutral callback equalities retain the preceding driver,
and generic lifecycle history/projection checks pass. Concrete carrier repairs
and complete checkpoint validation pass.
Native exchange receipts now have local start/response/install epoch contracts
with visible H1 edges. Native holder accounting extends through handshake
receive, send/clear drains and single/bulk peer removal. Initialized exchange
and holder closure remain open. Full native staged submission now preserves
the supplied historical encryption exclusion and physical frontier carrier.

[AGENT 2026-10-19] Expose only
native timer arms and send-work appends as shared effect callbacks; keep all
native guard steps fixed. This allows one causal journal without granting a
callback authority over arbitrary native operations. Generic projection and
history contracts and the exact neutral nonce specialization pass. Concrete
carrier adaptation and complete checkpoint validation pass. The owned tranches
add lifetime-preserving effect decoration, shared exchange-driver erasure,
configured-session funding, native shutdown and peer-creation holder contracts.
All six outcomes remain open.

[AGENT 2026-10-19] Close the selected timer scope on normal callback return,
before deferred workers. Preserve an unfinished scope on Stop. This prevents
a prior timer from authorizing unrelated later effects; delayed work must carry
its own queue or wheel cause. Generic projection/history and neutral specialization
pass, with no added premise in the existing initialized claims. Checkpoint
seventeen passes complete validation of this API and the new native
ingress/handshake exclusion, causal handshake, exchange-worker and complete
peer-command holder contracts.
All six outcomes remain open.

[AGENT 2026-10-19] Create local fixture causes only around the native guarded
send callbacks in peer configuration, first-identity configuration, interface
open and explicit transmit calls. Input, stack replies and deferred drains must
inherit their own causes. The generic fixture-scope projection/history proofs
and existing nonce specialization pass; concrete campaign adapters retain
their original initialized signatures and pass complete checkpoint validation. Native historical exclusion now
also covers peer/device removal, creation, opening and configuration. Exchange
closure extends through environment lifecycle calls, and the slot-liveness
carrier covers native staging, handshake receive, peer commands and timers.
The eighteenth checkpoint passes the complete proof gate, all twelve witness
recipes, fresh-root kernel replay, the model build and unit suite. All six outcomes remain
open. A scoped removal proof compiler was deliberately interrupted after a
looping tactic; all seven dirty repository worktrees were snapshotted with
indexes and branches preserved before further development. The corrected
proof passes; this development failure was not a mirror finding.

The nineteenth checkpoint passes complete validation. Native exchange history derives
from initialized execution, with named C2 native edge/configuration/traffic
facts still explicit. Successful sessions now expose the actual singleton
allocation receipt, derived material cut, handshake clearing and unchanged
other-peer tags; false sessions preserve the complete WireGuard state. Direct
initialized stale-refusal/no-response and final role-slot placement remain;
T4 is not yet marked complete. Initialized slot liveness supplies independent peer
protection on the same shared execution; exact key-holder accounting remains
open. The parent joins physical occurrence ownership with the used-encryption
history. Its initialized whole-driver proof now excludes repeated device-epoch/packet
identities, with no supplied physical/history invariant, including both timer
modes and stopped prefixes. Exact old-history projection transports this
claim to the final causal journal. Complete native device configuration and
TX/handshake iterations also preserve their stated joint holder accounts. All 1792 proof-source hashes stayed unchanged through the gate, replay and
speedbump runs. Adopted owned-path pins are T3 `495d5e54`, T4 `5cdbf628` and
T6 `1a6ff935`; no mirror or existing main proof file changed.

[AGENT 2026-10-19] Additional causal and exchange receipts use a new journal
instance of the same source driver. Its exact projection retains the prior
journal's complete states, results, event order and stopped prefixes. This
reuses existing initialized claims without a second execution or another
native frame pass; causal authorization remains a separate obligation.

The twentieth checkpoint passes complete validation. Native staging now assigns each
packet a distinct reservation occurrence after the preceding allocation. The
initialized journal supplies this positional assignment without an entry
premise. Joining it with native reservation non-reuse, packet-allocation
provenance and initialized encryption-identity non-reuse proves that every
actual AEAD has an exclusive allocation-stamped reservation token matching
its packet nonce. Exact projection carries this result to the final causal
journal. Continuity between that historical allocation and the resident AEAD
key remains open. The shared execution also now derives valid native timer-arm
and queued-send receipts with their exact lexical contexts; that result does
not establish causal authorization. Its exchange projection derives initialized
exchange history. Native full RX polling transports its selected key credit
through validation, promotion, GRO callbacks, cleanup and iteration; global
holder initialization remains open. The proof gate passes 1872 jobs and 1277 terminal declarations across thirteen
root modules, with only the three permitted axioms. All twelve witness
recipes and fresh-root kernel replay pass; the model build passes 130 jobs,
and 131 unit tests pass with one configured-kernel skip (22.948 seconds).
All 1816 proof-source hashes stayed unchanged through validation. Adopted child pins are T3 `53106bb6`, T4 `24f59cf8`
and T6 `d7f3d879`. A worker deliberately stopped a slow draft compiler and
replaced the proof search with an existing exact execution lemma. Before
further edits, all twelve registered worktrees were audited and all seven
dirty trees snapshotted, including untracked nonignored files; branches and
normal indexes were preserved. The corrected scoped proof passes. This
development failure is not a mirror finding. All six outcomes remain open.

Checkpoint twenty-one passes complete validation. Every initialized allocation batch
now has one peer and one selected numeric key slot across its packet arguments.
The actual encryption worker preserves head/per-packet peer/key agreement
under explicit physical selection and resident-batch homogeneity. Initialized
transport of that separate resident-batch projection remains open; key-allocation material continuity remains independent.
The actual final-journal session entry now discharges the configured-identity
and current-slot guards for role-selected key residency, under named C2
contracts. Native decrypt and NAPI iterations now carry the joint holder
account through publication, IRQ callbacks and final peer payment. Adopted
owned pins are T4 `a6f7dead`, T6 `16990d1c` and T3 `fd3cf708`.
The native scheduler now transports the joint holder account through all nine
atoms and nested rescheduling without a worker-coverage premise. Native timer,
packet-maintenance and lifetime-observed completion callbacks retain the
delayed-occurrence carrier; its initialized authorization remains open.
The gate passes 1896 jobs and 1282 terminal declarations across thirteen root
modules, with only the three permitted axioms. All twelve witness recipes and
fresh-root kernel replay pass. The model build passes 130 jobs; the unit suite
completes 131 tests with one configured-kernel skip (23.610 seconds). All 1840
proof-source hashes stayed unchanged through validation. Main, the mirror and
existing main proof files remain unchanged.
All six outcomes remain open.

Checkpoint twenty-two passes complete validation. The same actual nonce position now names
its adjacent native reservation receipt. Every native staged-send path preserves
resident-batch peer/key alignment under the explicit physical/alignment entry
carrier. Actual allocation preserves old queued cells and constructs the new
aligned batch; admission and create-data cleanup retain the invariant through
EPIPE, ENOSPC and dead-peer refusal. Initialized transport remains open.
A fixed assignment bank generalizes the positional/token exclusivity theorem
so a stronger material certificate can choose its witnesses consistently. Its
certification remains explicit; the earlier weaker exclusive-assignment result
does not establish reservation-to-AEAD material continuity by itself.
Native existing-key material frames, actual allocation and the full encryption
tail retain conditional material certificates through Stop. Delayed-occurrence
transport now includes the actual handshake/send actors and final TX completion.
Native send/clear work, timer scans and inject/flood/mixed-batch traffic now join
key credits to the exact source-selected peer ledger; outer initialization is
still open. Adopted owned pins are T3 `b6df1e98`, T4 `1914a691`, and T6 `7f5e5c60`.
The proof gate passes 1929 jobs and 1291 terminal declarations across thirteen
root modules, with only the three permitted axioms. All twelve witness recipes
and fresh-root kernel replay pass; the model build passes 130 jobs. The unit
suite completes 131 tests with one configured-kernel skip (22.823 seconds).
All 1873 proof-source hashes stayed unchanged through validation. Main, the
mirror and existing main proof files remain unchanged. No mirror finding is
asserted; all six outcomes remain open.

[AGENT 2026-10-19] Material binding uses one certified assignment bank for each
actual allocation. Independent existential witness choices do not identify the
same reservation across the exclusivity and key-material claims.


Checkpoint twenty-three passes complete validation. Native batch alignment now survives
all five timer callbacks, complete handshake receive/send paths, transmit and
receive admission, authenticated receive completion, Stack/GRO replies, RX
polling, NAPI callbacks, decryption, encryption and TX disposal. These native
contracts retain explicit physical/alignment entry premises; configuration,
lifecycle and initialized driver transport remain open.
The initialized staging-material history supplies one canonical certified
reservation bank. Conditional allocation-entry material retention links a
bound encryption receipt to that same bank with the actual AEAD key stamp and
packet nonce. Initialized resident-material transport remains open.
Delayed-effect transport now covers actual session, staging, keepalive, timer
and handshake/data receive callers; selection receipts expose native queued
membership and timer selection, without claiming initialized causal authority.
Native lifecycle/controls and full or stepped dump syscalls preserve joint key
credit, including cursor aliasing and final reference payment. Adopted owned
pins are T3 `9e77544d`, T4 `4cfce567`, and T6 `b8e1514a`.
The gate passes 1966 proof-build jobs and 1298 terminal declarations across
thirteen root modules, with only the three permitted axioms. All twelve witness
recipes and fresh-root kernel replay pass. The model build passes 130 jobs;
the unit suite completes 131 tests with one configured-kernel skip (23.104
seconds). All 1910 frozen proof-source hashes and all 916 existing main proof
files remain unchanged. Main and the mirror remain unchanged. No mirror
finding is asserted; all six outcomes remain open.

## Validation

Both explicit coherent replays pass: original runner accepted, observer JSON
equal, lifetime 1 and nonce 1 retained, expected ciphertext emitted, and the
post-clear variant's final reference released. These are interpreter checks,
not kernel-proved universal statements.

The model build passes all 130 jobs. The unit suite completes 131 tests with one
skip: computing the selected kernel build's identity when no such build is
configured. These checks used:

```sh
capped -- scripts/in-bundle lake build leanux-model
capped -- scripts/in-bundle python3 -B -m unittest evaluator.test_evaluation evaluator.test_model_replay harness.test_trace harness.test_wg harness.test_linux
```

The inherited `LeanuxProofs` build passes all 973 jobs. The full proof gate
passes all 895 declarations over nine root modules, using only `propext`,
`Classical.choice` and `Quot.sound`; its token, import and target checks pass.
The counterexample speedbump passes all twelve recipes, including both coherent
T6 witnesses and W7's full ring. These checks used:

```sh
capped -- scripts/in-bundle lake build LeanuxProofs
capped -- scripts/in-bundle scripts/proof-gate
capped -- scripts/in-bundle scripts/proof-counterexamples
```

The builds report the existing `Leanux/Env.lean:865` `String.mk` deprecation;
it belongs to the mirror lane and is not suppressed or changed here. The gate
also reports that its nested wrapper lookup cannot find `capped` inside the
bundle's PATH; the outer `capped` invocation still contains the gate and its
children in the capped cgroup. No differential check or guest was run.

At checkpoint `333f3818`, only documentation differed from main. Current work
adds proof files and root imports; the mirror and existing campaign-1 proof
lemmas remain unchanged. The branch is preserved without merging or pushing.

A configuration proof initially exhausted elaboration heartbeats because a
native public-key computation was offered an ambient-only frame. Its existing
whole-WG frame resolves that mismatch without executing the computation during
unification. An ephemeral diagnostic tactic also indexed a binder as an
application and triggered Lean panic diagnostics; all dirty worktrees were
snapshotted before removing the diagnostic. These failed development checks are
not mirror findings or validation passes.
