# Independent review of proof campaign 2's landing

[AGENT, reviewer, Claude Opus 5.5, 2026-10-20]. Verdict: **land with the
named changes** (section 3). No finding blocks the landing. The trust checks
pass, the mirror is untouched, and no theorem I read is false or rests on a
hidden premise. Seven should-fix items need correcting before the merge.
Most are wording: the register rows and the campaign's summary claim more
than several headlines prove. One is a correction to the namespace-pin
finding, which understates the mirror defect it reports. None of the
should-fix items changes a proved statement.

## 0. What was reviewed and how

- Branch `proofs/campaign-2` at `3dbf9a02`. Main `1a69cebb` is its ancestor
  (merged at `6e91c19a`), so the branch is current. I read it through Git
  and built a detached copy, `.worktrees/review-campaign2`, which is now
  removed. I did not enter the campaign's own worktree.
- I read the charter, `AGENTS.md`, the campaign report (its top 250 lines in
  full, and other sections where they were relevant), the retrofit report,
  all three finding documents, the mirror-requests document, the register,
  campaign 1's landing review (as the form), and the mirror on main. I read
  these against the C in `.deps/linux`: `net/core/net_namespace.c`,
  `drivers/net/wireguard/device.c` and `noise.c`, and
  `include/uapi/linux/wireguard.h`. Three read-only helper agents read the
  six `Statements.lean` files in pairs (H1/H3, H2/H4, H5/H6). I checked
  every claim of theirs that I rely on below against the source myself, and
  I rejected one of their conclusions (note N1).
- Commands I ran in the detached copy:

| Check | Command | Result |
| --- | --- | --- |
| Proof gate | `capped -m 64G -- scripts/in-bundle scripts/proof-gate` | `Build completed successfully (3137 jobs)`; `proof gate: PASS (1774 terminal statements, axioms within ['Classical.choice', 'Quot.sound', 'propext'])`; exit 0. Axiom sets: 1,755 × {propext, Classical.choice, Quot.sound}, 7 × {propext, Quot.sound}, 4 × {propext}, 8 none. The build took over an hour on the contended host. My first run failed only check 4, because a scratch audit file I had placed inside the copy imported the proof tree. I moved it out and ran the gate once more on the clean tree; the build was cached, and the result is the one given here. The gate's own axiom step printed `note: capped is not installed`: inside `scripts/in-bundle` its `shutil.which('capped')` finds nothing. The whole run was under my outer `capped`, so this is a box matter |
| Kernel replay | `capped -- scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs` | exit 0, 3m57s, no output |
| Independent axiom audit | a Lean script that imports `Leanux.Proofs`, walks the module data of the six campaign-2 `Statements` modules and runs `collectAxioms` on every non-internal theorem | 881 theorems: Noise 75, Index 162, Roaming 45, Config 219 (the 217 in the source plus two generated `.eq_1` lemmas of local definitions), Progress 280, TimerDiscipline 100. Non-standard: 0. The theorem counts match the register rows and the gate's regex list. |
| Counterexample speedbump | `capped -- scripts/in-bundle scripts/proof-counterexamples` | `proof counterexamples: PASS (12 recipes replayed)`, 39 s. These are campaign 1's recipes only. |
| Campaign-2 recipes (not in the speedbump, finding S4) | `lake env lean Leanux/Proofs/WG/Progress/NamespacePinPending.lean`; `lake env lean --run Leanux/Proofs/WG/Noise/ReplayConfirmationIncarnations.lean < corpus/wireguard/d2_respond_then_data.json`; `python3 -B docs/proof-campaign-2-giveup.py \| lake env lean --run Leanux/Proofs/WG/TimerDiscipline/ReplayInitializedGiveUp.lean` | all exit 0. Pin: `original accepts; final pending netnsCleanup is [12]`. Incarnations: raw slot 0 repeats with stamps 1 and 2, confirmations at operations 3 and 11. Give-up: accepted, 19 retry callbacks, then give-up at callback 20, `keypair_counter` 0 throughout. In addition, the gate's build replays the `#eval`s of `QueueRefill.lean` and `RecordedPending.lean` (both report that the regression passed). |
| Namespace-pin harness domain | `harness.trace.validate_trace` on the finding's JSON | accepted, unchanged |
| Namespace-pin teardown at operation 1 | a scratch `lean --run` driver of `Runner.executeTrace … true` on the alias trace and on the plain `[wg_netns_close]` trace | both report `wg_netns_pre_exit.creator=1` at the `wg_netns_close` operation (finding S3) |
| Mirror untouched | `git log --no-merges 1a69cebb..3dbf9a02 -- <mirror paths>`; for each of the 12 merges, compare its mirror tree with each parent | no non-merge commit touches the mirror; every merge's mirror tree equals one of its parents; the diff against main outside `Leanux/Proofs/` and `docs/` is the root `Leanux/Proofs.lean` only (six imports added) |
| Docstrings | a scan of every terminal theorem in the six `Statements.lean` | 868 of 879 have a docstring; 11 do not (finding S6) |
| Lean options | `git diff 1a69cebb 3dbf9a02 -- Leanux/Proofs \| grep set_option` | see note N3 |

Mirror paths: `Leanux/FS`, `WG`, `Kernel`, `Env`, `Env.lean`, `Runner.lean`,
`Net`, `Seccomp`, `Syscalls.lean`, `Main.lean`. The branch adds 2,210 proof
modules (2,207 in the six result directories, three in `Campaign2/`), 23 docs,
one Python generator, and edits `docs/proofs.md` and `docs/README.md`. It
edits no campaign-1 file.

## 1. The six results as proved

"Hypotheses" means premises beyond the mirror's own definitions. Every
whole-run headline below runs a proof-side instrumented copy of the runner
and proves that it erases exactly to `Runner.executeTrace`: the same JSON or
the same indexed Stop, in both placeholder modes, from the real initial
fixture. Its "final state" is the instrumented copy's world, because
`executeTrace` returns none. That the instrumented copy emits an event at
*every* relevant call is not a theorem. It follows from how the copy is
assembled from callback-parametrised source factorisations, which the
campaign checked by review (note N2).

**H1, Noise state machine.** *Charter: state moves only along the IK edges,
each taken by its owning function; at most one keypair per slot;
`begin_session` rotates exactly as the C does; confirmation promotes next to
current exactly once per keypair; expiry and clearing leave the slots as the
C does.*

- **Edges.** `Noise/Statements.lean:1021` `original_initialized_driver_tags`
  holds for every typed trace, with no hypothesis. It is a genuine
  whole-run ownership result for the handshake state tag. Between events a
  tag only stays or is deleted, and each event is an actual native run of
  the operation that owns the edge. A Stop yields only `ValidHistory`, not
  coverage.
- **One keypair per slot.** This holds by the type: `Slots` is three
  `Option KeypairId` (`Noise/Model.lean:6`). The docstrings say that slots
  may alias each other and need not point at resident keys (`:221–236`).
- **Rotation, confirmation, expiry, clearing.** These are per-function
  contracts, not whole-run claims:
  - `original_slot_rotation` (`:74`) and `original_begin_session_ordered`
    (`:280`);
  - `original_confirmation` (`:85`);
  - `original_expiry_slots` (`:164`);
  - `original_clear_ordered` (`:199`).

  I checked `rotate` and `confirm` (`Model.lean:17–25`) against
  `noise.c:198–260` and `wg_noise_received_with_keypair`. All three arms of
  `add_new_keypair` match, including an initiator demoting a pending next.
- **Exactly once.** `:835` `original_initialized_confirmation_unique` proves
  that successful completed confirmations have pairwise distinct
  `internalId`, the C's `internal_id` stamp, across device recreation and
  before an outer Stop. That is "at most once per allocation", which is the
  right identity (finding F1 in section 2.4). A confirmation inside a consume
  that itself Stops is not in the list.
- **Scope.** The `*_ready_returns` forms carry readiness premises, but each
  has a premise-free `Ensures` partner. The fresh-history theorems
  (`:488`, `:508`) assume `FreshNextBound` and a nine-operation language;
  their docstrings say so.
- **Not proved: whole-run slot discipline.** No theorem says that slot
  fields change only inside `addNewKeypair`, `receivedWithKeypair` and
  `keypairsClear`.

**H2, index uniqueness.** *Charter: no two live sessions share an index;
lookup returns the owner or nothing; a colliding draw is retried as the C
retries it.*

- **Uniqueness.** `Index/Statements.lean:1729`
  `original_initialized_index_tables` gives `UniqueIndices`, `UniqueOwners`
  and `KeypairOwnersBounded` at the normal final endpoint of every
  initialized trace. `:1722` derives `IndexCore` from
  `executeTrace … = .ok json`. There is no invariant premise.
- **Lookup.** `:162` `original_index_lookup` holds in any state; the
  endpoint uniqueness then makes the returned entry the owner.
- **"Excludes unhashed stale fields."** This is a legitimate reading of
  "live", not a narrowing. A local index exists only as an `IndexEntry` in
  `Device.indexTable` (`WG/Types.lean:95–106`). Peers and keypairs carry
  only the remote index.
- **Collision retry.** `:212` `original_index_insert_recorded` is local and
  covers records mode only. The `s2_index_collision` composition (`:229`)
  says it is "not an accepted runner trace". No runner-level theorem says
  that insertions inside an accepted trace consume draws this way.
- **Not covered.** Stopped runs and intermediate boundaries.

**H3, roaming.** *Charter: an endpoint changes only at authenticated
callers or a netlink set; an unauthenticated datagram never moves an
endpoint; the endpoint roamed to is that packet's source.*

- **Final provenance.** `Roaming/Statements.lean:543`
  `original_initialized_latest_endpoint_origins` assumes only that the run
  completes normally. Every present final endpoint then has a latest
  setter: either configuration, or an authenticated packet with no later
  setter for that peer.
- **Authentication.**
  - `:599` `original_initialized_handshake_attempt_authentication`: every
    committed handshake setter attempt emitted by the observer passed its
    MAC and consumer checks.
  - `:554`: every data check is preceded by authentication.
- **Source.** `Authenticated` requires
  `r.endpoint = sourceEndpoint r.source` for the same message whose checks
  passed (`HandshakeOverlayModel.lean:16`), so "that packet's source" is
  proved. The outer address is copied and not AEAD-bound, as in the C. The
  register row says so.
- **"Never moves" is not proved per write.** No theorem says that every
  change of a peer's endpoint between consecutive states happens at an
  authenticated attempt or a netlink set. An unauthenticated move that was
  later moved back would not contradict any headline. The row lists
  "physical-write enumeration" as outside the claim; the status column
  should carry that too (finding S1).

**H4, configuration.** *Charter: get-after-set for the fields the dump
carries; the semantics of replace-peers, remove, update-only and the
allowed-IP removal flag; the side effects of a listen-port, fwmark or
private-key change.*

- **Get-after-set.** `Config/Statements.lean:3701`
  `original_mixed_scalar_getter` and `:2934`
  `original_initialized_mixed_readback`. The getter's static bounds are
  satisfiable by ordinary configurations, and multi-message dumps are
  covered:
  - `MixedPageReady` checks only the first page's head;
  - `headerFits` holds for sane names;
  - the 4096 bound is the mirror's own loop bound.

  The bounds are disclosed. The get-after-set itself is weaker than the
  charter's:
  - **One-directional.** The peer part is `Agrees` (`ScalarExpectationModel.lean:64`):
    `∀ pid c, actual pid = some c → expected pid = some c`, and a `quiet`
    step allows deletion. A peer that should have been born may be missing,
    and a peer that should have been removed is caught only by the separate
    flag-only theorems.
  - **Four tracked fields.** The tracked peer cell is
    `(internalId, psk, keepalive, endpoint)` (`GetterScalarModel.lean:9`).
    Public key, allowed IPs and protocol version are not in the mixed
    get-after-set.
  - **JSON against a proof-side serialiser.** The JSON equals
    `mixedGetterJson d …` of the post-set device; device fields are tied to
    the request by `Fields attrs before d`.
  - **Entry invariant not composed.** `:3701` assumes
    `OwnerConfiguration.ProjectedEntry`, and no headline derives it at an
    initialized endpoint. So set-then-get is a contract from any state
    satisfying the invariant, not a statement about traces. The initialized
    getter (`:2934`) is a separate statement about reading.
- **Replace-peers.** Flag-only (`:2554`, `replacePeersAttrs` sets only
  `WGDEVICE_F_REPLACE_PEERS`), under the assumed `ReplaceCompletion.View.Input`.
- **Remove and update-only.** `:2695` and `:3071`, under `ProjectedEntry`.
- **Allowed-IP removal flag.** Recast as peer `REMOVE_ME` and
  `REPLACE_ALLOWEDIPS` [AGENT 2026-10-15] (report `:7598`). This is correct:
  the oracle's `include/uapi/linux/wireguard.h` (6.12) has no per-allowed-IP
  flag, only `WGPEER_F_*`. It is a statement artefact of the charter, and the
  register row does not record it.
- **Side effects.** Port `:449`, `:462`, `:2804`; fwmark `:436`; private key
  `:2883` with precompute and expiry `:698`, `:709`. These are over source
  factorisations proved equal to the mirror by `rfl`
  (`Config/DeviceSource.lean:92`).

**H5, termination and progress.** *Charter: every operation terminates on
every accepted record stream; a unit the records dispatch runs; a suspended
activation the records resume resumes; an operation ends with no pending
unit unless the run stops `unsupported` naming it.*

- **Termination.** `Progress/Statements.lean:173`
  `original_executeTrace_finite`:
  `Runner.executeTrace trace placeholders = RunnerFinite.executeTrace trace placeholders`
  for every trace. This is not vacuous (note N1), but it is finite
  evaluation, not budget adequacy:
  - every Stop is preserved, including an exhausted budget
    (`RunnerFiniteSource.lean:56–58`);
  - adequacy is proved for the scheduler (`:1626`), the send and timer
    loops (`:1669`, `:1699`) and the batch loop (`:1726`), records mode
    only;
  - `Activation.run`'s budget has no general adequacy result, and the
    report says so.
- **Dispatch and resume.** `:469` `original_turn_dispatch_runs` and `:354`
  `original_turn_resumes`. Both are close to the code's own branches. The
  service result is `:2502` `original_initialized_completed_record_decrease`,
  whose receipt-entry `hidden = some _` premise is disclosed. Its
  propagation to interior entries is unproved and reported as follow-up.
  This is a disclosed gap, not a hidden strengthening.
- **No pending unit at the end.** `:191` `original_accepted_operation_boundaries`
  gives the runner's four literal end-of-operation guards. `pendingWork = []`
  holds only with supplied records, and the docstring says so. In
  placeholder mode the clause is refuted by the namespace-pin trace (section
  2.4, F3).

**H6, timer discipline.** *Charter: each timer is armed only at its C sites
with the C's delay; persistent keepalive re-arms on every authenticated
traversal; handshake retransmission re-arms until the attempt limit (19);
the zero-key timer is armed once per session.*

- **Sites and delays.** Local per-helper contracts:
  - `TimerDiscipline/Statements.lean:84` `original_guarded_arm`, plus
    `:95`, `:105`, `:115` and the recorded variants `:171–260`;
  - hook receipt effects `:985`, `:996`.

  They give the guarded effect with the mirror's constant. There is no
  "only" theorem. That the mirror's arming sites are the C's, with the C's
  constants, is established by inspection and the earlier correspondence
  audits.
- **Keepalive.** Six all-mode headlines cover the six caller sites
  (`:837–922`), in the form "if the hook is reached, it re-arms with the
  guarded effect". That every authenticated traversal reaches the hook
  follows from the journal construction (N2), not from a theorem.
- **Retries.** `:770` `original_timer_actual_retry_block_counts` proves 19
  for qualifying contiguous retry blocks inside one normal `runTimers`
  episode. Interleaved and multi-episode histories are not covered; the
  row says so.
- **Zero-key timer.** `:1232` `original_initialized_session_counts` proves
  one derived hook call per successful session stamp. It proves *at most
  one* completed wheel enqueue per stamp: the guard or an unchanged expiry
  gives zero. `:784` shows give-up cleanup arming the timer with no session.
  So "once per session" is reshaped to "at most one session-derived enqueue
  per stamp, plus a separate give-up cause". That is the right property of
  the code. The status column says "allocation-relative counting" without
  the two wordings.

## 2. Findings

### Blocking

None.

### Should-fix before landing

**S1. The register status columns overstate coverage against the
charter.** Evidence: section 1. The rows call H4 "Current,
complete", H5 "termination … claims closed" and H6 "complete initialized
caller coverage", and say nothing of H1's slot clauses being per-function.
Each narrowing is in the theorems and mostly somewhere in the row's
1,000-word narrative, but not in its status. Settled by one sentence per
row stating the claim and what it does not cover:
- **H1.** Edge ownership is whole-run; slot rotation, confirmation, expiry
  and clearing are per-function contracts; "one keypair per slot" holds by
  the type; "exactly once" is "at most once per allocation stamp".
- **H2.** The collision retry is local and records-mode only.
- **H3.** No per-write theorem; final provenance and the observed attempts
  only.
- **H4.** Peer get-after-set is one-directional over four tracked scalars,
  under an entry invariant not derived at initialized endpoints;
  replace-peers is flag-only; the allowed-IP removal flag is recast,
  because 6.12 has none.
- **H5.** Finite evaluation preserving every Stop, not budget adequacy;
  pending emptiness holds with supplied records only and is refuted without
  them.
- **H6.** No "only at these sites" theorem; keepalive re-arms are
  conditional on the hook being reached; "at most one enqueue per stamp",
  not "once"; caller coverage rests on the journal construction.

**S2. The register's form.**
- **Stale preamble.** The campaign-2 rows sit in a separate "Campaign 2
  working checkpoints" section whose preamble is stale and contradicts the
  rows:
  - "H5–H6 remain in progress" (`docs/proofs.md`, the paragraph before the
    table);
  - "Campaign 2 incorporates documentation-only main 783510e8; its shared
    proof and mirror sources are unchanged from … 77c9b555".
- **Branch-perspective intro.** The edited intro says "this branch also
  incorporates", which is wrong once merged.
- **Rows are logs.** The H5 row ends with "Prior full gate: 3,129 jobs /
  1,771 terminals". The rows carry per-tranche gate counts from several
  dates, in conflict with "Earlier run and recipe counts below are
  historical". `AGENTS.md` rules out run narratives.
- **Missing columns and table entries.** The rows have no Review column,
  and campaign 2 has no entry in the claim-carrying-theorems table that
  campaign 1 uses. Campaign 3 needs to know which declarations are H1's
  claim.

Settled by:
- moving the six rows into the `## Results` table with Charter, Review
  (this document), Mirror commit and a short Status;
- adding six lines to the claim-carrying table. My suggestion, from
  section 1:
  - H1: `:1021`, `:835`, `:74`, `:85`, `:199`;
  - H2: `:1729`, `:162`, `:212`;
  - H3: `:543`, `:599`, `:554`;
  - H4: `:3701`, `:2934`, `:2554`, `:2695`, `:3071`, `:2883`;
  - H5: `:173`, `:191`, `:2502`, and the finding;
  - H6: `:84`, `:1232`, `:770`, `:784`.
- deleting the checkpoint narrative, which the campaign report already
  holds.

**S3. The namespace-pin finding understates the defect. The pending
cleanup is the second symptom; the first is a teardown the C does not
perform.**
- **Evidence.** In the alias trace the mirror runs `Env.netnsCleanup` at
  operation 1 (`wg_netns_close`). That runs `WG.netnsPreExit` (carrier off,
  socket reinit, endpoint-source clear) and the creator namespace's FIB
  teardown, although descriptor 10 still pins the namespace. My scratch run
  of the original `executeTrace … true` reports
  `wg_netns_pre_exit.creator=1` at index 1 of the alias trace, exactly as in
  the plain `[wg_netns_close]` trace. In the C, closing descriptor 9 does
  not reach `__fput`, so `put_net` is not called; nothing queues
  `cleanup_net` (`net_namespace.c:697–703`), so `wg_netns_pre_exit`
  (`device.c:409–428`) does not run at operation 1. Branch labels are a
  compared channel, so this diverges at operation 1, before the pending bit
  at operation 2.
- **Cause.** Two fail-open points in the environment:
  - `Syscalls.netnsClose` (`Syscalls.lean:225–232`) assumes that closing
    `PIN_FD` drops the last reference;
  - `Env.netnsCleanup` (`Env.lean:1127–1131`) runs its section whether or
    not a unit was queued (`if let some u ← peekUnit … then …` skips
    silently).

  The later `close(ref 0)` reaches `FS.fputFinal`, which queues a
  `netnsCleanup` unit (`FS/Fput.lean:68`) that nothing runs. The
  end-of-operation refusal at `Runner.lean:1197–1200` applies only with
  supplied records, so the placeholder run accepts.
- **Classification, against Rule Zero's three clauses.** This is clause 1,
  a mirror (environment) defect. It is the same class as the pending-work
  lifecycle defect fixed at `3f3879e0` (request 4), whose end-of-operation
  refusal was made supplied-mode only.
  - It is not a wording artefact of "pending quiescence": the charter's
    clause is violated literally, and the state is wrong before the pending
    bit appears.
  - It is not a legitimate deferral the mirror inherits from the C. The C
    does defer `cleanup_net` to `netns_wq` after the actual last
    `put_net`, so a pending cleanup after a plain `close` is a real C
    possibility. But the mirror models that deferral only inside
    `wg_netns_close`'s wait, and it runs the teardown at the wrong point.
- **Where it is open.** In supplied mode the differential check would
  refuse this trace noisily: the section-start record for `cleanup_net` is
  absent at operation 1, and the pending guard trips at operation 2. So the
  trust surface is not open. The open path is the `--domain` placeholder
  filter (`Main.lean:43–45`), which admits the trace.
- **What the campaign got right.** The campaign classified the finding
  correctly as an environment request. It did not edit the mirror, it did
  not impose a no-alias premise, and it left the clause refuted.
- **Settled by** amending
  `docs/2026-10-20-proof-campaign-2-namespace-pin.md` and request 5 in
  `docs/2026-10-14-campaign-2-mirror-requests.md` to state:
  - the operation-1 teardown and its branch-label divergence;
  - the silent skip at `Env.lean:1130`;
  - that the check refuses the trace in supplied mode;
  - that a fix either refuses a retained pin alias fail-noisily, or queues
    and runs cleanup at the actual last release, modelling the C's
    asynchronous `cleanup_net`.

  The mirror fix itself belongs to the mirror lane; this review does not
  prescribe it.

**S4. Three campaign-2 recipes are outside every automated check.**
- **Evidence.** `scripts/proof-counterexamples` is unchanged by the branch
  and replays only campaign 1's twelve recipes. Three recipes are neither
  in it nor imported by anything:
  - `Progress/NamespacePinPending.lean`, H5's only counterexample;
  - `Noise/ReplayConfirmationIncarnations.lean`, H1's statement-artefact
    witness;
  - `TimerDiscipline/ReplayInitializedGiveUp.lean`, with
    `docs/proof-campaign-2-giveup.py`.

  (`RecordedPending.lean` and `QueueRefill.lean` are imported by
  `Progress/Statements.lean`, so their `#eval`s run in the gate's build.)
  The helper modules `Progress/AmbientRetentionFrames.lean` and
  `Progress/SuppliedRecordSource.lean` are outside the root's closure, so
  the gate does not build them.
- **Settled by:**
  - adding the three recipes to `RECIPES` in
    `scripts/proof-counterexamples` (cheap; a speedbump, as the script
    already is);
  - either importing the two helpers from a built module or deleting them.
    They claim nothing, and unbuilt proof code rots.

**S5. The charter's per-result report is missing.**
- **Evidence.** Charter section 5 asks for one short report per result:
  - the architecture;
  - every reshaped statement with both wordings;
  - every finding with its counterexample;
  - the effort;
  - a ranked list of mirror changes, each marked altitude-preserving or
    not.

  `docs/2026-10-14-proof-campaign-2.md` is 11,562 lines in 226 dated
  sections. The reshapes are scattered, and several are recorded nowhere
  as "both wordings":
  - H1 raw ID to allocation stamp;
  - H4 allowed-IP flag;
  - H5 pending emptiness to supplied-mode only;
  - H6 "once" to "at most one enqueue per stamp".
- **Settled by** a six-section summary at the top of the report, about a
  screen each, with the reshapes in both wordings. The dated sections can
  stay below it, or move to history.

**S6. Eleven terminal theorems lack docstrings.**
- **Evidence:**
  - `Progress/Statements.lean`: `original_clear_callback_record_suffix`
    and `original_clear_worker_record_decrease`;
  - `TimerDiscipline/Statements.lean`, nine theorems from `:985` to
    `:1058`: `original_initiation_hook_receipt_effect`,
    `original_data_sent_hook_receipt_effect` and the seven
    `*_hook_journal` theorems.

  The charter (section 5) and the register procedure require a plain-words
  docstring on every terminal statement.
- **Settled by** adding them.

**S7. The supplied-pending finding document is stale and its
classification is ambivalent.**
- **Evidence.** The status line of
  `docs/2026-10-19-proof-campaign-2-supplied-pending.md` still reads "a new
  H5 runtime counterexample over main 783510e8". Its "Statement and
  classification" section treats statement artefact as the first
  distinction.
- **What happened instead.** The mirror lane fixed the defect at `3f3879e0`.
  The integration record cites `workqueue.c:3230`, `:3264`, `:2423` and
  `:2322–2325`, and records that the witness supersedes B4's earlier
  decision not to check pending identities. `RecordedPending.lean` now
  checks the corrected refusal. So the finding was a clause-1 mirror
  defect.
- **Correctly classified.** The mirror-requests document's current
  disposition (request 4: "fixed on main `3f3879e0`") is correct.
- **Settled by** a disposition line at the top of the finding document:
  mirror defect, fixed at `3f3879e0`, reproducer retained as a regression.

### Notes

**N1. Termination is not vacuous. I disagree with one helper review here.**
- No mirror function is `partial`. But the mirror uses `while` and `repeat`:
  - `FS/Pipe.lean:257`, `:359`, `:456`, `:550`;
  - `Seccomp/Translate.lean:206`;
  - `WG/Curve25519.lean:32`;
  - `Kernel/Defs.lean:2370`.
- On v4.35 these elaborate to `repeatM`. Logically, `repeatM` is pinned by
  `Classical.choice` to a fixed point of its body, and the compiled code is
  `implemented_by` (`Init/While.lean:48–80`). Proving `executeTrace` equal
  to a finite evaluator therefore shows that those loops are finite on
  every input. That is real content.
- What it does not show is that no budget is exhausted (S1, H5).

**N2. Journal completeness rests on source factorisation and review.**
- Each whole-run observer is the mirror's source with callback slots at
  chosen call sites, and the rest lifted unobserved. For example,
  `TimerDiscipline/EpisodeJournalSyscallSource.lean:71–74` lifts
  `Env.netnsCleanup` and `Env.runSendWorkers` unobserved. Erasure to
  `executeTrace` is proved.
- An omitted hook site would still erase correctly. That no site is omitted
  is the campaign's independent source review ("no omitted nonstructural
  callback"), not a theorem.
- This is the same posture as campaign 1's R2 and R4. It should be named in
  the "does not claim" sentence of the rows that say "complete … coverage"
  (H1, H3, H6), as S1 asks.

**N3. Raised Lean limits exist, but not in the Prefill fix.**
- `Progress/SeccompPrefillFiniteSource.lean`, `RunnerInitialFiniteSource.lean`
  and their claims set only `autoImplicit false`. The Prefill bridge is
  within the default limits, as the investigation report says.
- Elsewhere the branch sets:
  - `maxRecDepth 20000`, `maxHeartbeats 1600000` and
    `synthInstance.maxSize 1024` in `Progress/BatchBacklog.lean`,
    `BatchBacklogModel.lean` and `BatchBacklogAcceptance.lean` (concrete
    `decide +kernel` witnesses);
  - `maxRecDepth 20000` and `maxHeartbeats 1600000` in
    `Progress/QueueRefill.lean`;
  - `maxRecDepth 4096` in three `Index` source and frame files;
  - `maxHeartbeats` between 800000 and 1000000 in about 240 files.
- None is a trust issue. No file on the finite-evaluation path
  (`Progress/*Finite*.lean`) sets a limit. The report's "no limit increase"
  statements are each scoped to their own tranche, and they are accurate.

**N4. Concrete kernel evaluations.** `decide +kernel` (kernel-checked, not
`native_decide`) closes these concrete-trace statements:
- the batch-backlog refusal behind `Progress/Statements.lean:178` and
  `:183`;
- the placeholder regression behind `:879`;
- the dump-room witness `Config/DumpCancellation.lean:29–40`;
- the give-up curve evaluation in `TimerDiscipline/InitializedGiveUpCurveSource.lean`.

`:879`'s docstring says it is a concrete regression. `:178` and `:183` do
not say that they are kernel evaluations of one constructed trace; a phrase
would help.

**N5. Hygiene otherwise clean.**
- No `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`,
  `extern`, `unsafe`, `debug.*` or `opaque` in the campaign's directories.
- The `elab` and `macro` definitions are tactic macros only; there is no
  `addDecl` or environment mutation.
- The fresh kernel replay above covers metaprogram tampering.

**N6. Campaign-3 interaction.** Campaign 3 imports no campaign-2 module. It
names campaign-2 declarations in docstrings and as named-hypothesis
structures, for example
`HandshakeSecurity/ConfirmationH1Initialized.lean` and
`ExchangeH1Placement.lean`.
- **Stable.** Every cited name I extracted exists at `3dbf9a02` (88 names
  across `proofs/campaign-3*`). The files that hold the rotation and
  confirmation facts are byte-identical between the `5177bd9c` that
  campaign 3 pins and `3dbf9a02`:
  - `Noise/SessionSource.lean` (`beginSession_effect`);
  - `RotationSource.lean` (`receivedWithKeypair_effect`);
  - `RotationEffects.lean` (`rotationRun_peer`);
  - `ConfirmationUniqueClaims.lean`, `ConfirmationOrderSource.lean`,
    `ConfirmationOrderLabels.lean` and `ConfirmationLabelSource.lean`;
  - `Index/SessionCoherenceFrames.lean`.
- **One misattribution, on campaign 3's side.** It cites
  `Noise.rotationRun_excluded_key`, but the declaration is
  `Index.rotationRun_excluded_key` (`Index/SessionCoherenceFrames.lean:19`).
- **Support lemmas, not terminals.** Most cited names are not terminal
  statements, so this landing's register does not commit to them. If
  campaign 3 will discharge its H1 hypotheses with them, either campaign 3
  imports them at its own carry, or they are promoted to `Statements` with
  a register mention.

**N7. Retrofit and carries.**
- The thirteen late deletions in the retrofit report (section "Remaining
  peer frames …") are justified by the types. Each deleted leaf framed an
  `AmbientM` action, or a refcount operation polymorphic over a
  `MonadLiftT AmbientM` lift, against kernel state it cannot touch. I
  checked `peekUnit` (`Kernel/Defs.lean:2176`) and `queueDeviceWork`
  (`:2235`).
- The five retired historical cookie claims are refuted, with checked
  counterexamples, not deleted for convenience.
- The 1,321 "retyped or generalized" and 244 "corrected" statements I
  sampled rather than read all. The register says all 258 original
  headline names remain, and the corrections I read (peer release, queued
  handshake, timer deletion) each cite a checked counterexample to the old
  wording.
- The final carry of `1a69cebb` changes no state type and deletes nothing.
  I did not find a retyped statement that changes its claim silently.

**N8. Process.** The report's validation commands set
`LEANUX_QEMU_SLOTS=16`, and the finding recipes copy it. `AGENTS.md` says
to keep 8. No guest ran, so there was no effect, but the recipes should
drop the variable.

**N9. Stale comment.** The module comment at `Index/Statements.lean:110`
("Reachable owner/peer-word coherence remains a separate obligation") is
superseded by `:1737`.

### 2.4 The three findings, under Rule Zero

- **F1, confirmation uniqueness over the raw store key: statement artefact,
  correctly classified.** The raw `KeypairId` is a per-device store
  location: `wgSetup` resets `nextKeypairId` while the world's allocation
  counter survives. The charter's "per keypair" means per allocation, which
  is the C's `internal_id`. The counterexample is reproducible (table
  above), and the corrected statement over `internalId` is proved (`:835`).
  It was not a mirror defect and not a kernel finding.
- **F2, supplied-record pending identity: mirror defect, fixed on the mirror
  lane at `3f3879e0`.** The campaign never edited the mirror; the fix was
  the mirror lane's, under user signoff. The finding document's own wording
  needs the update in S7.
- **F3, namespace pin: mirror (environment) defect, as argued in S3.** It
  is not a wording artefact and not a C deferral the mirror merely inherits.
  It is the environment's unenforced fixture assumption, with the
  supplied-mode-only completion guard as a second fail-open. It is correctly
  routed to the mirror lane as request 5, and should be amended as S3 says.
- **The mirror was never edited** by the campaign (table in section 0).

## 3. Verdict

**Land with the named changes: S1–S7.** No theorem I read is false. The
trust checks pass with standard axioms and a fresh replay. Every premise
beyond the mirror is visible in a signature and, apart from the points in
S1, disclosed. The three findings are routed correctly. The changes are to
what the register and report claim (S1, S2, S5, S7), to one finding's
completeness (S3), and to cheap checks and form (S4, S6). None requires a
new proof. With S1 in place, the register says what was proved.

H5's pending clause remains refuted until the mirror lane settles request
5. That is a lag the register should carry; it does not hold this landing
back.

## 4. What the six results establish about the mirror

These results hold for every typed trace from the real fixture, in both
record modes. Stopped runs keep their exact Stop, and the claims about final
states cover runs that finish normally.
- **Handshake (H1).** The mirror's handshake state moves only along the
  Noise IK edges, by the functions that own them. Its slot rotation,
  confirmation, expiry and clearing match the C's three-way rotation,
  function by function. No allocation's keypair is confirmed twice.
- **Index (H2).** Session indices are unique and lookups find their owner
  at every normal endpoint.
- **Roaming (H3).** Every endpoint a peer ends with was set by
  configuration or by a packet that passed its MAC and AEAD checks, and it
  is that packet's source.
- **Configuration (H4).** The getter reads back the configured device
  fields and the surviving peers' key, keepalive and endpoint, under ordinary
  dump bounds.
- **Progress (H5).** Every operation evaluates finitely, including the
  mirror's `while`-loops. Committed activations consume their records.
- **Timers (H6).** Timers arm with the C's delays at the guarded sites, and
  each session arms the zero-key timer at most once.
- **Not established.** A per-write trace for slots, endpoints or timers;
  get-after-set for peer creation and removal in mixed requests; budget
  adequacy; and coverage proven rather than reviewed. The one place where
  the mirror fails the charter, a retained namespace-pin alias in the
  domain filter, is a mirror defect that the proofs found, which is the
  validation channel working as intended.
