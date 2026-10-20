# Independent review of proof campaign 3's landing

[AGENT, reviewer, Claude Opus 5.5, 2026-10-20]. Verdict: **land with the
named changes** (section 3). One finding blocks landing until it is fixed or
the user disposes of it (B1: the campaign says no resource limit was raised,
yet it raises them file-wide in about a quarter of its files). The trust
checks pass on the head I checked: the gate, the axioms, the fresh kernel
replay and the counterexample recipes. The mirror and the earlier proof
layers are untouched. No theorem I read is false. The should-fix items are
about what the register and the report say the theorems give. In several
places they say more than the types carry: T2's conservation, the T4 and T5
hypotheses, T6's packaging, and the narrowed T1 and T6 targets.

## 0. What was reviewed and how

- **What I reviewed.** Branch `proofs/campaign-3` at `7b8994b1`, which is
  linear on main `eba3c2b6` (262 commits, no merges). I judged it on that
  base, as asked. Main has since moved to `218d3ffd`, and all six outcomes
  lag that commit; the campaign records this itself. I checked it out as a
  detached copy, `.worktrees/review-c3-copy`, and removed the copy
  afterwards. I did not enter the campaign's own worktree.
- **What I read.**
  - The charter, and its diff over the campaign.
  - `AGENTS.md`.
  - The campaign report: the progress section, the rebase notes, C3-F1,
    proof structure, and parts of the validation log.
  - The register's campaign-3 section and its Results table.
  - The four campaign-internal review notes, only to see who wrote them and
    what they cover.
  - The four `Statements.lean` files, in the parts relevant to each target.
- **How I used helper agents.** Four read-only helper agents read the
  statements:
  - T1 and T2;
  - T3, T4 and T5;
  - T6 and C3-F1;
  - how faithful and complete the proof-tree journals are.

  I checked myself every claim of theirs I rely on below. The checks were
  the `H1*` packages and that none of them is ever constructed; T5's
  signature; `concreteChildren` and `concrete_children`; T3's `Protected`
  set; the fields of T6's `Outcome`; and the conservation headline's
  implicit binders.

| Check | Command (in the detached copy) | Result |
| --- | --- | --- |
| Proof gate | `capped -- scripts/in-bundle scripts/proof-gate` | `Build completed successfully (6677 jobs)`; `proof gate: PASS (2448 terminal statements, axioms within ['Classical.choice', 'Quot.sound', 'propext'])`; exit 0; no `warning` line in the log. Printed axiom sets: 2,427 × the standard three, 9 × {propext, Quot.sound}, 4 × {propext}; the rest print no axioms. All 674 campaign-3 terminal theorems are among them. The build took over an hour on the contended host. The gate's inner step printed `capped is not installed` (the bundle's PATH); the whole run was under my outer `capped`. This is a box matter, as in the campaign-2 review. |
| Headline axioms | a scratch file importing `Leanux.Proofs`, with `#print axioms` on `initialized_nonce_safety`, `initialized_transmit_source_conservation`, `transmit_source_children_are_closed`, `original_transmit_refusal_charged_once`, `initialized_silence_security_outcome`, `initialized_responder_confirmation_discipline`, `native_nonce_rejection_invalidates_and_restores`, `reference_aware_retirement_outcome`, plus `#check` of two signatures | each depends on the standard three only |
| Kernel replay | `capped -- scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs` | exit 0, 7m24s, no output |
| Counterexample speedbump | `capped -- scripts/in-bundle scripts/proof-counterexamples` | `proof counterexamples: PASS (15 recipes replayed)`, 58 s, including `r5-delayed-encryption` and `r5-coherent-post-clear`, the witnesses for C3-F1 |
| Mirror untouched | `git log eba3c2b6..7b8994b1 -- <mirror paths, scripts, harness, evaluator, kernel, corpus, lakefile, toolchain>`; `git diff --name-only --diff-filter=MDR` | no commit touches them. The only modified files are `Leanux/Proofs.lean` (four imports), the charter, `docs/README.md` and `docs/proofs.md`. Every proof file is an addition under the four new result directories, so no landed lemma of campaign 1 or 2 was edited. |
| Gate scanner coverage | the gate's declaration regex compared with every declaration form in the four `Statements.lean` | no `private`, `protected`, attributed or indented declaration escapes it |
| Docstrings | a scan of every top-level declaration in the four `Statements.lean` | 674 of 674 have a docstring (all theorems). T6's headline is a structure instance whose eighteen fields have none (S4). |
| Resource options | `grep` over the four result directories | finding B1 |

## 1. Findings

### Blocking

**B1. The campaign raises resource limits throughout, and says it does not.**
- **What the documents claim.** The report (`2026-10-18-proof-campaign-3.md:12`)
  and the register (`proofs.md:17`) both state that no resource limit was
  raised. The validation log repeats "default limits" for later tranches.
- **What the branch contains.**
  - 906 `set_option maxHeartbeats` lines, 885 of them file-wide, at values
    from 200,000 to 2,000,000. They are in 898 of the 3,545 new files.
  - 433 file-wide `set_option maxRecDepth 4096`.
  - Only 21 are scoped with `in`. None carries a stated reason.
  - They were added across 91 commits. The late tranches I sampled do use
    default limits, which may be what the sentence meant, but the
    campaign-level claim is false.
- **Rules it breaks.** The standing practice allows raising a limit only as
  a last resort, scoped to one declaration, with the reason beside it, and
  listed in the working-practices doc if it must stay.
- **Why it blocks.** It is a false statement on the claim surface, and it
  breaks a standing rule at scale.
- **Required change.** Correct the sentence in both places. Then put the
  disposition to the user. Either scope each raise to its declaration with
  a reason (a large but mechanical follow-on), or record a narrowly worded,
  user-approved project exception for the generated source-closure layers.
  I recommend the second only together with a follow-on to shrink the set.

### Should-fix before landing

**S1. T4 and T5 rest on campaign-2 hypothesis packages that are never inhabited, although H1 has landed.**
- **Where the premises are.** The final T4 theorems take
  `H1DriverSourceFacts`, `H1ConfigurationTagFrames` and `H1TrafficTagFrames`;
  the session theorem also takes `H1ResponderCurrentEdges` and
  `H1SessionPlacement`. T5's headline,
  `initialized_responder_confirmation_discipline`, takes `H1DriverFrames`
  and `H1ResponderCurrentEdges` (`#check` above).
- **What they contain.** These are `Prop` structures (26 `structure H1…`
  declarations in `HandshakeSecurity/`). Their fields are claims about the
  concrete mirror functions over every world, roughly fifty leaf facts.
- **They are never constructed.** No value of any of them is built anywhere
  in the tree. So the theorems' non-vacuity has never been checked inside
  the project.
- **What the charter asked.** Cite H1's theorems if they have landed. They
  had: `Noise/` is in this tree and H1 is current at `1f766662`.
- **What the documents say instead.** The register and the progress table
  call T4 and T5 "Complete and validated". They describe the premises as
  "named C2 source assumptions" or "local operational assumptions". The
  register names `H1ResponseEdges` and `H1SessionEffects` at `5177bd9c`,
  but the final theorems take other packages, and the frame docstrings cite
  `7ff94e48`.
- **Required change.** The rows must say that T4 and T5 are conditional;
  name every package each headline takes; say that none has been
  inhabited; and fix the pins.
- **Recommended follow-on.** Instantiate the packages from `Noise/`. This is
  the most valuable one: it either removes the premises or shows where the
  campaign's views differ from campaign 2's.

**S2. T2 conservation holds at the points the proof tree declares; that those points cover the mirror rests on an audit.**
- **What the headline says.** `initialized_transmit_source_conservation`
  gives `AccountOrRecords` at every `SourcePoint`.
  - `SourcePoint` is `Runner.Points.Point concreteChildren …`: the entries,
    returns and interior cuts of the families the proof tree defines.
  - `concreteChildren` sets the five extension families to `False`.
  - `transmit_source_children_are_closed` proves only that the five
    parameters are unused. Its proof is `children_closed`.
- **Docstrings that overstate.**
  - The closure theorem's docstring says changing a family "cannot omit a
    native child from the concrete initialized source relation". That
    overstates the theorem.
  - The headline's docstring says "every native source point", while its
    sibling theorems (`Statements.lean:2703-2760`) still say coverage of
    finer points is a separate obligation.
- **Further limits.**
  - The ledger is chosen afresh at each point. No exported statement says a
    ticket's terminal status persists from one point to the next.
  - The admission boundary is a successful splice or a new keepalive. Early
    `wgXmit` refusals sit outside the ledger and are charged once per
    invocation by `original_transmit_refusal_charged_once`. The charter
    listed `tx_errors` among the dispositions of admitted packets.
- **Required change.** The register row ("Proof and source audit closed")
  must say:
  - the claim holds at declared points;
  - coverage was audited, not proved;
  - the ledger is per point;
  - the admission boundary moved, recorded as a reshaping with both
    wordings.

  Correct both docstrings, and make the headline's implicit binders
  `{site w h}` explicit.

**S3. T2's binding is a set of pieces, not one chain.** The charter's outcome
chains three steps: the peer at `wgXmit`, the key at staging, the endpoint
at the send. That chain has to be assembled from
`initialized_socket_route_key_core_and_endpoint`,
`recorded_admission_destination`, `initialized_socket_ciphertext_provenance`
and the `Born` relation.
- `Born` matches by payload, not by occurrence.
- `SocketReceipt.Valid` does not state that the world after the peer read is
  the world the socket call runs in.

The register should say this plainly. A composed theorem is a natural
follow-on.

**S4. T6's headline is an eighteen-field structure, and runner-level retirement is not in it.**
- **What `Outcome` is.** `reference_aware_retirement_outcome : Outcome`
  packages eighteen fields with no field docstrings. They mix three domains:
  - universal per-function contracts (`txChecks`, `rxChecks`, `ageCheck`,
    `sendingRejection`, `removedRead`, …);
  - a fact at the end of a successful run only (`initializedCredits`);
  - implications from a native call that succeeded (`workerUnpublishes`,
    `finalRelease`). `finalRelease` assumes `refcount = 1` and concludes
    removal.
- **Where runner-level retirement is.** It is only in
  `initialized_conditional_tx_retirement` and `…_rx_retirement`, outside
  the headline. Each chains the dispatch, the worker, the last reference
  and the release as hand-supplied premises after a successful run.
- **Two gaps.**
  - No field links a later encryption to its earlier valid admission
    certificate, the contract C3-F1 relies on. That link lives in T1 and T2.
  - Removal is stated at a single point in time, not as persistence.
- **Required change.**
  - Give each field a docstring.
  - In the register, split the row by domain.
  - State the residual exposure plainly. Packets admitted before expiry,
    invalidation or unpublication may still encrypt afterwards. No time or
    count bound on that is proved.

**S5. The narrowing of T1 and T6 is recorded as a wording artefact, without both wordings, and "no statement was weakened" misleads.**
- **What changed.**
  - The original T6 forbade transport encryption under an invalid or
    expired sending key, retained work included.
  - The original T1 said no encryption happens under a key after its limit.
  - Commit `867b471f` amended both to admission-time checks, under a
    `[USER 2026-10-18]` tag.
- **The Rule Zero reading is right.** The mirror follows the C: checks at
  staging (`send.c:356-388`), later encryption without a recheck
  (`send.c:162-219`), and release at the last reference. So this is not a
  mirror defect, and the evidence for a kernel bug is not there.
- **But the meaning changed.** It is still a narrowing of a security target
  that the implementation does not meet, not a reshaping that keeps the
  meaning.
- **How it is recorded.**
  - Both wordings survive only in git history.
  - `docs/decisions.md` has no entry, although this changes a standing
    charter target.
  - The sentence "No statement was weakened" (report `:12`, register `:17`)
    will be read as covering the campaign.
- **Required change.**
  - Put both wordings and the reason in the report.
  - Add a decisions entry with its provenance.
  - Qualify the sentence.
- **For the user.** The `[USER]` tag is the campaign's record; I cannot
  check it from the repository. Confirm it at signoff.

**S6. T3: one charter clause is held elsewhere, and two clauses are weaker than they read.**
- **Transport endpoint learning.** Learning the endpoint on the transport
  path (`setPeerEndpoint` after the replay window) is not among T3's
  `Protected` events (`CausalCoverageHistory.lean:12`). Campaign 2's H3
  covers it (`original_initialized_data_consumptions_authenticated_final`);
  the T3 row should cite that.
- **Per-invocation and per-call clauses.** The at-most-one cookie reply is
  per invocation, not a count over the run. The refused consumers' "nothing
  else changes" is per consumer call.
- **What "rooted" admits.** Any effect inside a harness-initiated operation
  (`fixture` scope) counts as rooted.

  The row should say all three.

**S7. The report and the register are run narratives, are stale in places, and miss the success criterion's form.**
- **The report is mostly a log.** Most of its 746 lines are dated
  "Source-NN" tranche logs, and AGENTS.md rules out run narratives. Parts
  of it contradict the progress table: "T2 remains open" in the proof
  structure section, and "T2 is not complete" under Validation.
- **What the report lacks.** The charter's section 5 asks for a short report
  per result, with:
  - the architecture;
  - every reshaped statement with both wordings;
  - the findings;
  - the effort;
  - a ranked list of mirror changes, each marked altitude-preserving or not.

  None of these is there per result. The terms "effort", "altitude" and
  "ranked" do not occur.
- **The register has the same problems.**
  - It carries 75 "Source-NN" paragraphs, some under "Lag and repair".
  - Its campaign-3 prose still says the pending/terminal partition is open,
    against its own table.
  - The six outcomes have no row in the Results table, which the register
    itself calls the current claim register ("Adding a result", step 3).
- **Required change.**
  - Replace the log with the per-result reports.
  - Move the outcomes into the Results table.
  - Remove the tranche logs from the register.

**S8. Some of the report's reproduction commands cannot be run from a clone.** The historical recipes use `a241295c^1` and other pre-rebase commits. These are reachable only through the local ref `refs/archive/proofs-campaign-3-pre-eba3c2b6`. Remove those recipes, or mark them as not reproducible from a clone.

### Notes

- **N1. How faithful the journals are.**
  - **What the journals are.** The headlines are stated over journals from a
    proof-tree copy of the runner with hooks (`Driver.executeObserved`).
  - **How they are tied to the mirror.** Equivalence is proved at the level
    of the runner's output, the JSON result or the stop: `NativeDriver.erases`,
    and `initialized_joint_transmit_reservations` states `ErasesOuter` to
    `Runner.executeTrace`. It is not exported for the internal world at
    each event.
  - **Proved complete.** Socket egress: `Emissions.Inv` over `w.sent`.
  - **Complete by construction only.** Transport AEAD, session, timer and
    work events are complete by hook placement. The mirror has one
    transport AEAD site, and T2 shows every sent payload has an earlier
    receipt. So the open case is an AEAD whose packet is never sent.
  - **Not journaled.** Handshake and cookie AEADs.
  - **Recommendation.** A completeness theorem for AEAD events would close
    T1's dependence on construction.
- **N2. T1's headline docstring says slightly more than its type.** Its
  docstring says each ciphertext uses "its packet's assigned" counter. The
  type gives the uniqueness of (allocation stamp, nonce), with the stamp
  being `internalId`, which is never reset. It also gives the bound and the
  exact wire and AEAD encoding. That is a strong result. The link from an
  encryption to the allocation made for that packet is used inside the
  proof but not exported. Either export it or trim the docstring.
- **N3. The rejection-arm theorem is function-level.**
  `native_nonce_rejection_invalidates_and_restores` is a postcondition of
  the proof tree's copy of the arm (`Lifetimes.stagedOutNokey`). That copy
  is tied to the mirror by the erasure chain. The register's "actual
  invalidation" should say "function-level".
- **N4. Scale.** The campaign adds 317k lines in 3,545 files and 674
  terminal theorems. Every mirror change will cost a carry in proportion,
  and all six outcomes already lag `218d3ffd`. The project should weigh
  this against the value of the per-cut source closure.
- **N5. C3-F1's classification.** It is classified as no kernel bug and no
  tray entry. Under Rule Zero that is defensible: the code does what it
  intends. Whether a "design nuance" report belongs in the tray is the
  user's call.
- **N6. The recipes are automated as a speedbump.** The campaign adds no
  recipe of its own; C3-F1 rests on R5's two witnesses, which the
  speedbump replays. That is adequate for a finding that is not new.
- **N7. The four campaign-internal review notes are progress reviews by
  the campaign's own subagents.** One carries an `[AGENT]` tag. All four
  state their scope honestly. They are not independent landing reviews.

## 2. What the campaign establishes, read plainly

The campaign gives:

- **T1.** Whole-run nonce uniqueness per key allocation over initialized
  runs, stopped prefixes included, with the bound and exact encoding.
- **T2.**
  - Socket-level binding of ciphertext, key, peer and endpoint, in pieces.
  - A ticket ledger that is exact at the declared source points.
  - Per-invocation refusal accounting.
- **T3.** Whole-run silence and causal rooting for the protected events,
  with a cookie exception that is typed and per invocation.
- **T4 and T5.** Replay refusal, at most one response and installation per
  exchange, and responder confirmation, conditional on the uninhabited
  `H1*` packages.
- **T6.** Admission-time and decryption-time checks, and the per-call
  retirement contracts, with runner-level retirement only under
  hand-supplied premises.

It does not give:

- retirement that cancels admitted work;
- a time or count bound on retained work;
- conservation coverage proved rather than audited;
- completeness of the AEAD journal;
- anything over `218d3ffd`.

## 3. Changes required before the merge

1. **B1.** Correct the resource-limit claim in the report and the register,
   and obtain the user's disposition of the file-wide raises.
2. **S1.** Mark T4 and T5 conditional, with each headline's packages named
   and their uninhabited status stated; fix the C2 pins.
3. **S2.** Correct the T2 conservation row and the two docstrings; make the
   headline's binders explicit; record the admission-boundary reshaping.
4. **S3, S4, S6.** Correct the T2, T6 and T3 rows as described above; add
   docstrings to the fields of `Outcome`.
5. **S5.** Put both wordings of T1 and T6 in the report; add a decisions
   entry; qualify "no statement was weakened"; have the user confirm the
   amendment's provenance.
6. **S7, S8.** Replace the tranche logs with per-result reports in the
   charter's form; move the outcomes into the Results table; drop or mark
   the unreachable recipes.

None of these changes a proved statement. All but B1's disposition are
documentation or docstring edits.

Signed: independent reviewer (Claude Opus 5.5), 2026-10-20.
