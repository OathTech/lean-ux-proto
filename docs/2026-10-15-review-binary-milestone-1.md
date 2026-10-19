# Trust-surface review: binary adequacy, milestone 1

[AGENT, reviewer, Claude Opus 5.5], 2026-10-15. This is the independent review that
section 7a of [the charter](2026-10-15-charter-binary-adequacy.md) asks for after
milestone 1. Subject: `task/binary-tv` at `430ea90`, which has main `cb2348e`
merged in. Its report is `docs/2026-10-15-binary-adequacy.md`, section
"Milestone 1: function theorem and review handoff".

## What was run

Everything below ran in a detached, read-only copy
(`.worktrees/review-binary` at `430ea90`), never in the grind's worktree.

- Kraken was rebuilt from the shared clone at `8af7806` by applying the two
  patches in `binary/kraken-patches/` with `git am --committer-date-is-author-date`.
  The result is exactly `e033e3dac812a576881a329b2d4c174364f3d44c`, the commit
  `TrustBase.krakenCommit` names.
- `capped -- lake build` in `binary/`: PASS, 351 jobs.
- `capped -- scripts/in-bundle scripts/proof-gate --binary`: PASS. All nine
  declarations use only `propext`, `Classical.choice` and `Quot.sound`;
  `compose_regions` uses no axioms.
- `lake env leanchecker --fresh LookupSnapshotTransport` and
  `--fresh LookupWitness`: both exit 0. Together they replay the import closure
  of every headline.
- `#print axioms` run separately on `lookup_simulation`, `lookup_transport`,
  `lookup_framed_transport`, `lookup_snapshot_transport` and `witness_pre`:
  standard axioms only. I also printed the statement of `lookup_simulation`
  with `#check` (quoted under F0).
- I wrote and checked a scratch theorem that applies `lookup_simulation` to
  the witness with the real decoder `pinnedFetch`. It needs one fact,
  `AnchoredDecoderAgreement pinnedFetch`, which takes one line to prove; the
  five contracts remain hypotheses. Standard axioms only.
- Image check: I parsed `Image.lean` and `ServiceImage.lean` and compared
  them with `objdump -d` (binutils 2.42) of the pinned vmlinux
  (sha256 `16c34620…`, which equals `TrustBase.elfSha256`). All 226 rows match
  on address, length and text. The listings cover every instruction of the
  eight functions involved: lookup, peer-get, `__local_bh_enable_ip`,
  `__sanitizer_cov_trace_pc`, `write_comp_data` and the three comparison
  wrappers.
- `llvm-objdump-19`, a second, independent decoder, finds the same
  instruction boundaries. A spot check of the operands agrees.
- Text patching: none of the 847 `.altinstructions` entries falls in these
  ranges. The image has no `__jump_table`, its `.smp_locks` section is empty
  (a uniprocessor build), and `ret` is never rewritten to a thunk.
- DWARF, read with `llvm-dwarfdump-19`: `wg_peer.handshake` is at 0xe0 and
  `wg_peer.refcount` at 0x420. Both match `peerHandshakePeerOffset` and
  `Layouts.peer_refcount`. The entry field offsets (0/8/24/28) and the
  `and $0x1fff` bucket mask match the disassembly.
- Parsing: Kraken parses 87 of the 88 service rows. The one row it rejects
  is the `ud2` at `0xffffffff810732ea`, on `__local_bh_enable_ip`'s
  hard-interrupt warning path, which `BhEnableReady` excludes. It is a failing
  fetch, which fails closed.
- `binary-probe service-tests`, `peer-null` and `peer-nonnull`: PASS
  (18, 4 and 21 concrete cases, two undefined-value seeds each).

## F0. What the headline says (answers to question 1)

```
lookup_simulation : ∀ fetch, AnchoredDecoderAgreement fetch →
  TracePcContract fetch → TraceCmp4Contract fetch → TraceConstCmp4Contract fetch →
  TraceConstCmp1Contract fetch → BhEnableContract fetch →
  ∀ c coverage preempt returnAddress initial world,
    Pre_lookup c coverage preempt returnAddress initial world →
  ∀ answer finalWorld, (indexLookup c.kinds c.query).run world = .ok (answer, finalWorld) →
    Eventually (historyStep fetch) (LookupPost c coverage preempt returnAddress initial world answer finalWorld)
      ⟨initial, [initial]⟩
```

(`binary/LookupAdequacy.lean:13-25`). It has the shape section 1 asks for.
`Eventually` is Kraken's inductive "every path reaches the postcondition". An
`unimplemented` effect, an unmapped load or store, or a missing fetch makes a
step `False` (`Execution.lean:201-208`; Kraken `X64/OmniSemantics.lean:13-22`;
unmapped stores in `Semantics.lean:328-333`). Undefined values are universally
quantified, so a step can neither be skipped nor made vacuous.

`LookupPost` (`LookupPost.lean:166-178`) gives:
- the real ABI return: the return address, `rsp+8` and the callee-saved
  registers;
- the exact result: RAX is NULL or the entry address, and the output word
  holds the peer pointer;
- `R` at the final state;
- `R` at every observed point (`MatchesPoints` with `AtPoint`) and at every
  anchored cut (`CutsAligned`). Both are taken from the machine history,
  which the proof does not supply;
- an `EqualOutside` frame at the end and at every cut.

The observed decisions come from the real successor PC at each conditional
jump (`LookupObservation.lean:36-86`). An unexpected successor is an error.

Every hypothesis beyond the charter's statement: `AnchoredDecoderAgreement`,
the five service contracts, and `Pre_lookup` (the clauses of `LookupEntry`
beyond `R`; see F1 and F7). That is the complete list. No hypothesis assumes
a region invariant, a decision sequence or a live peer.

Dead-peer states are not excluded:
- `EntryFocus` allows a NULL owner word (`focus.peer = none`);
- the count relation `PeerCountPhase.At` (`PeerCountState.lean:34-40`)
  allows a count of zero;
- `LookupOutputNeeded` (`TrustBase.lean:370-371`) requires output storage
  only for a live increment.

The one domain condition is that the focused peer is present in the mirror's
store, so that `project` gives `count = some _`. The mirror erases a peer at
kref release (`Leanux/WG/Peer.lean:71-77`), and on such a world its own run
stops (`getPeer`). So this exclusion comes from the mirror's acceptance, not
from Pre. It matches the report's stated limit (a state between a zero count
and the RCU release).

The record stream `ρ` of section 1 is vacuous for this function, which has
no hooks. See F11.

## Findings

### F1. Pre is witnessed only on the miss path (blocking for milestone 2)

`witness_pre` (`LookupWitness.lean:347-361`; its state is in
`LookupWitnessState.lean:12-59`) is the same-bucket miss of
`d1_wrong_receiver_index_same_bucket`: query `0x8a0b0c0d` against an entry with
index `0x0a0b0c0d`, `focus = ⟨none, none⟩`, KCOV mode 2.

Every clause that matters only when an owner is selected holds vacuously in
this witness: `dataService`, `dataReturn`, `dataBucket`, `ownerCount`,
`outputProtected` and `outputMapped` (lines 348-360). The same goes for the
13-word helper stack, the owner and count relations of `Physical`, and the
mode-3 buffer requirement. So no Lean proof shows that `Pre_lookup` is
satisfiable on any path that calls `wg_peer_get_maybe_zero`, which is where all
the helper work and the finding-1 store-back happen. If those clauses were
jointly unsatisfiable, the theorem would say nothing on the hit paths and the
gate would still pass.

I built a live-hit state by hand and found no contradiction, and the
concrete `binary-probe` runs execute such states. But that is not the guard
section 2a requires.

Settled by: Lean proofs of `Pre_lookup` for
- a live hit, using the state `d1_second_response` already runs concretely;
- a zero-count (dead) hit;
- a hit whose owner word is NULL;
- ideally, a wrong-kind stop in KCOV mode 3.

Each should come with its executable run to the return. They are cheap,
since the probe already materializes these states.

### F2. The five service contracts are assumed, though the code is in the image and provable (should-fix, before the milestone-4 transport)

The contracts are hypotheses quantified over the same `fetch` as the decoder
(`TrustBase.lean:115-123, 259-295`). If any one is false of Kraken's semantics
of the pinned bytes, the theorem is vacuous for the real kernel, on every
path.

I compared each plan with the listing:
- the gate on 0xff0100, 0x100 and 0xff0000;
- the reads at `+0x6e0`, `+0x6e4`, `+0x6e8` and `+0x704`;
- `pos < size` for the PC callback;
- `end_pos = 32*count+40 <= 8*capacity` for comparisons;
- the store order, with `area[0]` written first;
- argument widths and zero extension (`movzbl` for the 1-byte comparison);
- the BH arithmetic `preempt - cnt + 1`, then `decl`, then the pending test.

I found no discrepancy. All the bodies are leaf functions that push nothing,
so `EqualOutside` holds. The concrete `service-tests` confirm the plans in 18
cases, including mode 3. Still, this rests on tests and on reading, not on
proof.

The bodies are 88 straight-line instructions with no loops. Proving
`TracePcContract pinnedFetch` and the other four from `ServiceImage` would take
five items out of the trust base and leave only the bytes-to-AST link
(`WholeImageDecoderAgreement`). The charter asks that each trust item be
"necessary and stated at its weakest", and these are not necessary.
(Crypto contracts later cannot be discharged this way. KCOV, BH and lock
contracts can.)

Settled by: theorems that `pinnedFetch` satisfies each contract. Failing
that, a written justification for each contract that names the instructions,
plus a recorded decision [USER] to keep them assumed.

### F3. The trust file declares premises that no headline uses (should-fix)

The following are defined in `TrustBase.lean` and referenced nowhere else in
`binary/` (grep):
- `WholeImageDecoderAgreement` (37-38)
- `AnchoredTextStable` (46-47)
- `ReadOnlyImage` (51-52)
- `Permissions`, `AccessAllowed` and `RunAccessAllowed` (55-81)
- `SerializedEnvironment` (85-87)

Yet the file's header says "These are explicit hypotheses". The environment
premises the charter lists (one CPU, no interrupt, permissions, stable text)
are not hypotheses of the theorem at all. They are built into the choice of
model: Kraken has no interrupts, `All` grants every access, and `fetch` does
not depend on time. The theorem is sound about Kraken. But its link to the
hardware rests on these as unstated outside assumptions, and the trust file
suggests otherwise.

`%gs` is not mentioned anywhere. It is unused in the listings, which I
checked.

Settled by:
- moving these into a clearly marked "external interpretation, not Lean
  hypotheses" block, or deleting them;
- stating there, in one place, which model simplifications the hardware
  reading relies on;
- recording the text-patching facts measured above.

### F4. The postcondition cannot re-establish the next call's environment (should-fix, before composition)

`LookupPost` puts the preempt count in the write footprint
(`LookupWriteFrame.lean:9-12`) but never says what its final value is. It
also says nothing of the KCOV buffer invariant (`count ≤ capacity`) or the
softirq-pending word after the call. `BhEnableContract` balances the count,
but the theorem does not export that balance.

As a result, the next anchored entry's Pre clauses (`preemptAt`,
`coverageAt`, `bhPending`) cannot be derived from this theorem. Milestone 6,
and any caller-level composition, will need them.

Settled by: adding to `LookupPost` that the final preempt count equals
`preempt` and that `KcovBuffer` and the pending word are preserved. These are
probably already internal facts.

### F5. `compose_regions` is not the composition, and the method is not the generated per-region grind (should-fix in the report; note for the method)

`compose_regions` (`Execution.lean:213-223`) is a generic induction over
`Eventually`, and nothing in `binary/` uses it (grep). The proof of the
headline is a bespoke per-path composition (`selected_execution`,
`miss_execution` and others) spread across the roughly 190 files the branch adds under `binary/`,
28,291 inserted lines since the charter checkpoint `36cfe55`.

Yet the gate and the handoff present `compose_regions` as "the composition
lemma". The charter's single lemma, "proved once, that walks the mirror's
decision tree and the machine's control-flow graph together", does not exist.
Nor were region statements generated from the correspondence table; the
report says so for automation ("zero").

Settled by: correcting the report and the gate's list, and stating, before
milestone 2 scales, whether that lemma will be built or the per-function
composition will continue.

### F6. R is the function's own read/write footprint; landed results reach the binary only under frame premises nothing discharges (raise with the user; note)

What `R` relates (`LookupProjection.lean:274-314`), all by exact equality:
- the head word of the selected bucket;
- the chain's `next` pointers, `type` and `index`, in the mirror's list order
  (`Representation.lean:54-63`);
- the focused owner's peer word, including NULL, written back pending, at
  pointer equality;
- the focused peer's 32-bit count, unsigned, with the pending CMPXCHG phase;
- the decision log.

Abstracted:
- owner identity becomes an address, through the interpretation functions
  `c.peers` and `c.keypairs`. They are not required to be injective; within
  one bucket the chain forces distinct addresses;
- the table pointer is the argument, not `device->index_hashtable`;
- every other bucket, peer field and keypair field.

So `R` is exact and minimal for this function, and its physical reading is
correct against the ELF (see "What was run").

Charter section 2a lists fields the landed results read: the replay counter
and bitmap, the keypair slots, the queues, the endpoint, the allowed-IPs
nodes and the handshake state. None of these is in `R`. They reach the binary
only through `lookup_framed_transport` and its instance
`lookup_snapshot_transport` (`LookupSnapshotTransport.lean:145-172`), under two
premises:
- the bytes initially represent the snapshot (`represented`);
- those bytes are disjoint from lookup's writes (`separate`).

Both premises are stated honestly, not hidden. But neither Pre nor any
theorem discharges them, and the witness does not exercise them. So today no
landed result is carried to the binary unconditionally. The report's
sentence "Thus the lookup frames needed by replay-window/lifetime results are
available" reads stronger than that.

The charter's amended section 1 says both "R is minimal" and "R covers every
field a landed result observes". The build follows the first reading. I think
that reading is the sound one, since frame theorems give equality outside the
footprint, but the user should settle the wording. The two frame premises
then become named obligations of the composition: a global heap-separation
and representation invariant.

`lookup_transport` itself is generic, but its `P` gains binary meaning only
through the fields of `R`. That is by design, and the report should say it in
those words.

### F7. Realism of Pre: clauses to test against the kernel's entries at milestone 4 (note)

Nothing in Pre depends on the fixture's own addresses, and the separation
clauses (`TrustBase.lean:402-422`) describe ordinary kernel layout (stack,
heap, vmalloc'd KCOV area, globals). Three clauses can exclude real states:

- `bhPending` (`TrustBase.lean:401`) requires the pending-softirq word to be
  zero whenever `rcu_read_unlock_bh` would read it. That happens for
  process-context callers with preempt count 0: the handshake worker's
  `wg_noise_handshake_consume_response` and the cookie path. With a softirq
  raised, the real `__local_bh_enable_ip` runs `do_softirq` inside the lookup
  (`call` at `0xffffffff810732f8`), and Pre excludes that state. If the corpus
  places a softirq there, the theorem does not cover that entry, and the
  contract needs a variant that runs the recorded softirq.
- `KcovBuffer` requires `area[0] ≤ capacity`. That word is writable from user
  space. The harness keeps it valid, but this is a harness assumption.
- `BucketShape` requires entry addresses other than 0. The machine treats an
  entry at 0 (a node at address 8) as the end of the chain. Unrealistic, and
  harmless.

Settled by: the milestone-4 capture-and-check. The report should list these
clauses as the ones to watch.

### F8. The binary gate does not bind the trusted inputs (should-fix)

`check_binary` (`scripts/proof-gate`, after line 207) builds, checks the axioms
of nine names and scans `binary/*.lean`. It does not check three things:

- (a) That `.deps/kraken` is at `TrustBase.krakenCommit` with a clean tree.
  It is a lake path dependency, so the gate passes on any Kraken state.
  `binary/run.py` checks the commit, but the gate does not. This check is
  cheap, guards the semantics the charter names as trusted, and belongs in
  the gate.
- (b) The trust surface, "reported by name" as the charter asks. The gate
  never prints the headline's statement or `TrustBase.lean`'s declarations,
  so a change to `Pre_lookup`, `LookupEntry` or the hypotheses passes
  silently. A printed `#check` of the headline, diffed against a committed
  copy, would be a cheap speedbump.
- (c) That `Image.lean` and `ServiceImage.lean` still match the ELF. My
  comparison takes seconds, so this would be a cheap speedbump at claim
  points.

Kernel replay is left to `lake check` outside nono. That is consistent with
the box rules.

### F9. The rate and the feasibility claim (note)

The report's numbers are honest as worded:
- 54 region identities in 16.98 elapsed hours;
- elapsed time, explicitly "not aggregate agent labor";
- zero automated regions, 54 hand-finished.

But the evidence is thin for the claim of feasibility. It covers one small
function and its helper: 138 anchored instructions, plus 88 service
instructions handled by contract. It took about 28,000 lines of hand proof,
roughly 200 lines per anchored instruction, with no automation, no generated
statements and a bespoke composition (F5). Nothing yet supports a forecast
for milestones 2 to 6, which bring loops over a trie, `bsr`, crypto contracts
and writes to shared structures.

Settled by: labor accounting and lines of proof per instruction in the
milestone-2 report, and an explicit automation target there.

### F10. Process notes on the branch (note)

- The validation runs used `LEANUX_QEMU_SLOTS=16`. AGENTS.md says to keep it
  at 8.
- `harness/guest.c` now prints `LEANUX_BINARY_PCS` and `LEANUX_BINARY_CMP` for
  every operation, unconditionally, with the s4 addresses hard-coded. The
  harness parser matches line prefixes, so it ignores these lines
  (`harness/linux.py:542-554`). Still, they should be put behind a flag, or
  kept off `main`, when the branch lands.
- The branch edits AGENTS.md (the gate paragraph). That is a standing-rule
  edit, which goes to the user at merge.
- Kraken itself contains a `sorry` in `Kraken/X64/Examples/IncrementDMA.lean`.
  It is off the proof path; the axiom check is clean.

### F11. What the theorem does not say (answer to question 6)

The report lists: no reachability of dead-peer entries, no allocator
membership, no whole-trace claim, unwitnessed frame premises, Pre realism
pending, contracts assumed, and the ELF interpretation external. That list
is accurate but incomplete. Add:

- Pre is unwitnessed on every hit path (F1).
- The environment premises are not hypotheses but properties of the model
  (F3).
- There is no exported preempt or KCOV state at return, so the result cannot
  yet be chained (F4).
- The record-stream part of section 1 is not exercised: the lookup has no
  hooks, so the statement's shape with records is untested until milestone 3.
- `c.peers` and `c.keypairs` are a per-call interpretation, and nothing ties
  them to a global allocation map. The theorem does not say that two calls
  read identities the same way; composition must share `c`.
- KCOV contents at return are confined to the footprint but not otherwise
  specified. They are not a WireGuard observable.

## Verdict

**Go to milestone 2 with the named changes.**

The theorem is genuine, kernel-checked, and it has the shape section 1
describes. It is total over undefined outcomes. It runs from every Pre state
through the real return, and the decisions it matches come from real machine
edges. `R` relates by exact equality everything the function touches, and is
minimal. Pre does not exclude dead-peer states. The image and the DWARF
reading are correct against the ELF, and the private Kraken additions are
small and match the Intel definitions (memory CMPXCHG, `js`, index-only
addressing).

Conditions:
- **Before milestone 2 starts (blocking):** F1. Pre gets Lean witnesses on
  the hit paths.
- **Before the milestone-4 transport:** F2 (prove the KCOV and BH contracts
  from the image, or get the user's decision to keep them assumed), F3 (an
  honest trust file), F6 (the user settles the R wording, and the frame
  premises are recorded as composition obligations), and F8 (a)–(b).
- **Before composition:** F4.
- **In the milestone-2 report:** F5 and F9.

## For the user

This is the right kind of theorem, honestly stated, for one function. From
any entry state satisfying `Pre_lookup`, the binary under Kraken provably
reaches the real return, and at every branch it agrees with the accepted
mirror run. It agrees exactly on the bucket chain, the owner's peer word and
the peer's reference count, and it changes nothing outside a stated
footprint.

It is not yet the result you asked for in one respect that matters: no
landed property (the counter window, R1–R6, H1–H6) is yet carried to the
binary unconditionally. Generic transport reaches the binary only through
the three fields lookup touches. Everything else goes through frame premises
that some later global invariant must discharge.

Three more caveats:
- The precondition has a concrete witness only for a miss, so the hit paths
  could in principle be vacuous (F1, cheap to close).
- The environment assumptions live in the model rather than in the
  statement.
- The five callback contracts are assumed, though they could be proved from
  the image.

None of this is a defect in the statement itself. It is a matter of scope
and of guards, to fix before the grind scales.
