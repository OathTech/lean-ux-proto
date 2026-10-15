# Charter: binary-level adequacy of the WireGuard mirror, the grind

A long-cycle proof assignment for a Codex agent and its subagents, following
[the scoping probe](2026-10-15-binary-tv-scoping.md): prove one target
theorem, adequacy of the mirrored WireGuard functions at the binary level
under Kraken's x86-64 semantics, by a direct per-region grind with a trust
base listed in one place and kept small. No reusable toolchain is the
deliverable; whatever automation gets built along the way is a by-product.

Provenance: [USER 2026-10-14] "we're not building some reusable toolchain,
we are proving a single target theorem, namely adequacy of the called
function at the binary level. We might build some stuff along the way but
basically this is going to be a big grind and a minimized trust base." The
same day: "The hard part is finding the ISA-state simulation invariant, but
we basically already have a first approximation in the mirror
datastructures. Then the meat of the proof is verifying that between any
two correspondence points, we have invariant preservation." [AGENT,
coordinator] wrote the charter from the probe's findings; the probe's
estimate priced a certificate checker and its soundness theorem, which this
charter does not build.

## 0. What matters, and what does not

[USER 2026-10-14] "The eventual adequacy result & transport of wireguard
results to the binary, is the only thing that matters. We are going to get it
done by any means necessary. The theorem / trust surface MUST MUST be correct.
Everything else is ephemeral. It might get promoted to reusable
infrastructure at some point. But basically if it's outside the trust
surface, we don't care much, that's a judgement call."

So, in this assignment:
- The trust surface is two things: Kraken's semantics at the pinned commit,
  and the statement of section 1 with the premises it assumes: the
  environment premises, the call contracts, the decoder and the image, all
  of them declarations in `binary/TrustBase.lean`. `R` as a whole is a proof
  artefact, not surface: a wrong body fails the proofs or weakens the
  transported properties, both visibly. Its machine-side domain at an entry,
  the precondition `Pre_f`, *is* surface, because an unsatisfiable `Pre_f`
  makes every theorem vacuous [USER 2026-10-14: "a sub-part of R defines the
  states over which the binary may be called, and this *is* a trust surface
  (eg it could be vacuous and we would prove the binary 'correct' even
  though it couldn't be executed)"]. Section 2a says how it is guarded. They are reviewed
  independently (section 7a) and every change to them is visible, named and
  justified. Correctness here is the whole point.
- Everything outside that surface is a means: generators, scripts,
  automation, scratch definitions, the shape of intermediate lemmas, the
  private Kraken branch's internals. Any means that the Lean kernel accepts
  and that adds nothing to the trust base is allowed, including ugly ones.
  The house rules on form, naming and documentation apply to the trust
  surface and the reports, not to the means. What proves useful may be
  promoted to infrastructure later; nothing is built for reuse now.

## 1. The theorem

[USER 2026-10-14] "The ideal result here is essentially an adequacy result
over the kraken semantics for this specific binary. That is, if the binary
target function is called (inside the kernel) with the necessary precondition
satisfied over its state, the binary executes and establishes a post
condition that satisfies the theorems that have been proved about the lean
mirror. That is, any property we prove about the mirror is necessarily also
a property that we have proved over the binary. ... It should be phrased so
that we can transport any of the properties we care about into the binary.
Not over specific properties. That is, it's a generic simulation which shows
the binary is a refinement over the observations our properties depend on."

Fix the image (identity `6b2018b9`) and Kraken's semantics at the pinned
commit. `R` is the state relation between a Kraken machine state and a
mirror world, and it is minimal: a frame property [USER 2026-10-15]. It is
defined over the WireGuard projection of the mirror's World only, and every
clause of it is justified by a read or a write in an anchored function or
by a field a landed WireGuard result observes (the index table and its
owners, peers, keypairs and counters, the handshake and cookie state, the
rings and queues, the timers and dispatch state the anchored functions
touch, the service callbacks' metadata). What a function does not touch is
handled by frame theorems, the binary's write footprint and the mirror's
unchanged fields, never by a relation clause; the file layer, seccomp,
epoll, the task-work chains, credentials and signal state are outside `R`
by construction, not related trivially. A smaller `R` weakens the
hypothesis, so the theorem applies in more contexts, and the frame
theorems give equality outside the footprint, which is stronger than
relatedness; nothing transportable is lost, since a property transports
through the fields `R` relates, and `R` covers every field a landed result
observes. A later result that observes a field outside `R` extends `R`
additively. Definitions built for state outside `R` are parked under
`binary/attic/`, imported by nothing on the proof path, with a line saying
what each was for; they are not counted. (The charter's first wording,
"it relates the whole mirror world", was read literally and cost the
grind a day on task, seccomp and file state; the wording was the
coordinator's error.) For an anchored function `f` with mirror `m_f`:

> For every machine state `σ` and mirror world `s` with `R σ s`, every record
> stream `ρ`, under the environment premises of section 2: if the mirror's
> run of `m_f` from `s` on `ρ` is accepted (no fail-closed stop) and ends in
> `s'`, then Kraken's execution of `f` from `σ`, with the arguments in their
> ABI registers and `ρ` consumed at the hook calls, terminates at the return
> into the entry frame in a state `σ'` with `R σ' s'`, and at every
> correspondence point between the two, the machine state is `R`-related to
> the mirror's world at that point.

Composed over the recorded sequence of anchored entries (section 3), the
same statement holds for a whole operation and for a whole trace, with the
environment premises as the only additions.

## 1a. Transport, generic

The mirror's results are universal statements over accepted mirror runs:
sequences of mirror worlds and events. The theorem says that the `R`-images
of the machine states at the correspondence points *are* such a run, and
the accepted one. Therefore every property proved over mirror runs holds of
the binary's execution read through `R`, for every property at once,
landed or future: the counter window's S1 to S3, the campaigns' R1 to R6
and H1 to H6, and anything after them. There is no per-property transport
and no mention of any property in the statement; the binary refines the
mirror with respect to everything `R` observes.

The transport corollary is stated once, generically: for any predicate `P`
on mirror runs, if `P` holds of every accepted run of `m_f` from `s` on `ρ`,
then `P` holds of the mirror run induced by the machine execution from any
`σ` with `R σ s`. It is one application of the theorem. The report names,
at each milestone, which landed results are thereby carried to the binary
for the functions certified so far, as a consequence and not as work.

A binary execution the mirror would refuse as `unsupported` is outside the
claim by construction: the premise "the mirror's run is accepted" is the
fail-closed stance carried over, not a gap. A separate, weaker lemma may
state that up to the stop the two agreed; it is not required.

## 2. The trust base, kept in one file

`binary/TrustBase.lean` lists every assumption, each as a named Lean
declaration (an `axiom` only where nothing else expresses it, and then
counted), with a one-line justification. Nothing outside that file is
trusted beyond Lean's kernel. Expected contents:

- Kraken's x86-64 semantics as the meaning of the instructions (the
  `.deps/kraken` commit pinned).
- The decoder: the disassembly of the pinned image by binutils 2.42 as the
  instruction sequence Kraken interprets, with the branch displacements and
  instruction lengths checked by the probe's loader. There is no theorem
  from the bytes to the AST; this is an assumption, named.
- The image: identity `6b2018b9` (`kernel/identity-x86_64-net-choice.txt`),
  ELF sha256 `16c34620…`; its data and read-only sections at their link
  addresses as the initial memory for globals; runtime text patching
  (alternatives, static keys) assumed absent in the anchored ranges, or
  listed where it is not.
- Call contracts: for every service and environment callee reached from an
  anchored function, a specification stated as a hypothesis of the region
  lemmas that call it: allocators return the recorded outcome (kind 305),
  the hooks of kinds 206 to 312 write only the coverage area and return the
  recorded value, coverage and comparison calls write only the coverage
  area, locks and RCU leave `R`'s domain unchanged, `__local_bh_enable_ip`
  and its kin balance the preempt count and run no pending work, the
  assembly crypto computes the mirror's function. One declaration per
  callee, reused everywhere; adding one is a visible act.
- The environment: one CPU, no preemption, no interrupt inside an anchored
  run except where the records place a yield or a softirq placement, the
  anchored ranges mapped and fault-free, `%gs` unused (true of this image's
  anchored set, measured by the probe).
- The ABI: System V calling convention at entries and returns.

Not in the trust base: `bv_decide`'s native-verification axiom (the probe
closed its symbolic region with ordinary bitvector lemmas; if a goal needs
bit-blasting, the certificate is replayed without native reflection or the
goal is split, and a native axiom is a request to the user, not a default);
`sorry`; any `unsafe` definition in the proof path. The project's proof gate
(`scripts/proof-gate`) is extended by this charter to the `binary/` tree:
the three standard axioms plus the declarations of `TrustBase.lean` and
nothing else, reported by name.

## 2a. The entry precondition: non-vacuity and realism

For each certified function `f`, `Pre_f` (the machine states `R` relates to
some mirror world at `f`'s entry, with the ABI arguments; it constrains only
what `f` and its callbacks read, as `R` does) is listed in
`binary/TrustBase.lean` by name next to the function's theorem, and two
guards accompany it:

- **Non-vacuity, required at the function's milestone:** a concrete machine
  state satisfying `Pre_f`, constructed and executed under Kraken to the
  return (the probe's materialised state for the index lookup is the first),
  so the theorem is known to apply to at least one state. A `Pre_f` without
  its witness does not land.
- **Realism, required before the first transport (milestone 4):** the
  kernel's own entry states satisfy `Pre_f`. A record-only hook (class-
  approved, one oracle rebuild at an integration) captures, at an anchored
  entry during the differential run, the structures `R` reads for that
  function; the precondition is then checked offline against every recorded
  entry in the corpus, as a check rule with a fail-closed verdict. The
  report names the entries checked and the count. Until the hook exists, the
  witness is built from a corpus operation's mirror state through the DWARF
  layouts, and the report says so.

The same observation fixes what the reviewer checks about `R`'s body: the
fields the landed properties read (the replay counter and its bitmap, the
keypair slots and their identities, the queues' contents, the endpoint, the
allowed-IPs nodes, the handshake state) must be related by equality under
`R`, not loosely, or a transported property means less than its name. The
review compares `R`'s equations against the properties' statements.

## 3. The method

Direct, per region, no certificate layer:

- **Correspondence points** come from the existing table: each mirror
  decision's coverage point (`correspondence/kcov.json` and the witness
  data), each declared comparison's compare instruction, each record
  consumption's hook call, each call site. A region is the straight-line
  machine code between two consecutive points on a path, including the
  conditional moves and merged exits the compiler produced; a region may
  span a mirror decision whose outcome the machine computes without
  branching, in which case the lemma states the outcome as the value of a
  machine predicate.
- **`R`** is generated from DWARF layouts for records (the probe's
  `layouts.py` already extracts them) and written by hand for the
  pointer-shaped structures: the intrusive list chains, the rings, the
  trie, the keypair slots, as heap predicates of the form "the structure
  reachable from this address is this mirror value", with the probe's
  section 6 equations as the first instance. Loop invariants are `R` at the
  loop head plus the mirror's loop variables; nothing more is invented
  unless a loop forces it, and then it is written down.
- **Region lemmas**: for each region, from `R` at entry and the hypotheses
  of any call contract inside it, Kraken's run of the region's instructions
  ends in `R` at exit with the decision outcome stated. Discharged by
  symbolic execution with Kraken's `kstep` tactics and `R`-reasoning; the
  statements are generated from the correspondence table and the
  disassembly, the proofs automated where they can be and hand-finished
  where they cannot, and every hand-finished one is a candidate for the
  next automation.
- **Composition**: one lemma, proved once, that walks the mirror's decision
  tree and the machine's control-flow graph together, using the region
  lemmas, to the theorem of section 1 for `f`; calls to mirrored callees use
  their own theorems.
- **ISA gaps**: the 150 unsupported instruction forms the probe counted
  (signed-condition jumps, `rep stos`, `xadd`/`cmpxchg`/`xchg`, `ud2`,
  indirect `call` spelling, `bsr` with the zero-input policy, `div`,
  index-only `lea`, `bt`/`bts`, `cltq`) are added to a private branch of
  Kraken under `.deps/kraken` as they are met, each with its semantics
  reviewed against the Intel manual and a test, and listed in the report;
  `bsr`'s zero-input destination follows the kernel's own reliance
  (`arch/x86/include/asm/bitops.h`), stated as the model's choice.
- **The three-way check stays as a test, not as evidence for the theorem**:
  before a function's proof is attempted, its concrete run under Kraken is
  compared with the kernel's recorded coverage and operands on a corpus
  operation, as the probe did, so that a semantics mistake is caught by
  the kernel before a proof is built on it. Looping paths need
  per-invocation coverage; `harness/guest.c`'s first-occurrence
  deduplication is a harness change you may make for this purpose, named
  in the report.

## 4. Setup

- Repository `/home/dev/projects/lean-ux-proto`. Continue in
  `.worktrees/binary-tv` on `task/binary-tv` (the probe's branch, yours).
  The package is `binary/`, its own toolchain v4.35.0, requiring Kraken and
  the mirror by path; the mirror stays byte-identical to `main` except the
  one netlink-dump ascription already on the branch. `main` will move under
  you; merge it when convenient, the mirror edits are elsewhere.
- Kraken: a private branch for the ISA extensions, under `.deps/kraken` as
  a branch of the full clone, pinned by commit in the report; never the
  shared checkout's `main`.
- Everything else as the scoping charter: `capped` for builds, the oracle
  read-only, no other worktree touched, nothing on `main`, no push.

## 5. The order, and the milestones

1. `wg_index_hashtable_lookup`, every path, the bucket loop with `R` as its
   invariant, the two call contracts it needs. Deliverable: the section 1
   theorem for it, `TrustBase.lean` as it stands, the generators and
   automation as they stand. This is the milestone that decides the rate.
2. `wg_allowedips_lookup` with its `common_bits` helper (the `bsr` policy),
   over both address families, with the trie heap predicate.
3. `wg_index_hashtable_insert` and `wg_index_hashtable_replace`, the first
   writes to a shared structure; `wg_cookie_validate_packet` with the
   crypto contracts; `wg_noise_received_with_keypair` and the keypair
   rotation.
4. The receive path: `wg_packet_consume_data`, `decrypt_packet` (the
   inlined `counter_validate` certified inside `wg_packet_rx_poll` by an
   entry relation at its inlined range), `wg_packet_rx_poll`.
5. The send path, the handshake create and consume functions, the netlink
   surface, in the order the mirror's call graph suggests.
6. Composition over an operation's recorded entry sequence, the theorem for
   whole traces.

Each milestone is one commit series, one register row in a new section of
`docs/proofs.md` for binary adequacy (function, theorem name, the regions
count, the contracts used, the mirror pin), and one short report appended
to `docs/2026-10-15-binary-adequacy.md` (yours): what closed, what was
automated, every ISA extension, every trust-base addition with its
justification, the effort.

## 6. Rule Zero at this level

Rule Zero, in three clauses [USER 2026-10-14]: (1) the mirror might be
wrong; (2) the kernel might contain bugs; (3) the former is much more likely
than the latter. Every discrepancy is read in that order: a mirror defect
first, settled by the differential check against the kernel and fixed on the
mirror lane; a kernel finding only with positive evidence against the code's
stated intent, written up in the tray; a statement or relation is never bent
to accommodate either.

[USER 2026-10-14] "In general, the purpose of the verification should be
to validate the mirror, and detect discrepancies. Not to conform to mistakes
in the mirror. The binary (ie the real kernel) is the source of truth here
of course." So the direction of every discrepancy is fixed: the mirror
conforms to the binary, never the reverse. A region that will not close
because the mirror's data or control flow differs from the machine's is a
mirror defect, fixed on the mirror lane by the project's normal process (a
settling pass, the differential check, the register), and the region's
lemma closes against the fixed mirror. Neither `Pre_f` nor `R` is narrowed
or bent to make a mismatched region close, and the theorem's statement is
not weakened for it. The first instance: the index lookup's dead-peer
branch, where the kernel stores the null peer back into the entry and the
mirror kept the stale id, found at milestone 1 and fixed on the mirror.

A region lemma that will not close is one of three findings, and the report
says which with the evidence: the mirror differs from the machine on that
region (a mirror defect, reported with the trace that would show it
differentially; the mirror is never edited by this campaign); Kraken's
semantics differs from the hardware (tested against the kernel's recorded
coverage and operands; reported with the instruction); or the kernel's code
does something the mirror's altitude cannot express (a new cut, stated as a
contract and counted). None is a reason to stop; the next region starts.

## 7. Working conditions

As the proof campaigns': multi-week, subagents freely with one writer per
worktree, no hard stops, form corrected in the next commit, one commit
series and one report per milestone, the user relays, neutral framing, your
own attribution, no merge, no push. Report after milestone 1 with the rate
you measured (regions per agent-day, automated versus hand-finished) and
the trust-base file verbatim, then after each milestone.

## 7a. Review of the trust surface

After milestone 1 and before milestone 2, the coordinator sends the theorem
statement, the transport corollary, the composition lemma's statement and
`binary/TrustBase.lean` to an independent reviewer with no context, with one
question: is this the theorem we want, is every item in the trust base both
necessary and stated at its weakest, is each `Pre_f` satisfiable by a reachable
kernel state and the one the kernel actually provides at the call, and does
`R` relate by equality every field the landed properties read? The review's findings are
corrections to the surface before the grind scales; a finding that the
surface is wrong is the most valuable result this assignment can produce
early. The same review repeats at milestone 4 (the first transport) and
before the whole-trace composition.

## Paste for Codex#3

> Follow-on to your scoping probe, same worktree and branch: prove one
> theorem, adequacy of the mirrored WireGuard functions at the binary level
> under Kraken, by a direct per-region grind with a minimised trust base,
> and transport the mirror's landed results to the binary through it. The
> theorem statement, the transport corollary and `binary/TrustBase.lean` are
> the trust surface and must be correct; everything outside it is a means and
> may be ugly. Charter: `docs/2026-10-15-charter-binary-adequacy.md` (read it whole). No
> certificate checker and no soundness theorem about a checker: region
> lemmas between correspondence points, discharged by symbolic execution,
> composed by one lemma proved once; `R` generated from DWARF for records
> and written by hand for the pointer-shaped structures; every assumption
> in `binary/TrustBase.lean` by name; no `bv_decide` native axiom, no
> `sorry`, no `unsafe` on the proof path; ISA gaps added on a private Kraken
> branch as met, with tests. Milestone 1: `wg_index_hashtable_lookup` over
> every path with its bucket loop, then report the measured rate and the
> trust base verbatim. The three-way check against the kernel's recorded
> coverage stays as a test before each function. `main` moves under you:
> merge when convenient. No merge, no push; `capped` for builds.
