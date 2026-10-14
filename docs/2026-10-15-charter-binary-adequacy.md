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

## 1. The theorem

For an anchored WireGuard function `f` with mirror `m_f`, with `R` the state
relation between a Kraken machine state and a mirror state:

> If the machine state `σ` is related by `R` to the mirror state `s` at
> `f`'s entry, with `f`'s arguments in their ABI registers, and Kraken runs
> `f` from its first instruction to the return into the entry frame under
> the environment assumptions, consuming the record stream `ρ` at the hook
> calls, then the run reaches a state `σ'`, `m_f` run from `s` on `ρ` reaches
> `s'`, `R σ' s'` holds, and the machine's branch outcomes at the
> correspondence points equal `m_f`'s decisions in order.

Adequacy of the mirror for an operation is the composition of these over
the recorded sequence of anchored entries, with the environment assumptions
as stated premises. The first theorem to close is for
`wg_index_hashtable_lookup`, over every path: hit, miss, type reject,
reference reject, and the bucket chain's loop. The order after it is in
section 5.

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

## Paste for Codex#3

> Follow-on to your scoping probe, same worktree and branch: prove one
> theorem, adequacy of the mirrored WireGuard functions at the binary level
> under Kraken, by a direct per-region grind with a minimised trust base.
> Charter: `docs/2026-10-15-charter-binary-adequacy.md` (read it whole). No
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
