# Statement packet C1: the compiled allowed-IPs insertion

2026-11-10, branch `task/binary-c1-statement`. **Revision 2**, after the
independent review at `9155fd0a`
(`docs/2026-11-10-review-statement-packet-c1.md` on
`task/review-c1-statement`). Statements and their justification for one
proposed result of the binary track, for the owner to accept, change or
reject **before any proof work**. Nothing here is proved and nothing is an
adopted decision; every choice in it is a proposal [AGENT]. Revision 1 is
commit `954f8c1d`.

The Lean statements are in `binary/Statements/C1/`:

| File | Contents | Source lines |
| --- | --- | ---: |
| `Contracts.lean` | The layout and the service contract | 116 |
| `Headline.lean` | Premises, caller conditions, the headline, the alternative | 250 |
| `Vacuity.lean` | The witness, two exclusions, and `Signed` | 129 |
| `Test.lean`, `run-tests.sh` | The executable rendering and the search | 546, 28 |
| `measure-surface.py`, `Closure.lean` | The measurements of section 4 | 49, 48 |

They are `def … : Prop` and executable `def`s only: no theorem, no `sorry`,
no axiom, no resource raise. They compile file by file against the landed
package (Lean v4.35.0, Kraken pin `43df9468`) and are not package roots,
so the package build, the gate and `TrustSurface.expected.txt` are
untouched.

## What changed in revision 2

The review's verdict was: the headline's form is sound; do not sign until
the allocator contract is repaired. It was right on every point I could
check. Dispositions, one per finding:

| Finding | Disposition |
| --- | --- |
| **H1** A conforming service may overwrite nodes already handed out; the headline is false for such a service | **Fixed.** `ServiceWrites` now excludes the objects that stay handed out (`Kept`): all of `live` for an allocation, all but the released object for a release. The stub the reviewer argued is built and executed (section 5): it meets every clause of the revision 1 contract, clears an older node's peer word, and a later lookup returns NULL where the mirror returns a peer. The revised contract refuses it at the write-set clause |
| **H2** No mapped-stack, direction-flag or capacity premise; with `frame` that forces `Idle` false for any service that pushes | **Fixed.** `ServiceReady` on both clauses, in the form of the landed `RandomReady`: valid coverage state, room for a record when the buffer is in use, direction flag clear, `depth` mapped bytes below the return word. `insertReady` supplies the flag and the capacity; both caller conditions check the stack byte by byte. The direction flag is carried to the service calls by the landed `SystemInvariant` argument. A probe executes the hole: a state meeting every hypothesis of the revision 1 clause from which a stack-using service cannot return |
| **H3** The image's own allocator cannot meet the contract under the pinned Kraken, in either mode | **Accepted; the claim is reworded.** The result is about the six WireGuard functions linked against *any* service that meets the contract at two addresses. `Premises` never said which code is there; the text now says so, the names `allocEntry` and `freeEntry` are described as addresses, and the reasons the image's allocator is not such a service are in section 2 and in section 3. I confirmed `popf`, `prefetcht0` and `rdtsc` in the image and their absence from the pinned Kraken |
| **M1** Recording mode: six words written outside the buffer, the unwinder's reads against `frame`, capacity | **Capacity fixed** (in `ServiceReady`). **The rest described, not fixed**: section 2 lists the six words and what putting them in the arena costs, and says `frame` is false of the hook's unwinder. I did not add an exemption to `frame`: after H3 the contract is not a description of the hook, and a clause shaped to one detail of code the result cannot be about would be surface without a job. Owner decision 2 |
| **M2** The tie of the outcome to the pending record is foreknowledge in both modes; `free` keeps the stream, so only failures that do not depend on the slab can be carried | **Stated** in section 2 as the reviewer puts it. Contract unchanged: that scope (forced failures, or a stub's) is the oracle's |
| **M3** The hidden invariant makes the result closed-world; the sequence counter's increment is unclaimed | **Closed-world: stated** in sections 1 and 3 and put to the owner (decision 1). **Sequence counter: fixed**: `InsertStep` now concludes `SeqAdvanced`, a machine-level observation (the table's sequence word after the call is the word before plus one, modulo 2^64). It was dropped in revision 1 only because the relation carried it; nothing else was |
| **M4** The witness shows too little | **Fixed as a statement.** `Witness` replaces `Satisfiable`: an actual execution from an empty table through an insertion, an insertion that allocates twice, a rollback with its release, and a lookup that finds a peer; the service has a nonempty scratch, and during the second call's allocation changes a scratch byte and a coverage-buffer byte. It will be a stub and is called one |
| **M5** The tests do not test the contract; records replaced, not threaded; no variant perturbs the machine or the service | **Fixed.** The test is rewritten (section 5): its own machine driver; a service that uses its stack, writes the buffer, keeps its state and answers in arena memory and returns garbage in caller-saved registers; every clause of the contract checked on every service transition against a concrete `Idle`; mirror world and records threaded from an empty table; a search over layouts, entry states and services that meet the premises |
| **M6** The mirror's share of the claimed closure is understated | **Fixed.** Section 4 gives the closure by declaring module (my count: 970 hand-written declarations under `Headline`, 372 of them the mirror's; the reviewer's count by its own method was 847 project constants) and says the definition of an accepted run is in it |
| **L1** Premises against image and source | Folded in: the over-long-prefix path is not reachable from `set_allowedip` (section 3); the comment on address bytes and the return word is corrected, the condition left as it was, since narrowing it buys nothing |
| **L2** Cost | Folded in (section 6): contract repair and the witness added; the lower half of the range dropped |
| **L3** Slips | Fixed: the release is at line 237; the script says it needs the host Python and how long it takes; the T4 address item is closed (a slip in T4's notes, no proof depends on it) |
| Coordinator's correction on the size of the claim | Checked: the only thing revision 1 dropped from the conclusion to keep it short was the sequence increment, now restored. The vacuity statements are part of what is signed: `Signed := Headline ∧ Witness ∧ InsertThenLookup ∧ FailedInsertInvisible` |

The search found **no state or service that meets the premises as now
stated and breaks the conclusion**. It found one thing worth the owner's
attention that is not a counterexample: see "What the search found" in
section 5.

## 1. The headline

### In words

Fix the s5 image's code for `wg_allowedips_insert_v4`, `_v6`, `add.isra.0`,
`lookup`, `common_bits` and `wg_peer_get_maybe_zero` (26, 29, 506, 103, 73
and 76 instructions; the first three are new, the last three are the
landed lookup), the coverage and BH-enable callbacks under their landed
contracts, and **any code at the two service addresses that meets the
contract of section 2**. Fix a layout: the table's address, the peers'
addresses, the service's territory (the *arena*). Then there is an
invariant `Inv` between mirror worlds and machine memories such that:

- **Initial.** `Inv` holds at every physically empty table beside an
  empty mirror table, when the service is idle with nothing handed out and
  its future answers are the mirror's pending allocation records.
- **Framed.** `Inv` reads only the heap (the table's three words, each
  peer's reference count and list head, the arena).
- **InsertStep.** From any state satisfying `Inv` and the caller's
  conditions at the entry of either wrapper, and for any accepted run of
  the mirror's `Leanux.WG.insert` on the same arguments, the machine
  reaches the caller's return address with callee-saved registers
  restored, `eax` equal to the mirror's result, the table's sequence word
  advanced by one, `Inv` holding for the mirror's final world, and memory
  unchanged outside the stack window, the coverage buffer and the heap.
- **LookupStep.** From any state satisfying `Inv` and the caller's
  conditions at the entry of the compiled `lookup`, and for any accepted
  run of the mirror's lookup, the machine returns in `rax` the address the
  layout gives the selected peer, or NULL, and `Inv` holds again.

What is signed is `Signed`: the headline, the witness and the two
exclusions of section 5.

**What a reader may conclude.** For any finite interleaving of IPv4 and
IPv6 insertions and lookups on one table with a fixed set of peers,
starting from an empty table, every `eax` and `rax` the compiled code
returns is the mirror's, and each insertion advances the sequence word by
one. The reviewer's argument that the existential cannot be gamed (its
section 2) is the one I rely on: any `Inv` meeting the four clauses
contains every reachable pair.

**The result is closed-world.** The conclusion holds only while:

- the mirror world after one call is exactly the mirror world before the
  next: no removal, no peer creation or release, no packet path taking or
  dropping a peer reference, no other consumer of the record list;
- nothing but these calls changes a heap byte, the arena included, between
  calls. The statement does not say which heap bytes `Inv` reads, so the
  user must keep all of them fixed;
- the mirror's pending records are allocation records for the three sites
  and nothing else, from the start.

A later result on removal or the dump cannot use this one: two theorems
that each assert some invariant do not share it. Extending the claim means
a new, larger headline with every operation as a clause of one
existential, which replaces this one and re-proves its clauses. Lookups
raise a peer's count each time and nothing in scope lowers it.

### In Lean (`binary/Statements/C1/Headline.lean`)

```lean
def InsertStep (fetch : Int64 → Option Decoded) (L : Layout) (A : Allocator)
    (Inv : World → Mem 64 → Prop) : Prop :=
  ∀ (c : Context) (s : MachineState) (w w' : World) (family key cidr pid : Nat)
    (ra : UInt64) (answer : Int),
    Inv w s.data.dmem →
    insertReady L A c s family key cidr pid ra = .ok () →
    (liftWG (WG.insert family key cidr pid)).run w = .ok (answer, w') →
    Eventually (instructionStep fetch) (fun t =>
      Returned s t ra ∧
      t.data.regs.get (.low .rax .W32) = BitVec.ofInt 32 answer ∧
      SeqAdvanced L s t ∧
      Inv w' t.data.dmem ∧
      EqualOutside (InsertWrites L A c s) s.data.dmem t.data.dmem) s

def Headline : Prop :=
  ∀ (fetch : Int64 → Option Decoded) (L : Layout) (A : Allocator), Premises fetch L A →
    ∃ Inv : World → Mem 64 → Prop,
      Initial L A Inv ∧ Framed L Inv ∧ InsertStep fetch L A Inv ∧ LookupStep fetch L Inv

def Signed : Prop := Headline ∧ Witness ∧ InsertThenLookup ∧ FailedInsertInvisible
```

`HeadlineExplicit` is the same four clauses with `Inv` fixed to
`Related L A` (the landed `assertAt` for names whose nodes are the objects
handed out). It implies the headline and is what a proof would exhibit.

### Reused and new

Reused unchanged: `Eventually`, `instructionStep`, `EqualOutside`,
`InRange`, `Returned`, `EntryFrame`, `ActualHistory`, the decoder
agreements and callback contracts of `TrustBase.lean`,
`CommonBits.Callbacks`, the coverage `Context` and its executable checks,
`spansApart`, `Trie.networkKeyCheck`, `Trie.address`, `readNat`,
`tableFields`, `peerFields`, `Root.nodeOffsets`,
`AllowedipsEntry.TotalWrites`, `Source.lookup`, `liftWG`, the mirror's
`Leanux.WG.insert`; in `Related`: `Names`, `assertAt`, `reconstruct`,
`heap`.

New: `Layout`, `Allocator`, `Scratch`, `Kept`, `ServiceWrites`,
`ServiceReady`, `AllocResult`, `AllocatorContract`; `Premises`;
`callerSpans`, `frameReady`, `insertReady`, `lookupReady`, two window
constants; `armed`, `emptyTable`; `Initial`, `Framed`, `SeqAdvanced`,
`InsertWrites`, `LookupWrites`, `InsertStep`, `LookupStep`, `Headline`;
`Related`, `HeadlineExplicit`; `Ran`, `HeapSame`, `Witness`,
`InsertThenLookup`, `FailedInsertInvisible`, `Signed`.

## 2. Premises

Status key: **proved** elsewhere; **tested** by execution; **witness**
known; **assumed**.

| Premise | What it says | Status |
| --- | --- | --- |
| Sequential execution (implicit in `instructionStep`) | The machine steps Kraken's interpreter on this code alone | **Assumed, and unrealistic**: no interrupt, no RCU reader during an insertion, no sleeping allocation. The statement is about a quiescent machine |
| Kraken at `43df9468` with nine patches | The meaning of each instruction | **Assumed**; patches tested, none proved against another model |
| Decoder agreements (`Premises.insertion`, `.lookup`, `.peer`) | `fetch` returns the committed decoded terms of the six functions | **Tested** against the saved ELF by the generators' `--check`. The reviewer parsed `.altinstructions` and the section table: no patch site in any of the six functions and no jump-label, retpoline, return-thunk, ftrace or static-call section in the image, so "the CPU runs these bytes" holds for them. No common-fetch witness for the joint premise yet (landing review N4) |
| KCOV-instrumented image | 88 of the 813 instructions in scope are coverage calls | A fact about the target: the oracle build, not a production kernel |
| Callback contracts (`tracePc`, `callbacks`, `cmp1`, `constCmp4`, `bhEnable`) | Each returns, writes only its planned coverage words or the preempt count, keeps callee-saved registers | Five **proved** from the image in the first-milestone form; the allowed-IPs forms add a no-re-entry clause and are hypotheses in the landed lookup headline; `cmp1` and `cmp8` **not proved** in any form |
| `Premises.allocator` | The service contract, below | **Assumed. New.** Every clause tested against the test's own service; **not satisfiable by the image's allocator in this semantic base** |
| `insertReady` / `lookupReady` (per call) | Kernel ABI at entry, the arguments, address bytes in network order, a registered non-NULL peer, the `node_cache` word, a mapped stack window (200 bytes plus the service's scratch; 144 for lookup), valid coverage state with room for a record, the direction flag clear, and separation of the heap from the caller's spans and from every coverage and per-CPU word the callbacks touch | **Tested** over the search's families; refused on malformed entries. Consistent with the two calls in `set_allowedip` (reviewer, L1). **Entry realism assumed** (F7); no kernel capture replayed |
| `Initial`'s hypotheses | A physically empty table; objects aligned, separate and apart from the arena; mirror armed; pending records are allocation records for the three sites | **Tested**; satisfiable in a running kernel after `wg_allowedips_init` (reviewer) |
| Accepted mirror run (per call) | The mirror returns normally | The claim is silent where the mirror refuses |
| The mirror | `Leanux.WG.insert`, the mirror lookup, and the definition of an accepted run with the record machinery | The other side of the claim; tested by the project's differential check; 372 declarations of the headline's closure (section 4) |

### The service contract in full (`Contracts.lean`)

```lean
structure Allocator where
  Idle : Mem 64 → List Nat → List HiddenRecord → Prop
  depth : Nat

def Kept (kept : List Nat) (a : BitVec 64) : Prop :=
  ∃ object ∈ kept, InRange (.ofNat 64 object) nodeSize a

def ServiceWrites (L : Layout) (A : Allocator) (c : Context) (s : MachineState)
    (kept : List Nat) (a : BitVec 64) : Prop :=
  Scratch s A.depth a ∨ (L.Arena a ∧ ¬Kept kept a) ∨ c.writes a

structure ServiceReady (A : Allocator) (c : Context) (s : MachineState) : Prop where
  coverage : c.At s.data.dmem
  capacity : c.Needed → 0 < c.coverage.capacity.toNat
  forward : s.data.system.bits[10] = false
  stackMapped : ∀ i < A.depth,
    (s.data.dmem.get? (s.data.regs.rsp.toBitVec - .ofNat 64 A.depth + .ofNat 64 i)).isSome = true

def AllocResult (L : Layout) (A : Allocator) (live : List Nat) (record : HiddenRecord)
    (stream : List HiddenRecord) (t : MachineState) : Prop :=
  let a := t.data.regs.rax.toNat
  (record.bytes.head? = some 0 → a = 0 ∧ A.Idle t.data.dmem live stream) ∧
  (record.bytes.head? = some 1 →
    a ≠ 0 ∧ a % 8 = 0 ∧ (∃ span ∈ L.arena, span.1 ≤ a ∧ a+nodeSize ≤ span.1+span.2) ∧
    (∀ other ∈ live, disjointRanges a nodeSize other nodeSize = true) ∧
    readNat t a nodeSize = .ok 0 ∧ A.Idle t.data.dmem (live ++ [a]) stream)

structure AllocatorContract (fetch : Int64 → Option Decoded) (L : Layout) (A : Allocator) : Prop where
  frame : ∀ m m' live stream, A.Idle m live stream →
    (∀ a, L.Arena a → ¬Kept live a → m.get? a = m'.get? a) → A.Idle m' live stream
  alloc : ∀ (c : Context) (s : MachineState) (ra : UInt64) live record stream,
    s.pc = allocEntry → EntryFrame s ra → ServiceReady A c s →
    s.data.regs.rdi.toNat = L.cache → s.data.regs.get (.low .rsi .W32) = 0xdc0#32 →
    (ra.toNat, record.site) ∈ allocSites → A.Idle s.data.dmem live (record :: stream) →
    Eventually (instructionStep fetch) (fun t =>
      Returned s t ra ∧ EqualOutside (ServiceWrites L A c s live) s.data.dmem t.data.dmem ∧
      c.At t.data.dmem ∧ AllocResult L A live record stream t) s
  free : ∀ (c : Context) (s : MachineState) (ra : UInt64) live stream,
    s.pc = freeEntry → EntryFrame s ra → ServiceReady A c s → ra.toNat = freeSite →
    s.data.regs.rdi.toNat = L.cache → s.data.regs.rsi.toNat ∈ live →
    A.Idle s.data.dmem live stream →
    Eventually (instructionStep fetch) (fun t =>
      Returned s t ra ∧
      EqualOutside (ServiceWrites L A c s (live.erase s.data.regs.rsi.toNat)) s.data.dmem t.data.dmem ∧
      c.At t.data.dmem ∧ A.Idle t.data.dmem (live.erase s.data.regs.rsi.toNat) stream) s
```

`allocEntry` and `freeEntry` are the addresses at which the image has
`kmem_cache_alloc_noprof` and `kmem_cache_free`; `allocSites` maps the
three return addresses in `add.isra.0` to the mirror's record sites
(allowedips.c:205, :234, :190); the release returns at :237; `0xdc0` is
`GFP_KERNEL | __GFP_ZERO`. The test checks the literals against the
ELF-derived runner input; the reviewer confirmed them with `nm`,
`objdump` and `addr2line`.

**What the contract says, in the words a signer should use.** Some code
sits at two addresses. From any state in which it is ready (valid coverage
state with room for a record, direction flag clear, `depth` bytes of
mapped stack) and in which an abstract predicate `Idle` holds of memory, a
list of objects handed out and a list of pending answers:

1. it returns to its caller with the callee-saved registers kept;
2. it has changed memory only in its stack scratch, the coverage buffer,
   and the arena outside the nodes that stay handed out;
3. the coverage state is still valid;
4. an allocation answers as the first pending record says: NULL, or an
   8-aligned pointer to 72 zeroed bytes inside the arena overlapping no
   node handed out; a release takes the node back; `Idle` holds again with
   the lists updated;
5. `Idle` depends only on arena bytes outside nodes handed out.

`Idle` is never unfolded. For the contract to be satisfiable `Idle` must
determine the next answer from memory.

**This is not a description of Linux's allocator, and under the pinned
semantics the image's allocator cannot be shown to meet it.** What stands
between this contract and the code at those addresses in the image, as the
list of things that would have to be shown or assumed (the reading is the
reviewer's section 3, from the disassembly and the patch; I confirmed the
items marked *checked*):

| Item | Why it stands in the way |
| --- | --- |
| Instructions with no semantics in the pinned Kraken: `popf` (in `this_cpu_cmpxchg16b_emu`, on every successful fast path), `prefetcht0` (`kmem_cache_alloc_noprof+0x91`), `rdtsc` (twice per recorded allocation), `cmpxchg16b` (*checked*) | `instructionStep` is false where an instruction has no meaning, so no `fetch` that agrees with the ELF at the allocator can satisfy `alloc` where `Idle` holds. It needs Kraken patches (each a trust-surface change) before the question can even be asked |
| Boot-time patching: `kmem_cache_alloc_noprof+0x85`, `+0x91` and `kmem_cache_free+0xf4` are alternatives sites | The bytes the CPU runs there are not the ELF's; which text runs depends on the guest CPU's features |
| The slow path (`___slab_alloc`, then the page allocator) and `__slab_free` | `GFP_KERNEL` may reclaim and schedule; what runs meanwhile can change peer counts, which the contract says the call does not write. Only the fast paths (about 134 and 206 instructions) are candidates for proof |
| The interrupt flag (`pushf; cli; … popf` on every fast path) | Outside the sequential model |
| Recording mode: six words written outside the coverage buffer: `kcov_choice_seq`, `kcov_alloc_records`, `kcov_alloc_unwinds`, `kcov_alloc_unwind_cycles`, the steering schedule's `head` / `mismatches`, and `t->kcov_leanux_dropped` on overflow | They must be put in the arena. Then the arena is not the slab's territory but a set containing a counter that every recorded choice anywhere in the kernel increments, and the closed-world condition ("nothing else changes the arena between calls") excludes all of those, unless `Inv` ignores that word, which a reader of a hidden invariant cannot know |
| Recording mode: the unwinder (`kcov_alloc_chain` → `stack_trace_save`) reads the stack above the call and the ORC tables | The `frame` clause is false of the hook: its termination depends on bytes outside the arena, and with a chain-flagged steering entry so does the forced outcome. The claim would have to exclude chain-flagged entries and exempt a read-only region the caller keeps fixed |
| Recording mode: capacity | Fixed in the contract (`ServiceReady.capacity`): with a zero-capacity area the overflow branch stores outside the buffer |
| The outcome's tie to the pending record | **Foreknowledge in both modes.** With recording armed the record is *written by the call*, after the allocation (or by the pre-hook for a forced failure); before the call nothing in memory holds it, except a `fail` entry at the head of a loaded steering schedule. With recording disarmed no record is produced at all. As a precondition it is consistent (the record a recorded run yields is the outcome) and not checkable |
| `free` keeps the stream unchanged | For a slab, a release makes the next allocation succeed where it would have failed for want of memory, so no predicate on memory satisfies both clauses for a natural failure while a node is handed out; the rollback is exactly that case. The contract is consistent only for failures that do not depend on the slab's state: forced ones, or a stub's. That is the oracle's scope, and it settles the question |
| Zeroing and the size 72 | Depend on `s->object_size` and the cache having no constructor: properties of arena memory, hence of `Idle` |

What the reviewer's reading did establish in the contract's favour: the
hook leaves the callbacks' coverage state valid for a capacity of at
least one word, the record a recorded run produces carries the call's
outcome, the fast paths do not sleep, the real allocator never writes a
node it has handed out, and `kmem_cache_free` has no hook.

The landed random-provider contract is the precedent for a service behind
a hypothesis. This one differs from it in two respects a signer should
know: its private state is the abstract `Idle` where the provider's is an
executable check, and its coupling to the recorded input is merged into
the return law where the provider's is a separate safety law that does
not assert termination.

## 3. What is not claimed

- **Nothing about Linux's allocator.** The claim is about the six
  functions against any service meeting the contract. The image's
  allocator is not shown to be one and, in this semantic base, cannot be
  (section 2's table).
- Nothing about a concurrent kernel: no interrupt, preemption, softirq,
  second CPU, RCU reader during an insertion, or sleeping allocation.
- Nothing about a production kernel: the image is the KCOV-instrumented
  oracle build.
- **Nothing outside the closed world of section 1**: no other mirror
  operation between calls, no other change to any heap or arena byte, no
  composition with a later result.
- Not that the recorded outcome is what a real allocation will return.
- Not that the caller's conditions hold at any real call: `set_allowedip`
  is not in the claim and the lock argument is ignored. That caller
  checks the prefix length against the family's width first, so the
  over-long-prefix `-EINVAL` path of the claim is not reachable from it.
- Not the `!peer` exit: the caller's conditions require a registered,
  non-NULL peer, as the mirror's `insert` takes a peer identity.
- Nothing when the mirror refuses: a trie deeper than its bound, a lookup
  that would retry on a dying peer, a peer with a pending worker, a short
  or malformed record list.
- **Not the parent pointers, not the peers' node lists, not the internal
  nodes' list heads.** No theorem with an observable conclusion reads
  them; under `Headline` nothing proved here would notice a wrong one.
  The sequence word's increment is claimed per insertion (`SeqAdvanced`);
  its absolute value against the mirror's is not.
- Not the coverage record, a tight write frame, or any history,
  permission or no-re-entry conclusion.
- Worlds whose pending records contain anything but allocation records
  for the three sites are outside `Initial`.
- No transport of a proof-tree property; the two exclusions are instances
  stated by hand.

## 4. Trust surface

By the owner's definition as relayed by the coordinator [USER,
paraphrased]: trust surface is what could be wrong while every proof still
checks, in two kinds. Proofs, component theorems and relations used only
inside proofs are not surface. The claimed kind is surface because it may
be weaker than it looks; its size is a cost only where it is not needed
to say what the code does.

Printed lines, measured by `binary/Statements/C1/measure-surface.py` the
way `binary/surface.py` prints the landed file (`#print` at width 110,
universes shown):

**Kind 1, assumed** (may be false or unsatisfiable): the premises.

| Part | Printed lines |
| --- | ---: |
| New: layout, service contract with readiness, `Premises` | 230 |
| New: caller conditions and the starting point | 183 |
| Existing package definitions drawn in, not in the landed file | 174 |
| Existing and already printed | 40 |
| `TrustBase.lean`, landed verbatim | 755, none added |
| **New lines for kind 1** | **587** |

**Kind 2, claimed** (may be weaker than it looks, or vacuous).

| Part | Printed lines |
| --- | ---: |
| New: `Headline` and its clauses, `SeqAdvanced`, the write sets | 80 |
| Existing, not yet printed: `EqualOutside`, `InRange`, `instructionStep`, `TotalWrites` | 22 |
| The witness and the two exclusions, signed with the headline | 121 |
| **New lines for kind 2** | **223** |

The hypotheses inside the clauses belong to both closures; they are
counted once, under kind 1.

**The printed lines understate both kinds, and the mirror most of all.**
The definitional closure of `Headline`, counted as hand-written
declarations outside Lean's own libraries and grouped by declaring module
(`Closure.lean`):

| Where | Declarations |
| --- | ---: |
| The binary package (image terms, layouts, `TrustBase`, checks) | 369 |
| Kraken (the instruction semantics) | 188 |
| The mirror: `Leanux.Kernel.Defs` 159, `WG.Types` 145, `WG.State` 17, `WG.AllowedIps` 16, the decision enumerations 24, others 11 | 372 |
| The C1 statement files | 41 |
| **Total** | **970** |

(`Signed`: 982. `Premises` alone: 538. `HeadlineExplicit`: 1,029. The
reviewer's computed closure, by its own filter, was 847 project
constants; the difference is the filter, not the picture.) The mirror's
372 are what "the mirror's result" and "an accepted run" mean: the world,
the ambient state, the record machinery and `hiddenAlloc`, `lookup` with
`peerGetMaybeZero` and `refcountIncNotZero`. Acceptance is where the
claim goes silent, and its definition is in that closure, not in the
"about 120 lines of `add` and `insert`" revision 1 cited. This share is
claimed surface and is **not in the printed figures or the budgets
below**; the result's limits should say so.

**Not surface under `Headline`:** the relation. `Related`,
`HeadlineExplicit` and the closure of `assertAt` print 564 lines, 441 of
them new; under `HeadlineExplicit` they move into kind 2.

**Against the current total.** The landed file is 4,713 lines. Printed
the landed way this result adds 810 lines; the explicit alternative,
about 1,250.

**Proposed budgets:** kind 1, 600 new printed lines; kind 2, 230, of
which the headline proper is 102. Plus a stated, uncounted share: Kraken
and the mirror's closure. The reassessment's suggestion of 300 per
function family cannot be met.

**What pins the relation down, if it were in the conclusion** (unchanged
from revision 1): node keys, prefix lengths, child and peer pointers,
root words and reference counts have a consumer theorem (`lookup_checked`
concludes a pointer in `rax`); parent pointers, the peers' lists, the
internal list heads and the allocation counter have none, only tests. The
sequence word now has a machine-level observation of its own.

**A proposal on the gate's file** (no change made): split
`TrustSurface.expected.txt` into assumed and claimed sections, limit it to
final headlines, and add the closure count by module beside the line
count.

## 5. Evidence

Run: `binary/Statements/C1/run-tests.sh` after `lake -d binary build` and
`scripts/in-bundle /usr/bin/python3 -B binary/allowedips_mutation.py`
(the generator needs the host Python). It needs the saved s5 ELF; I used
`.artifacts/kernel-net-choice-s5/vmlinux` in the main checkout. Interpreted;
about 18 minutes. The figures below are from the final files; an earlier
run before the last statement edit printed the same lines.

### What the test is now

It executes the saved instructions of the six functions with the package's
interpreter loop (`runUntil`, unchanged) and uses nothing else of the
runner. Entry memory, the service and every check are the test's own.
Each call is judged in three steps and a failure is reported under one of
them:

- **PREMISE**: `emptyTable`, `insertReady`, `lookupReady` (the statement's
  own definitions), and on every service transition every clause of
  `AllocatorContract`: the hypotheses (entry, frame, `ServiceReady`'s four
  fields, the cache, the flags, the return site against the pending
  record's site, `Idle`), then `Returned`, every store the service made
  against `ServiceWrites`, the coverage state afterwards, `AllocResult`,
  and `Idle` afterwards.
- **MIRROR**: the mirror's own run from the threaded world.
- **CONCLUSION**: `Returned`; `eax` against the mirror's result;
  `SeqAdvanced`; every instruction write and every service store against
  `InsertWrites` with the statement's window (200 bytes plus the scratch);
  for lookups `Returned`, `rax` against the layout's address of the
  mirror's answer, and the write frame.

`Idle` is a concrete model: the service keeps a bump pointer, a free
list threaded through released objects, and **its pending answers** in a
block of arena memory, and `idle` reads them back and compares them with
the mirror's pending records. The service fails on an unmapped stack,
fills its scratch, appends a word to the coverage buffer when the buffer
is in use, scribbles on free arena bytes and on the released object,
reuses released objects, and returns garbage in the caller-saved
registers. The mirror world and its record list are built once, at the
empty table, and threaded from call to call; after each insertion the
address just inserted and up to four earlier ones are looked up. The
landed relation (`assertAt`) is checked after every insertion as an
instance of `Inv`, separately from the conclusion.

The scenario is revision 1's sixteen insertions plus a default route and
an address with host bits set, per family: every decision of the mirror's
`add` both ways except `addNoPeer`.

### The search

Aim: a layout, entry state or service that **meets the premises as
stated** and breaks the conclusion. For each family below the harness
first establishes the premises (a PREMISE failure is reported as such and
counts as no evidence), then looks for a CONCLUSION failure. Each row is
the whole scenario with IPv4 and IPv6 insertions interleaved on one table
(the baseline also each family alone and a second undefined-value seed).

| Family (premises established by the harness in each) | Insertions | Lookups | Conclusion |
| --- | ---: | ---: | --- |
| Baseline: the fixture's addresses, PC coverage; each family alone, both interleaved, two seeds | 108 | 486 | holds |
| Objects handed out 72 bytes apart (touching) | 36 | 168 | holds |
| Objects 80 bytes apart, the service scribbling on the 8 bytes between | 36 | 168 | holds |
| Kernel-range addresses (`0xffff8880…`, stack `0xffffc900…`) for the table, peers, arena, stack and address bytes | 36 | 168 | holds |
| Kernel-range addresses, objects touching | 36 | 168 | holds |
| Comparison coverage (KCOV mode 3) | 36 | 168 | holds |
| Coverage off (mode 0) | 36 | 168 | holds |
| Coverage buffer full from the start | 36 | 168 | holds |
| Coverage buffer filling up during the run | 36 | 168 | holds |
| Coverage capacity of two words | 36 | 168 | holds |
| Preempt count 0 (process context, where insertion really runs) | 36 | 168 | holds |
| Preempt count 1024 (nested BH-disable) | 36 | 168 | holds |
| Sequence word `2^64 - 1` at the start | 36 | 168 | holds |
| Garbage in `rdx` above the prefix-length byte | 36 | 168 | holds |
| Address bytes directly above the return word | 36 | 168 | holds |
| Address bytes ending where the stack window begins | 36 | 168 | holds |
| Stack pointer 8 mod 16 | 36 | 168 | holds |
| Table ending where the arena begins | 36 | 168 | holds |
| A small arena, objects touching | 36 | 168 | holds |
| Mirror allocation counter 1000, reference counts `0x7ffffff0` | 36 | 110 | holds; the mirror refused 58 lookups (below) |
| No stack scratch (`depth` 0) | 36 | 168 | holds |
| A 512-byte scratch | 36 | 168 | holds |
| A quiet service: no stack use, no record, no scribbling | 36 | 168 | holds |
| **Total** | **900** | **4,124** | **no conclusion broken** |

In every family but the last the service fills its scratch, appends to
the coverage buffer when it is in use, scribbles on free arena bytes and
the released object, and returns garbage in `rcx`, `rdx`, `rsi`, `rdi`
and `r8` to `r11`. The deepest stack write stayed at 200 bytes in every
family, and all 23 reachable outcomes of the mirror's `add` decisions
were taken in each.

Premises that must refuse, and do:

| Family | Refused by |
| --- | --- |
| Direction flag set at entry | `insertReady`: `c1.direction-flag` |
| Address bytes inside the stack window | `c1.caller-separation` |
| Arena laid over the table | `emptyTable`: `c1.arena-overlap` |
| Coverage capacity zero with the buffer in use | `c1.coverage` |
| Stack mapped less deeply than the window plus the scratch | `c1.stack-mapping` |

### The two defects of revision 1, executed

- **H1.** A service identical to the test's, except that on each successful
  allocation it also stores zero into the first word (the peer pointer)
  of the oldest node handed out. Judged by the **revision 1** contract,
  the harness finds every premise met on every transition (the store is
  inside the arena; `Idle` does not read handed-out objects), and the
  conclusion fails: after the third insertion (`first-child`), the
  compiled `lookup` of `10.0.0.0` returns NULL where the mirror returns
  the peer at `0x601000`. Judged by the **revision 2** contract, the same
  service is refused at the write-set clause on that allocation
  (`contract.writes: 0xa01000+8 is outside the service's write set`). So
  revision 1's `Headline` was false as stated, as the reviewer argued,
  and the repaired contract excludes this service
- **H2.** A state at `allocEntry` with the cache and flags in their
  registers, the return word of site 190 at the stack pointer, `Idle`
  true with one answer pending, valid coverage state, and nothing mapped
  below the return word. It meets every hypothesis of the **revision 1**
  `alloc` clause; the test's service, which stores below its stack
  pointer, cannot return from it (`store to unmapped stack`), so the
  clause is false of that service unless `Idle` is false there. Under
  **revision 2** the state is outside the clause (`ready.stack-mapped`)

### What the search found

No counterexample to the statement as revised: no layout, entry state or
service that meets the premises broke `eax`, the sequence word, `rax`,
`Returned` or a write frame. Three things it did turn up:

- **The claim goes silent inside its own closed world.** With reference
  counts near `2^31` the mirror refuses lookups (`refcount_warn_saturate`
  is unsupported in the mirror) once the count would reach `2^31`: 58 of
  168 lookups in that family. Since each lookup raises the count and
  nothing in scope lowers it, a long enough run of lookups of one peer
  always ends in silence. Not a defect of the statement; a limit to list.
- **A narrowing I had introduced while fixing H2**, found on re-reading
  the search's refusals, not by a failure: `lookupReady` had inherited the
  direction-flag and capacity conditions, which only the services need.
  They now apply to insertion alone. The run reported here is on the
  final files.
- **What execution cannot see.** Every way the test's service differs
  from a quiet one lies in memory or registers the six functions never
  read back (scratch, caller-saved registers, free arena bytes). That is
  evidence the compiled code does not depend on them. It is also why a
  contract that is too weak is invisible to any test whose service
  behaves: H1 and H2 were found by the reviewer's reading, and are
  executed here only because a misbehaving service was written for the
  purpose.

What I tried, so the reader can judge the search: the 23 families of the
table; the five refusals; the H1 service under both contracts; the H2
state under both; three probes of the `Idle` model's frame. What I did
not try: a service that returns an object straddling two arena spans
(the layout has one span); arenas of several spans; more than two peers;
a table and peers interleaved in one page with the arena; entry states
with status flags set other than the direction flag; a caller that
changes non-heap memory between calls beyond registers, the return word
and the address bytes; services whose `Idle` reads a non-live arena byte
that the six functions write (none exists by `InsertWrites`, but it was
not searched); any state taken from a kernel.

### Not tested

- No captured kernel memory and no recorded workload. The recording-armed
  capture of decision 10 remains the cheapest real evidence about the
  image's allocator and was not run.
- The service is a Lean-level transition, not fetched code: `Eventually`
  through a service body, and the witness itself, are untested.
- `frame` is probed at three points, not established for the model.
- `Framed` is exercised only by rebuilding the caller's registers, return
  word and address bytes between calls.
- One invariant instance, `Related`; two peers; tries of at most about
  thirty nodes; the families of the table and no others. Stack and
  coverage areas stay at low addresses in every family but one.
- The universal quantification: these are a few thousand executions.
- The package was not rebuilt from sources (outputs copied from the
  reassessment worktree and replayed).

### Evidence against vacuity, signed with the headline (`Vacuity.lean`)

- `Witness`: some `fetch`, layout and service meet every premise, and an
  actual execution runs from an empty table with five answers pending
  through an insertion, an insertion that allocates twice while a node is
  handed out, an insertion whose second allocation is refused (the
  rollback and the release), and a lookup that finds a peer; each call
  meets its caller conditions, the mirror accepts it and consumes exactly
  those records; the code at `allocEntry` has a nonempty scratch and,
  with the buffer in use, changes a scratch byte and a buffer byte during
  the second call's allocation. Intended realism: the literal image for
  the six functions and the callbacks (which needs `cmp1`, `cmp8` and a
  common fetch), and a **stub** at the two service addresses, named as a
  stub. It shows the premises are not contradictory. It shows nothing
  about the image's allocator.
- `InsertThenLookup`: at an empty table whose service will succeed, an
  insertion with a prefix length in range returns 0 and every later
  lookup of that address returns the peer's address, not NULL.
- `FailedInsertInvisible`: at an empty table whose service will refuse,
  the insertion returns `-ENOMEM` and every later lookup returns NULL.

The exclusions quantify over `Premises` and are as vacuous as it is; they
are evidence about the conclusion, the witness about the premises.

## 6. Decomposition and cost

A proof of `Headline` exhibits `Related` (possibly strengthened) and
proves the four clauses for it.

| Piece | Status |
| --- | --- |
| Wrapper: sequence increment, address copy and byte swap, call, epilogue | Counter instruction and epilogue landed; the rest open |
| `add` entry, guards, `-EINVAL` | Trial T4, unreviewed |
| Empty root | Tail landed (`Root.initialization_checked`); entry-to-return in T4 on a contract this packet replaces |
| Entry to the placement loop header | Open |
| Placement loop; `common_bits` at both call sites | Landed |
| Exact reassignment | Landed from its cut; composition open |
| First allocation on a nonempty trie, initialization, selection | Core landed; contract application and `-ENOMEM` open |
| Child attachment | Landed, `add+0x156` to `+0x549` |
| Covering node | Data side in T2, 22 instructions in T1; the rest open |
| Intermediate node | Data side and the tail in T5; 45 instructions and the composition open |
| Rollback: unlink, release, return | Open; no trial |
| Ordering and prefix facts T2 and T5 assumed | Open. **The largest uncertainty** |
| Each path linked to an accepted run of `Leanux.WG.insert` | Partly in the trials |
| `Initial`, `Framed`, `SeqAdvanced`, arena and `Idle` bookkeeping, `ServiceReady` at each call (direction flag by `SystemInvariant`) | Open, small |
| `LookupStep` from the landed `lookup_checked` | Open, small |
| Witness: a stub service as instruction terms, its contract proof, a common fetch, `cmp1` and `cmp8`, the four-call execution | Open; larger than revision 1 allowed |
| Exclusions | Open, small |

**Source-side facts.** The statement needs none; the proof and the
exclusions do. `Placement.loop_checked` exports nothing about what the
mirror's `nodePlacement` returned. The facts exist in
`Leanux/Proofs/WG/AllowedIps/` (about 1,600 lines for the placement
ones), which `binary/` may not import. Options: re-prove locally (4 to 10
worker-hours; within the range below); copy with origin (2 to 4 hours,
duplicate text); or a rule change, which also needs the proof gate
changed, since it fails if anything outside the proof tree imports it.
For C1 alone I recommend local re-proof, as the reviewer does; the rule
is C2's question.

**Cost.** Worker-hours: `InsertStep` 20 to 40; lookup clause, exclusions
and integration 8 to 15; the stronger witness 8 to 15. **40 to 70 in
all**, centre 50. Elapsed four to six days with four provers and a
reviewer. The basis is thin (single unreviewed trials on a contract now
twice changed, side conditions underived); the reviewer judged the lower
half of revision 1's 30 to 60 unlikely and I have moved the range up by
the witness. Owner: this packet with `Contracts.lean` and `Headline.lean`
(366 source lines) in one sitting; one for the post-proof review; one
`lake check` outside the sandbox. Independent review after proof: six to
ten hours.

## 7. Decisions for the owner

1. **The internal-invariant headline, knowing it is closed-world.**
   Recommended: yes; the reviewer concurs. It will be replaced, not
   extended, by any later result on removal or the dump. Alternative:
   `HeadlineExplicit`, which can be composed with later results and puts
   441 more printed lines in the claim, half of them policed by tests
   only.
2. **The service contract as revised**, read as a contract for any code at
   two addresses and not as a description of the allocator. Recommended:
   accept, with section 2's table as part of the result's stated limits.
   Sub-question: add a read-only exemption to `frame` for the unwinder
   (the reviewer's M1.2 offers it or exclusion)? Recommended: no; say the
   hook is outside the claim. Alternative: the exemption, about ten
   printed lines of contract shaped to code the result cannot be about.
3. **`Signed` is what is signed**: headline, witness and both exclusions.
   Recommended. Alternative: the headline alone, with vacuity argued.
4. **A stub service as the witness**, named as one. Recommended.
5. **Scope: both wrappers, `add` and the lookup observation.** Recommended.
6. **The NULL-peer exit stays outside.** Recommended.
7. **Prove `cmp1` and `cmp8` from the image** within this result.
   Recommended; the witness needs them.
8. **Budgets**: 600 new printed lines assumed, 230 claimed, with Kraken
   and the mirror's closure stated as uncounted. Alternative: count the
   closure by module at each claim point (my proposal for the gate's
   file).
9. **Source-side facts**: local re-proof for C1; the rule decided on C2's
   packet.
10. **Kernel evidence before proof**: a capture with allocation recording
    armed, checked against the contract's conclusion clauses, and the
    October capture and recorded comparison rerun. Recommended; the
    reviewer wants it seen before proof starts. It is evidence about how
    far the image's allocator is from the contract, not a discharge.
11. **Whether the result is worth having on these terms.** After H3 the
    honest reading is: WireGuard's insertion and lookup code is correct
    against the mirror *given an allocator specified by assumption*. That
    is what every landed headline with a service hypothesis says; here
    the service is on every interesting path. Recommended: yes, as the
    first completed state-changing function, with that sentence in its
    summary.

## What needs discovery

Nothing blocks stating the result. Open before or during proof:

- **The trie invariant.** The trials assumed ordering and prefix facts
  the landed relation does not carry. `Headline` absorbs a strengthened
  invariant without change.
- **A stub service in instruction terms** that meets the contract and is
  realistic in the two respects the witness asks for. Nobody has written
  one.
- Closed since revision 1: the reading of the recording hook (done by
  the reviewer; its results are section 2's table), and the T4 address
  (a slip in T4's notes).
