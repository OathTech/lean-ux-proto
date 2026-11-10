# C1: the recording-armed capture and the final statement

2026-11-10, branch `task/binary-c1`. Phase A of the commissioned result C1
(the compiled allowed-IPs insertion): the kernel capture that was to be run
and looked at before any proof work, and the final text of what is signed.
**Nothing is proved here.** The statement files contain `def … : Prop` and
executable definitions only. What was decided is in `docs/decisions.md`
(2026-11-10): `Signed` of revision 2 of
[the packet](2026-11-10-statement-packet-c1-insertion.md) with finding F1 of
[the review's follow-up](2026-11-10-review-statement-packet-c1.md) repaired.
Every judgement below is mine [AGENT]; the two things I think the owner
should decide are in [section 5](#5-what-the-capture-puts-to-the-owner).

## 1. The capture

### What was run

Five traces, each recorded first by the differential check on the saved s5
image with the insertion coverage profile, which arms the three allocation
sites of `add` (`allocNode190`, `allocNode205`, `allocNode234`): the oracle's
ordinary recording mode. All five recordings pass the check, so the mirror
and the kernel agree on them at the level the project's gate compares. Each
was then replayed in a guest stopped under QEMU's debugger and every call of
`wg_allowedips_insert_v4` / `_v6` was single-stepped with interrupts and
timers deferred.

| Trace | Calls | What it exercises |
| --- | ---: | --- |
| `c1_capture_grid` (new, `binary/Statements/C1/capture/`; two peers created by a first `wg set`, thirteen prefixes added by a second) | 13 | Empty root, both families; child attachment; exact match onto another peer, both families; covering node at the root and below a parent, both families; intermediate node (two allocations) at the root, below a parent, and for IPv6 |
| `a2_allowedips_root_nomem` (corpus) | 1 | The allocation at `allowedips.c:190` forced to fail: `-ENOMEM` on an empty table |
| `a2_allowedips_newnode_nomem` (corpus) | 2 | The allocation at `:205` forced to fail |
| `a2_allowedips_split_nomem` (corpus) | 2 | The allocation at `:234` forced to fail after `:205` succeeded: the rollback and the release |
| `b1_trie_routing` (corpus) | 8 | Five peers, each created between the insertions: what an ordinary multi-peer `wg set` does |

The failures were forced with the oracle's steering schedule (a `fail`
entry for the named site, as the three corpus traces carry it); a natural
allocation failure was not attempted. In all: **26 wrapper calls, 30
allocations (27 objects, 3 forced NULL) and 1 release.**

At each wrapper entry and return, and at each call of and return from the
two service addresses, the capture takes the registers, the memory the
statements mention (table, peers, nodes handed out, 3 KiB of stack below the
entry and 256 bytes above, the address bytes, the `node_cache` word, the
per-CPU words, the task's coverage fields, the coverage buffer's used part)
and **a dump of the whole guest RAM**. What a service wrote is therefore the
difference of two complete memory images, not a list of places somebody
thought to look. Inside the services every instruction address and the
registers before it are recorded, so the instructions executed and the
addresses their operands name are known too.

Three checkers read the captures (commands in [appendix B](#appendix-b-reproduction)):

- `analyse.py`: the whole-RAM differences sorted into the clauses of
  `ServiceWrites`, the instructions and operand addresses inside the
  services, the allocation outcomes against the recorded run's records.
- `Check.lean`: the statements' own executable definitions (`emptyTable`,
  `insertReady`, `lookupReady`, the literals, the windows, the layout) on
  the captured states, the mirror's `Leanux.WG.insert` threaded from the
  empty table, and Kraken executing the compiled wrapper, `add`,
  `common_bits` and the coverage callbacks from the captured entry state,
  with each captured service transition installed where the interpreter
  reaches a service address. The clauses of `AllocatorContract` are
  renderings, as in the packet's test, since they are propositions.
- The arena is not given by the statements. `analyse.py` proposes the
  smallest one that makes the write clause true of the run (the nodes' slab
  page plus every other byte range a service changed outside its stack and
  the buffer) and `Check.lean` evaluates the caller premises with it.

### What it showed

1. **No disagreement between the mirror and the compiled code.** In the 20
   calls evaluated against the mirror (12 of them inside one closed world
   from an empty table, the grid's other 8 after the change of peer of
   point 5), under two undefined-value seeds, `eax` is the mirror's answer,
   the sequence word advances by one, the landed relation holds after every
   call against the mirror's world, and 33 compiled lookups run afterwards
   on the captured heaps return the mirror's peer or NULL. Among them are
   instances of both exclusions: after the grid's first insertion the
   address is found; after `a2_allowedips_root_nomem`'s refused one it is
   not.
2. **Kraken's execution of the six functions reproduces the guest.** From
   each captured entry state the interpreter visits exactly the instruction
   addresses the guest did, reaches each service call in the captured state
   (registers and every captured byte), and ends in the captured return
   state. This was not required; it is the strongest evidence here that the
   decoded terms and the semantics mean what the CPU did on these paths.
3. **Every clause of the contract that can be evaluated holds of the image's
   allocator on these runs, for a suitably drawn arena.** Entry conditions,
   return, callee-saved registers, coverage state before and after, the
   returned object (aligned, 72 zero bytes, in the slab page, apart from
   every node handed out), NULL on a forced failure, and no byte of a node
   that stays handed out, of the table, or of a peer changed by any of the 31
   service calls anywhere in RAM.
4. **What the allocator does outside the contract is what the review said,
   plus the page allocator.** Outside its stack, the buffer and the slab
   page it changed the four recording counters on every allocation, the
   steering schedule's head on the three forced ones, the per-CPU freelist
   and transaction words, and, on the first allocation of each boot, about
   fifteen words of page-allocator and slab metadata. Its unwinder reads up
   to 1,448 bytes of the callers' stack above the return word and the ORC
   tables. Two of the instructions it executes at the service addresses are
   not the ELF's (boot-time patching), and the `popf` the review expected on
   every fast path is not executed on this guest CPU.
5. **A real configuration run leaves the closed world between peers.** The
   caller holds a reference on the peer it is configuring: between the last
   insertion for one peer and the first for the next it lowers one peer's
   count and raises the other's, both heap words. With peers created in the
   same `wg set` (`b1_trie_routing`) it also creates the peer. As signed,
   the result therefore speaks about the insertions of the first peer
   configured after the table is empty (5 of the grid's 13 calls, 2 of
   `b1`'s 8) and not about the rest of the same `wg set`. Nothing is wrong
   in those later calls: the grid's 8 were checked with the mirror's counts
   re-read from memory at the switch and every check holds. The statement
   is silent there. This is put to the owner in section 5.

### Clause by clause

Counts are checks passed out of checks made. "×2" means under both
undefined-value seeds. "Window" means the readiness definitions were
evaluated with the coverage buffer truncated to its captured words (the
guest's buffer is 32 MiB; `Context.At` asks that every word be readable);
the same definitions were evaluated verbatim on the whole buffer at the
first call of the grid.

| Clause | How it was checked | Result |
| --- | --- | --- |
| **(a) Wrapper entry** | | |
| `emptyTable` (the base case of `Initial`) | The statement's definition, on the first call of each trace, against the mirror's device after peer creation and the caller's reference | 5/5 ×2. The table's sequence word is the mirror's initial 1; counts and list heads agree |
| `insertReady` | The statement's definition, window | 20/20 ×2. Verbatim with the 32 MiB buffer loaded: 1/1 |
| The caller conditions inside it | Same evaluation: return word, 200 + `depth` mapped bytes of stack (`depth` 736 to 968 by trace), valid coverage state, capacity, direction flag, the separations (with the drawn arena, 5 to 23 spans, in the heap) | Hold. The preemption count at entry is `0x80000000`, a value the packet's search did not include |
| Whole 32 MiB buffer apart from heap, caller spans and metadata | `spansApart` on the full span | 20/20 ×2 |
| **(b) Each service call** (30 allocations, 1 release; 22 and 1 of them in the 20 calls evaluated in Lean) | | |
| Entry: service address, aligned `rsp`, `rdi` the cache, `esi = 0xdc0`; release: its one return site and `rsi` handed out | Interpreter state at the stop, which equals the captured one byte for byte | 23/23 ×2 |
| Return site against the mirror's pending record (`(ra, record.site) ∈ allocSites`) | The mirror's record list threaded from the empty table | 22/22 ×2 |
| `ServiceReady`: coverage, capacity, direction flag, `depth` mapped bytes | Window; `depth` the deepest the trace's services went (736 to 968) | 23/23 ×2 |
| `Returned` | Captured return state | 23/23 ×2. The other 8 return to their site with `rsp + 8`; their callee-saved registers were not compared |
| `EqualOutside ServiceWrites` with `Kept` | (i) Every captured byte that changed; (ii) the whole RAM | (i) 23/23 ×2. (ii) 31/31: nothing changed in a kept node, the table, a peer or above the return word. With the arena the slab page only, the clause is **false**: the list below |
| `c.At` afterwards | Window | 23/23 ×2 |
| `AllocResult` | By the mirror's pending record's byte: NULL, or non-NULL, 8-aligned, in the arena, apart from live nodes, 72 zero bytes | 22/22 ×2 (19 objects, 3 NULL) |
| The outcome against the record the mirror consumes | Site and outcome of the k-th allocation in the capture against the k-th allocation record of the recorded run | 30/30 |
| `Idle`, `frame` | Not capturable: `Idle` is abstract. What `frame` would have to be true of is in the next subsection | |
| **(c) Wrapper return** | | |
| `Returned` | Interpreter's final state, equal to the captured one | 20/20 ×2 |
| `eax` is the mirror's answer | `Leanux.WG.insert` on the same arguments and records | 20/20 ×2 (17 zero, 3 `-ENOMEM`) |
| `SeqAdvanced` | The table's sequence word before and after | 20/20 ×2 |
| `Inv` re-established | One instance, the landed relation (`assertAt`), with names taken from the allocations | 20/20 ×2 |
| `EqualOutside InsertWrites` | (i) Every store of the interpreter against the 200 + `depth` byte window, the buffer and the heap; (ii) whole RAM across the call | (i) 20/20 ×2; deepest store of the six functions and callbacks 200 bytes. (ii) 26/26 with the service-changed words in the arena |
| The mirror's pending records afterwards | Equal to the records the captured services did not consume | 20/20 ×2 |
| **(d) Lookup afterwards** | The compiled `lookup` under Kraken on the final captured heap of each trace, for every inserted address and three others; caller frame constructed inside the captured stack | `lookupReady` (window) 33/33; `Returned` 33/33; `rax` the mirror's peer 33/33 (20 a peer, 13 NULL) |

**Written outside the stack scratch, the buffer and the slab page** (the
whole-RAM differences across the 31 service calls):

| Where | Calls | What |
| --- | ---: | --- |
| `kcov_choice_seq`, `kcov_alloc_records`, `kcov_alloc_unwinds`, `kcov_alloc_unwind_cycles` (kernel globals) | 30 of 30 allocations each | The recording hook's counters; the last holds `rdtsc` differences |
| The steering schedule's `head` (a heap object of the oracle's) | 3 of 3 forced failures | 0 to 1 at the steered encounter |
| The cache's per-CPU `freelist` and `tid` words | The 27 allocations that return an object, the release | The lock-free swap, or the slow path's refill |
| `struct slab` fields of the new page, the cache's node counters, the per-CPU page lists, `contig_page_data`, `vm_node_stat`, `vm_event_states` | 4 allocations: the first of each boot | The slow path: `___slab_alloc`, `allocate_slab`, `__alloc_pages_noprof` |
| The free-pointer word inside the 54 other objects of the new slab page | Same 4 | Inside the slab page; none is handed out |
| `t->kcov_leanux_dropped`, the schedule's `mismatches` | 0 | Not reached: no buffer overflow, no schedule mismatch |

**Stack.** A recorded fast-path allocation uses 736 or 744 bytes below its
entry `rsp`, a forced failure 736; through the page allocator, 968; the
release, 64. An unrecorded allocation was not captured.

**Instructions.** A recorded fast-path allocation is about 6,400 native
instructions, of which 96 are in `kmem_cache_alloc_noprof` and about 5,400
in the unwinder. Per allocation: `rdtsc` twice; `pushf`/`cli`/`sti` once or
more (the steering lookup); `prefetchw` once on the fast path. No call of
`this_cpu_cmpxchg16b_emu` and no `popf` in any of the 31 calls: at
`kmem_cache_alloc_noprof+0x85` and `kmem_cache_free+0xf4` the guest's text
is `cmpxchg16b (%rsi); nop` where the ELF has the call, and at `+0x91` it
is `prefetchw` where the ELF has `prefetcht0`. Those are the three sites
the review named, and no other byte of the two functions differs.

**Read outside the arena.** Operand addresses of the service instructions:
the callers' stack above the return word (22 loads per allocation, up to
1,448 bytes above the service's entry `rsp`, far beyond the wrapper's
frame), `.orc_unwind`, `.orc_unwind_ip`, `.orc_lookup`, `.rodata`,
`pcpu_hot`, the task's coverage fields, `gfp_allowed_mask`,
`kcov_alloc_armed`, `init_on_alloc`, `init_on_free`, `slub_debug_enabled`,
and for the release `phys_base` and `mem_section`.

**Between calls** (whole RAM, restricted to the heap and the arena words):
nothing, between two insertions for the same peer (16 gaps). At each change
of peer (5 gaps): the two reference counts; in `b1_trie_routing` also the
new peer, `kcov_choice_seq` advanced by 2 or 3 (the records of the peer's
creation), and at two of the four gaps slab and page-list words that other
allocations share with the arena as drawn.

### The review's predictions

| Prediction (review section 3 and M1, M2) | Capture |
| --- | --- |
| Entry arguments: the cache, `0xdc0`, three return sites; the release's one | **Confirmed** |
| Needs mapped stack, clear direction flag, capacity; `Returned` on the fast path, the forced failure, and the slow path when it returns | **Confirmed**, the slow path included |
| Never writes a node it has handed out | **Confirmed** over the whole RAM, 31 calls |
| Coverage state valid afterwards for capacity ≥ 1 | **Confirmed** (window) |
| Object 8-aligned, 72 zero bytes, apart from live nodes; NULL when forced | **Confirmed** |
| The record is written by the call and carries the outcome; consistent with the recorded run's record | **Confirmed**: 30 of 30 outcomes equal the recorded run's records; the buffer gains the record during the call |
| Six words outside the buffer: `kcov_choice_seq`, `kcov_alloc_records`, `kcov_alloc_unwinds`, `kcov_alloc_unwind_cycles`, the schedule's `head`/`mismatches`, `kcov_leanux_dropped` | **Four confirmed on every allocation, `head` on the forced ones.** `mismatches` and `kcov_leanux_dropped` not reached |
| The in-progress counter is restored | **Consistent**: no net change |
| The unwinder reads the stack above the call and the ORC tables | **Confirmed**, with the extent: 1,448 bytes |
| `rdtsc` twice per recorded allocation; `prefetcht0` | **Confirmed** (`prefetchw` after patching) |
| Three alternatives sites; the bytes the CPU runs are not the ELF's | **Confirmed**, exactly those three |
| `popf` in `this_cpu_cmpxchg16b_emu` on every successful fast path | **Refuted for this guest**: the emulation is never called; the patched `cmpxchg16b` runs. `cmpxchg16b` has no semantics in the pinned Kraken either, so the conclusion the review drew stands |
| Fast-path frame about 150 bytes | Not tested (non-recording). Recording: 736 or 744 bytes |
| `kmem_cache_free` has no hook; one store into the freed object and the per-CPU swap | **Confirmed** (one release) |
| Every recorded choice anywhere increments `kcov_choice_seq`, so an arena containing it is changed between calls | **Confirmed** in `b1_trie_routing`; not in the grid, where nothing is recorded between calls |
| Natural failure after a release (M2) | Not exercised |

Nobody predicted: the first allocation of each boot goes through the page
allocator (so "only the fast paths are candidates" leaves out the first
insertion a kernel ever makes); the caller's reference changes heap words
between peers (point 5); the preemption count at entry is `0x80000000`;
the buffer is 32 MiB, so `Context.At` cannot be evaluated on a capture
except once; and Kraken reproduces the guest's execution exactly.

### What could not be captured

- `Idle` and the `frame` clause: abstract. The reads above bound what
  `frame` would have to ignore.
- Transient writes: a byte written and restored within one service call
  does not show in a memory difference. The in-progress counter is one.
- Loads of the service's string instructions beyond their first address,
  and 24 instructions the operand reader could not decode.
- The non-recording mode, a natural allocation failure, the slow path of
  the release, a buffer overflow, a steering mismatch.
- Anything concurrent: the call is single-stepped with interrupts and
  timers deferred, as in every capture of this package.
- The lookups are the compiled code under Kraken on captured heaps with a
  constructed caller frame, not lookups stepped in the guest. (The
  differential check of `b1_trie_routing` and the grid covers the guest's
  own lookups at the level it compares.)
- In `b1_trie_routing` the statements' definitions were evaluated on the
  first peer's two calls only; the other six calls were checked at the
  service level (whole-RAM classes, outcomes against records).
- The mirror's record is compared by site and outcome, not byte for byte
  with the words the capture run wrote into its buffer.

No harness, guest or kernel file was changed. The capture needed two things
the existing tooling did not have, both added in the new capture script on
top of the package's debugger client: QEMU's monitor through the debugger
(`pmemsave`, `gva2gpa`, both read-only) and all registers in one packet.

### Judgement

**The proof can start as signed.** The capture found no premise that fails
at a real call, no conclusion clause the image's code violates, and no
difference between the mirror and the binary. What it found about the
image's allocator is inside what was accepted when `Signed` was chosen: the
result is about any code at the two addresses that meets the contract, and
the image's allocator is not shown to. The capture adds that on these runs
the allocator's *behaviour* fits every evaluable clause once the arena is
drawn around what it writes, and that the remaining distance is the list
the review gave (instructions without semantics, the unwinder's reads, the
counters) plus the page allocator on a first allocation.

One thing should be decided before the headline's four clauses are
assembled, though it does not hold up the work on `InsertStep`: point 5,
in section 5.

## 2. The signed text

`binary/StatementC1Contracts.lean` (116 source lines),
`binary/StatementC1Headline.lean` (252),
`binary/StatementC1CallbackImage.lean` (21, generated) and
`binary/StatementC1Vacuity.lean` (155), roots of the package library
`BinaryProofs`: built by `lake -d binary build` and scanned by the binary
gate, which passes on this branch (1,123 jobs, printed surface unchanged).
The namespace is still `Binary.Statements.C1`. Doc comments are left out
below; the files carry them. `HeadlineExplicit` and `Related` stay in the
file as the alternative; `Signed` does not mention them.

**What is signed:**

```lean
def Signed : Prop :=
  Headline ∧ Witness ∧ InsertThenLookup ∧ FailedInsertInvisible
```

**The headline and its clauses:**

```lean
def Headline : Prop :=
  ∀ (fetch : Int64 → Option Decoded) (L : Layout) (A : Allocator), Premises fetch L A →
    ∃ Inv : World → Mem 64 → Prop,
      Initial L A Inv ∧ Framed L Inv ∧ InsertStep fetch L A Inv ∧ LookupStep fetch L Inv

def Initial (L : Layout) (A : Allocator) (Inv : World → Mem 64 → Prop) : Prop :=
  ∀ w d m stream, w.wg.dev = some d → armed w = true → w.ambient.hidden = some stream →
    (∀ record ∈ stream, record.site ∈ allocSites.map (·.2)) →
    emptyTable L m d = .ok () → A.Idle m [] stream → Inv w m

def Framed (L : Layout) (Inv : World → Mem 64 → Prop) : Prop :=
  ∀ w m m', Inv w m → (∀ a, L.Heap a → m.get? a = m'.get? a) → Inv w m'

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

def LookupStep (fetch : Int64 → Option Decoded) (L : Layout)
    (Inv : World → Mem 64 → Prop) : Prop :=
  ∀ (c : Context) (s : MachineState) (w w' : World) (d : Device) (family key : Nat)
    (ra : UInt64) (answer : Option PeerId) (pointer : Nat),
    Inv w s.data.dmem → w.wg.dev = some d →
    lookupReady L c s family key ra = .ok () →
    (Source.lookup (if family == 4 then d.peerAllowedips.root4 else d.peerAllowedips.root6)
      (if family == 4 then 32 else 128) key).run w = .ok (answer, w') →
    Trie.address L.peers answer = .ok pointer →
    Eventually (instructionStep fetch) (fun t =>
      Returned s t ra ∧
      t.data.regs.rax.toNat = pointer ∧
      Inv w' t.data.dmem ∧
      EqualOutside (LookupWrites L c s) s.data.dmem t.data.dmem) s

def SeqAdvanced (L : Layout) (s t : MachineState) : Prop :=
  ∃ before, readNat s (L.table+AllowedipsMutationLayout.seq) 8 = .ok before ∧
    readNat t (L.table+AllowedipsMutationLayout.seq) 8 = .ok ((before+1) % 2^64)

def InsertWrites (L : Layout) (A : Allocator) (c : Context) (s : MachineState) (a : BitVec 64) : Prop :=
  Scratch s (insertWindow + A.depth) a ∨ c.writes a ∨ L.Heap a

def LookupWrites (L : Layout) (c : Context) (s : MachineState) (a : BitVec 64) : Prop :=
  AllowedipsEntry.TotalWrites s c.coverage c.preempt a ∨ L.Heap a
```

**What is assumed of the code:**

```lean
structure Premises (fetch : Int64 → Option Decoded) (L : Layout) (A : Allocator) : Prop where
  insertion : AllowedipsMutationDecoderAgreement fetch
  lookup : AllowedipsDecoderAgreement fetch
  peer : AnchoredDecoderAgreement fetch
  tracePc : TracePcContract fetch
  callbacks : CommonBits.Callbacks fetch
  cmp1 : AllowedipsTraceCmp1Contract fetch
  constCmp4 : AllowedipsTraceConstCmp4Contract fetch
  bhEnable : AllowedipsBhEnableContract fetch
  allocator : AllocatorContract fetch L A
```

**The service contract** (for whatever code is at the two addresses):

```lean
structure Allocator where
  Idle : Mem 64 → List Nat → List HiddenRecord → Prop
  depth : Nat

def Scratch (s : MachineState) (depth : Nat) : BitVec 64 → Prop :=
  InRange (s.data.regs.rsp.toBitVec - .ofNat 64 depth) depth

def Kept (kept : List Nat) (a : BitVec 64) : Prop :=
  ∃ object ∈ kept, InRange (.ofNat 64 object) nodeSize a

def ServiceWrites (L : Layout) (A : Allocator) (c : CommonBitsCoverage.Context)
    (s : MachineState) (kept : List Nat) (a : BitVec 64) : Prop :=
  Scratch s A.depth a ∨ (L.Arena a ∧ ¬Kept kept a) ∨ c.writes a

structure ServiceReady (A : Allocator) (c : CommonBitsCoverage.Context) (s : MachineState) : Prop where
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
  alloc : ∀ (c : CommonBitsCoverage.Context) (s : MachineState) (ra : UInt64) live record stream,
    s.pc = allocEntry → EntryFrame s ra → ServiceReady A c s →
    s.data.regs.rdi.toNat = L.cache → s.data.regs.get (.low .rsi .W32) = 0xdc0#32 →
    (ra.toNat, record.site) ∈ allocSites → A.Idle s.data.dmem live (record :: stream) →
    Eventually (instructionStep fetch) (fun t =>
      Returned s t ra ∧ EqualOutside (ServiceWrites L A c s live) s.data.dmem t.data.dmem ∧
      c.At t.data.dmem ∧ AllocResult L A live record stream t) s
  free : ∀ (c : CommonBitsCoverage.Context) (s : MachineState) (ra : UInt64) live stream,
    s.pc = freeEntry → EntryFrame s ra → ServiceReady A c s → ra.toNat = freeSite →
    s.data.regs.rdi.toNat = L.cache → s.data.regs.rsi.toNat ∈ live →
    A.Idle s.data.dmem live stream →
    Eventually (instructionStep fetch) (fun t =>
      Returned s t ra ∧
      EqualOutside (ServiceWrites L A c s (live.erase s.data.regs.rsi.toNat)) s.data.dmem t.data.dmem ∧
      c.At t.data.dmem ∧ A.Idle t.data.dmem (live.erase s.data.regs.rsi.toNat) stream) s
```

**The evidence against vacuity:**

```lean
def CallbacksFromImage (fetch : Int64 → Option Decoded) : Prop :=
  ServiceDecoderAgreement fetch ∧
  ∀ pc instruction, StatementC1CallbackImage.fetch pc = some instruction → fetch pc = some instruction

def Witness : Prop :=
  ∃ (fetch : Int64 → Option Decoded) (L : Layout) (A : Allocator)
    (w0 w1 w2 w3 w4 : World) (d0 d3 : Device) (c1 c2 c3 c4 : Context)
    (s1 t1 s2 t2 s3 t3 s4 t4 : MachineState) (h1 h2 h3 h4 : List MachineState)
    (k1 n1 p1 k2 n2 p2 k3 n3 p3 key pointer : Nat) (found : PeerId) (ra : UInt64)
    (stream : List HiddenRecord),
    Premises fetch L A ∧ CallbacksFromImage fetch ∧
    w0.wg.dev = some d0 ∧ armed w0 = true ∧
    w0.ambient.hidden = some ([outcome 77 true, outcome 78 true, outcome 79 true,
      outcome 78 true, outcome 79 false] ++ stream) ∧
    (∀ record ∈ stream, record.site ∈ allocSites.map (·.2)) ∧
    emptyTable L s1.data.dmem d0 = .ok () ∧
    A.Idle s1.data.dmem [] ([outcome 77 true, outcome 78 true, outcome 79 true,
      outcome 78 true, outcome 79 false] ++ stream) ∧
    insertReady L A c1 s1 4 k1 n1 p1 ra = .ok () ∧
    (liftWG (WG.insert 4 k1 n1 p1)).run w0 = .ok (0, w1) ∧ Ran fetch s1 t1 ra h1 ∧
    HeapSame L t1 s2 ∧ insertReady L A c2 s2 4 k2 n2 p2 ra = .ok () ∧
    (liftWG (WG.insert 4 k2 n2 p2)).run w1 = .ok (0, w2) ∧
    w2.ambient.hidden = some ([outcome 78 true, outcome 79 false] ++ stream) ∧ Ran fetch s2 t2 ra h2 ∧
    HeapSame L t2 s3 ∧ insertReady L A c3 s3 4 k3 n3 p3 ra = .ok () ∧
    (liftWG (WG.insert 4 k3 n3 p3)).run w2 = .ok (-12, w3) ∧
    w3.ambient.hidden = some stream ∧ Ran fetch s3 t3 ra h3 ∧
    HeapSame L t3 s4 ∧ lookupReady L c4 s4 4 key ra = .ok () ∧ w3.wg.dev = some d3 ∧
    (Source.lookup d3.peerAllowedips.root4 32 key).run w3 = .ok (some found, w4) ∧
    Trie.address L.peers (some found) = .ok pointer ∧ Ran fetch s4 t4 ra h4 ∧
    0 < A.depth ∧ c2.Needed ∧
    ∃ (enter leave : MachineState) (back : UInt64), enter ∈ h2 ∧ leave ∈ h2 ∧
      enter.pc = allocEntry ∧ Returned enter leave back ∧
      (∃ a, Scratch enter A.depth a ∧ enter.data.dmem.get? a ≠ leave.data.dmem.get? a) ∧
      (∃ a, c2.writes a ∧ enter.data.dmem.get? a ≠ leave.data.dmem.get? a)
```

`Ran` (an actual finite execution that returns), `HeapSame`, `outcome` (a
record with the given site and outcome byte) and the two exclusions,
`InsertThenLookup` and `FailedInsertInvisible`, are in appendix A with
the layout, the literals, the executable caller conditions (`insertReady`,
`lookupReady`, `emptyTable` and what they call) and the ten instruction
terms `CallbacksFromImage` names
([appendix A](#appendix-a-the-rest-of-the-signed-text)). They are part of
what is signed.

**Sizes**, by the project's definition of trust surface (printed lines, the
way `binary/surface.py` prints the landed file; `measure-surface.py`):

| | Printed lines | Against revision 2 |
| --- | ---: | --- |
| **Assumed**: layout, service contract, `Premises` | 230 | same |
| **Assumed**: caller conditions and the starting point | 183 | same |
| **Assumed**: existing package definitions the premises draw in, not in the landed file | 174 | same |
| **Assumed, total new** | **587** | same |
| **Claimed**: `Headline` and its clauses, `SeqAdvanced`, the write sets | 80 | same |
| **Claimed**: existing definitions the conclusion draws in | 22 | same |
| **Claimed**: the witness, the exclusions, `Signed` | 127 | +6 (`CallbacksFromImage`) |
| **Claimed**: the ten instruction terms and their `fetch` | 75 | new (F1) |
| **Claimed, total new** | **304** | +81 |

Uncounted, as in the packet: the definitional closure of `Signed` is 988
hand-written declarations (982 in revision 2), 372 of them the mirror's,
188 Kraken's. The packet's proposed budget for the claimed kind was 230
printed lines; the claim proper is 229, and the listing F1 needs takes it
to 304. That listing is a reading of the image (ten instructions, checked
against the ELF by `binary/generate_c1_callbacks.py --check`), of the same
kind as the landed `ServiceImage`.

## 3. The difference from packet revision 2

Against `eb67564b`, `git diff -M eb67564b -- binary/` restricted to the
statement modules and the lake file. The headline, its clauses, the
premises, the contract, the caller conditions and both exclusions are
textually unchanged.

```diff
diff --git a/binary/Statements/C1/Contracts.lean b/binary/StatementC1Contracts.lean
rename from binary/Statements/C1/Contracts.lean
rename to binary/StatementC1Contracts.lean
--- a/binary/Statements/C1/Contracts.lean
+++ b/binary/StatementC1Contracts.lean
@@ -1,9 +1,9 @@
 import PairAllowedipsMutation
 import AllowedipsRootRecord
 
-/-! Statement packet C1 (no theorem, no proof): the layout a reader is told
+/-! Result C1, final statement (no theorem, no proof): the layout a reader is told
 about and the allocator/free contract. Everything here is a premise of the
-headline in `Statements.C1.Headline`: nothing in a proof polices it. -/
+headline in `StatementC1Headline`: nothing in a proof polices it. -/
 namespace Binary.Statements.C1
 open Leanux Leanux.WG Binary.Pair Binary.Pair.Allowedips Binary.TrustBase
 local instance : Labels := Image.linkedLabels
diff --git a/binary/Statements/C1/Headline.lean b/binary/StatementC1Headline.lean
rename from binary/Statements/C1/Headline.lean
rename to binary/StatementC1Headline.lean
--- a/binary/Statements/C1/Headline.lean
+++ b/binary/StatementC1Headline.lean
@@ -1,7 +1,7 @@
-import Statements.C1.Contracts
+import StatementC1Contracts
 import PairAllowedipsLookupAdequacy
 
-/-! Statement packet C1 (no theorem, no proof): the proposed headline for the
+/-! Result C1, final statement (no theorem, no proof): the headline for the
 compiled allowed-IPs insertion of the pinned s5 image, as `def … : Prop`.
 
 `Headline` keeps the memory relation internal (an existentially quantified
@@ -214,7 +214,7 @@ def LookupStep (fetch : Int64 → Option Decoded) (L : Layout)
       Inv w' t.data.dmem ∧
       EqualOutside (LookupWrites L c s) s.data.dmem t.data.dmem) s
 
-/-- THE PROPOSED HEADLINE. Under the premises there is an invariant, holding
+/-- THE HEADLINE. Under the premises there is an invariant, holding
 at every empty table, insensitive to memory outside the heap, preserved by
 every insertion and every lookup, under which each returns what the mirror
 returns. The relation between memory and the mirror is not part of the
diff --git a/binary/Statements/C1/Vacuity.lean b/binary/StatementC1Vacuity.lean
rename from binary/Statements/C1/Vacuity.lean
rename to binary/StatementC1Vacuity.lean
--- a/binary/Statements/C1/Vacuity.lean
+++ b/binary/StatementC1Vacuity.lean
@@ -1,7 +1,8 @@
-import Statements.C1.Headline
+import StatementC1Headline
+import StatementC1CallbackImage
 
-/-! Statement packet C1: the kernel-checked evidence against vacuity that the
-result carries, as statements (no theorem, no proof). `Witness` says the
+/-! Result C1, final statement: the kernel-checked evidence against vacuity that
+the result carries, as statements (no theorem, no proof), and `Signed`. `Witness` says the
 premises can be met along an actual execution through every kind of call;
 the two exclusions are consequences with no mirror state in their
 conclusion, naming machine behaviours the headline rules out. -/
@@ -20,8 +21,18 @@ def HeapSame (L : Layout) (t s : MachineState) : Prop :=
 
 def outcome (site : Nat) (ok : Bool) : HiddenRecord := ⟨site, (if ok then 1 else 0) :: List.replicate 39 0⟩
 
-/-- WITNESS (revision 2). Some `fetch`, layout and allocator meet every
-premise, and an actual execution runs, from a physically empty table with
+/-- The code at every coverage and BH-enable callback the premises name is
+the image's: `fetch` returns the committed decoded terms of
+`__sanitizer_cov_trace_pc`, `_cmp4`, `_const_cmp1`, `_const_cmp4`,
+`write_comp_data` and `__local_bh_enable_ip` (the landed `ServiceImage`) and
+of `__sanitizer_cov_trace_cmp1` and `_cmp8` (`StatementC1CallbackImage`). -/
+def CallbacksFromImage (fetch : Int64 → Option Decoded) : Prop :=
+  ServiceDecoderAgreement fetch ∧
+  ∀ pc instruction, StatementC1CallbackImage.fetch pc = some instruction → fetch pc = some instruction
+
+/-- WITNESS. Some `fetch`, layout and allocator meet every premise, the
+callbacks being the image's own code (`CallbacksFromImage`: only the code at
+`allocEntry` and `freeEntry` may be a stub), and an actual execution runs, from a physically empty table with
 the allocator idle and five answers pending, through: an insertion into the
 empty table; an insertion that allocates twice (the intermediate node,
 while a node is handed out); an insertion whose second allocation is
@@ -37,7 +48,7 @@ def Witness : Prop :=
     (s1 t1 s2 t2 s3 t3 s4 t4 : MachineState) (h1 h2 h3 h4 : List MachineState)
     (k1 n1 p1 k2 n2 p2 k3 n3 p3 key pointer : Nat) (found : PeerId) (ra : UInt64)
     (stream : List HiddenRecord),
-    Premises fetch L A ∧
+    Premises fetch L A ∧ CallbacksFromImage fetch ∧
     w0.wg.dev = some d0 ∧ armed w0 = true ∧
     w0.ambient.hidden = some ([outcome 77 true, outcome 78 true, outcome 79 true,
       outcome 78 true, outcome 79 false] ++ stream) ∧
@@ -120,9 +131,24 @@ def FailedInsertInvisible : Prop :=
         Eventually (instructionStep fetch) (fun t' =>
           Returned s' t' ra' ∧ t'.data.regs.rax.toNat = 0) s') s
 
-/-- WHAT IS SIGNED (revision 2): the headline together with the evidence
-against vacuity it relies on. The exclusions follow from `Headline` and
-facts about the mirror; the witness is independent of it. -/
+/-- WHAT IS SIGNED: the headline together with the evidence against vacuity
+it relies on. The exclusions follow from `Headline` and facts about the
+mirror; the witness is independent of it.
+
+What it establishes, in the words its summary and register entry use: the
+compiled `wg_allowedips_insert_v4`, `_v6`, `add.isra.0`, `lookup`,
+`common_bits` and `wg_peer_get_maybe_zero` of the s5 image return what the
+mirror returns along any sequence of insertions and lookups from an empty
+table, **given any code at the two service addresses that meets the stated
+contract; the image's allocator is not shown to, and under this semantic
+base cannot be**. About how the compiled code uses that service it
+establishes that the code calls it only with the cache and the flags the
+contract names and from states the contract covers; relies on nothing about
+a returned object but that it is zeroed, aligned, inside the arena and apart
+from the nodes handed out; never depends on the service's stack scratch, on
+the caller-saved registers it returns, on free arena bytes or on the bytes
+of a released object; and releases exactly the node it allocated, once, on
+the one failing path. -/
 def Signed : Prop :=
   Headline ∧ Witness ∧ InsertThenLookup ∧ FailedInsertInvisible
 
```

Also: `binary/StatementC1CallbackImage.lean` is new (whole text in appendix A), and in
`binary/lakefile.toml` the `roots` of `BinaryProofs` gain `"StatementC1Contracts"`,
`"StatementC1Headline"`, `"StatementC1CallbackImage"` and `"StatementC1Vacuity"` (one line of
about six hundred module names; not reproduced).


| Hunk | Reason |
| --- | --- |
| The three files renamed to `binary/StatementC1*.lean`; the two `import` lines | The binary gate scans `binary/*.lean` only and the package's modules are flat. As top-level modules and roots of `BinaryProofs` the statements are built by the package build and seen by the gate's source scan, with no change to the gate |
| File headers: "Statement packet C1" to "Result C1, final statement"; `Statements.C1.Headline` to `StatementC1Headline` | They are no longer a packet. Comment only |
| "THE PROPOSED HEADLINE" to "THE HEADLINE" | Decided. Comment only |
| `import StatementC1CallbackImage`; new `CallbacksFromImage`; the conjunct `CallbacksFromImage fetch` in `Witness`; the witness's comment | **F1.** The witness must have the image's own code at the coverage and BH-enable callbacks, so that only the code at the two service addresses may be a stub. `ServiceDecoderAgreement` is the landed agreement for `__sanitizer_cov_trace_pc`, `_cmp4`, `_const_cmp1`, `_const_cmp4`, `write_comp_data` and `__local_bh_enable_ip`; the package had no terms for `__sanitizer_cov_trace_cmp1` and `_cmp8`, which `Premises` also names |
| New file `binary/StatementC1CallbackImage.lean` (generated by the new `binary/generate_c1_callbacks.py`) | The ten instructions of those two callbacks as literal terms, in the form of `ServiceImage` |
| The comment on `Signed` | **F2.** Says what the result establishes about how the compiled code uses the service, and carries the sentence the review asked for in the form decided |
| `binary/lakefile.toml`: four roots added to `BinaryProofs` | The wiring |

Not statement text, changed to follow the move: `Test.lean` and
`Closure.lean` (the import line), `run-tests.sh` (the statements are built
by lake now; it also refuses `lemma`), `measure-surface.py` (paths, and the
new definitions in its lists). `binary/TrustSurface.expected.txt` and
`binary/surface.py` are not changed: the printed surface is for landed
headlines, and C1 is not one yet.

**The packet's tests on the final text** (`binary/Statements/C1/run-tests.sh`):
`PASS`. 23 families, 900 insertions, 4,124 lookups, every family `holds`
(110 lookups where the mirror refuses on saturating counts), deepest stack
write 200, 23 distinct mirror decisions in each; the 5 refusals; H1 and H2
under both contracts as in the packet. The test does not exercise `Witness`,
so it does not exercise F1's conjunct; F1 is checked by the build and by the
generator's comparison with the ELF.

**Register wording** (for `docs/proofs.md` when the result lands; not
entered now, since nothing is proved): the text of the comment on `Signed`.

## 4. What the owner is accepting knowingly

1. **Closed-world.** The invariant is hidden, so the conclusion holds only
   while nothing but these calls changes a heap byte or the mirror world. A
   later result on removal or the dump replaces this one; it cannot extend
   it. The capture makes this concrete: see section 5, item 1.
2. **Parent pointers, the peers' node lists and the internal nodes' list
   heads are not claimed.** Nothing with an observable conclusion reads
   them. (The landed relation, which does read them, held after each of
   the 20 calls evaluated; that is a test of one invariant instance.)
3. **The mirror's definition of an accepted run is inside the claim** and
   is not in the printed line counts: 372 declarations of the closure.
4. **Nothing is claimed of the kernel's allocator.** The result is about
   the six functions given any code at the two service addresses that meets
   the contract. Section 1 is how far the image's allocator was seen to be
   from it on 31 calls, not a discharge.
5. **Where the mirror refuses, the claim is silent**: a trie deeper than
   its bound, a lookup that would retry on a dying peer, a peer with a
   pending worker, a short record list, and reference-count saturation.
   The last is reachable inside the closed world: each lookup raises a
   count and nothing in scope lowers it (58 of 168 lookups refused in the
   packet's family that starts near 2^31).
6. **Decoder agreement is tested, not proved**: `fetch` returning the
   committed terms is a premise; that the terms are the ELF's bytes is the
   generators' `--check`, now including the ten new terms. The capture adds
   execution agreement on 20 calls. At the two service addresses the guest
   does not run the ELF's bytes at three sites.
7. **Sequential model.** One CPU stepping these instructions alone: no
   interrupt, no RCU reader during an insertion, no sleeping allocation.
   The capture deferred interrupts and timers to match.
8. **Instrumented image.** The saved s5 oracle build with KCOV callbacks,
   not a production kernel.

Unchanged from the packet and still to be accepted: the caller's conditions
are not shown to hold at any real call by proof (the capture shows them at
20); the over-long-prefix exit is not reachable from the real caller; the
NULL-peer exit is outside.

## 5. What the capture puts to the owner

Neither is changed in the statements.

1. **Whether the closed world should admit the caller's reference on a
   peer.** Evidence: section 1, point 5 and "Between calls". As signed, a
   run of a real `wg set` over two existing peers is inside the claim for
   the first peer's insertions and outside it from the second peer on,
   because `set_peer` moves a reference between the two peers' counts, and
   those words are in `Layout.fixed`. Options: (a) leave it, and say in the
   summary that the sequences covered are those between two changes of a
   reference count; (b) add a clause to `Headline`'s conjunction, beside
   `Framed`: the invariant survives a change of one peer's count in memory
   together with the mirror's `peerGet` or `peerPut` on that peer. That
   would bring every insertion of a `wg set` over existing peers inside
   (not peer creation, which changes the peer set). The landed relation
   compares counts, so (b) costs the proof little; it adds perhaps ten
   printed lines to the claim and a second kind of step a reader must
   understand. It can be decided while `InsertStep` is being proved, since
   that clause does not change; it must be decided before `Headline` is
   closed, because the result is replaced, not extended, afterwards. My
   recommendation is (b).
2. **Whether F1's listing is the right way to pin the two callbacks.** The
   repair needed terms for `__sanitizer_cov_trace_cmp1` and `_cmp8`; I added
   them as a new generated module rather than extending the landed
   `ServiceImage`, which five proved contracts depend on. The cost is 75
   printed lines of claimed surface beyond the packet's budget. The
   alternative is to pin only the six functions `ServiceImage` already has
   and say in the summary that the witness's `cmp1` and `cmp8` may be
   stubs: a partial repair.

For information, no decision needed: a service that records as the image's
does needs `depth` of at least 968 bytes and an arena containing the four
counters; with `kcov_choice_seq` in the arena, any other recorded choice
between calls is a change to the arena (seen in `b1_trie_routing`). The
witness's stub is not bound by either.

## Appendix A: the rest of the signed text

```lean
structure Layout where
  table : Nat
  peers : List (PeerId × Nat)
  arena : List Pair.Span
  cache : Nat

def Layout.fixed (L : Layout) : List Pair.Span :=
  tableFields.map (fun (offset,size) => (L.table+offset,size)) ++
  L.peers.flatMap (fun (_,a) => (peerFields Allowedips.Root.nodeOffsets).map (fun (offset,size) => (a+offset,size)))

def Layout.heap (L : Layout) : List Pair.Span := L.fixed ++ L.arena

def Layout.Arena (L : Layout) (a : BitVec 64) : Prop := ∃ span ∈ L.arena, span.contains a

def Layout.Heap (L : Layout) (a : BitVec 64) : Prop := ∃ span ∈ L.heap, span.contains a

def allocEntry : Int64 := .ofNat 0xffffffff81196d20   -- where the image has kmem_cache_alloc_noprof

def freeEntry : Int64 := .ofNat 0xffffffff81199b10    -- where the image has kmem_cache_free

def cacheWord : Nat := 0xffffffff81fdbe60             -- &node_cache

def allocSites : List (Nat × Nat) :=
  [(0xffffffff813a0d04,78),(0xffffffff813a0e52,79),(0xffffffff813a0ff2,77)]

def freeSite : Nat := 0xffffffff813a1252

def nodeSize : Nat := 72

def insertWindow : Nat := 200

def lookupWindow : Nat := 144

def callerSpans (s : MachineState) (window : Nat) (query : Pair.Span) (cache : Bool) : List Pair.Span :=
  [((s.data.regs.rsp.toBitVec - .ofNat 64 window).toNat, window+8), query] ++
    (if cache then [(cacheWord,8)] else [])

def frameReady (L : Layout) (c : Context) (s : MachineState) (ra : UInt64)
    (window : Nat) (query : Pair.Span) (cache bh : Bool) : Except String Unit := do
  require (s.data.regs.rsp.toNat % 8 == 0 &&
    s.data.dmem.loadInt s.data.regs.rsp.toBitVec 8 == some (ra.toNat : Int)) "c1.abi-return"
  require ((List.range window).all fun i =>
    (s.data.dmem.get? (s.data.regs.rsp.toBitVec - .ofNat 64 (i+1))).isSome) "c1.stack-mapping"
  require (Trie.coverageCheck c s.data.dmem) "c1.coverage"
  if cache then   -- what the services need (`ServiceReady`); `lookup` calls none
    require (if c.Needed then 0 < c.coverage.capacity.toNat else true) "c1.coverage-capacity"
    require (s.data.system.bits[10] == false) "c1.direction-flag"
  if bh then
    require (Trie.coverageDataCheck ⟨c.coverage,c.preempt+512⟩ s.data.dmem) "c1.coverage-bh"
    require ((c.preempt+512) &&& 0x000f0000 == 0) "c1.hardirq"
    require (if LookupPendingRead c.preempt then
      s.data.dmem.loadInt softirqPendingAddress 2 == some 0 else true) "c1.pending-softirq"
  let preempt := [(preemptCountAddress.toNat,4)]
  let own := callerSpans s window query cache
  require (spansApart L.heap (own ++ Trie.callServices c ++ Trie.callBuffers c)) "c1.heap-separation"
  require (spansApart (Trie.callServices c) [own.head!]) "c1.service-stack"
  require (spansApart (Trie.callBuffers c) (own ++ Trie.callMetadata c ++ preempt)) "c1.buffer-separation"
  require (spansApart ([own.head!] ++ Trie.callMetadata c ++ Trie.callHeaders c) preempt) "c1.preempt-separation"
  require (spansApart [((s.data.regs.rsp.toBitVec - .ofNat 64 window).toNat, window)] own.tail!) "c1.caller-separation"

def insertReady (L : Layout) (A : Allocator) (c : Context) (s : MachineState)
    (family key cidr pid : Nat) (ra : UInt64) : Except String Unit := do
  require (family == 4 || family == 6) "c1.family"
  let width := if family == 4 then 32 else 128
  require (s.pc == (if family == 4 then AllowedipsMutationImage.Insert4.entry
    else AllowedipsMutationImage.Insert6.entry)) "c1.insert-entry"
  require (s.data.regs.rdi.toNat == L.table) "c1.insert-table"
  let peer ← Trie.address L.peers (some pid)
  require (peer != 0 && s.data.regs.rcx.toNat == peer) "c1.insert-peer"
  require (s.data.regs.rdx.toNat % 256 == cidr) "c1.insert-cidr"
  require (Trie.networkKeyCheck s.data.dmem s.data.regs.rsi.toBitVec width key) "c1.insert-address"
  require ((← readNat s cacheWord 8) == L.cache) "c1.node-cache"
  frameReady L c s ra (insertWindow + A.depth) (s.data.regs.rsi.toNat, width/8) true false

def lookupReady (L : Layout) (c : Context) (s : MachineState)
    (family key : Nat) (ra : UInt64) : Except String Unit := do
  require (family == 4 || family == 6) "c1.family"
  let width := if family == 4 then 32 else 128
  let slot := L.table + (if family == 4 then AllowedipsMutationLayout.root4 else AllowedipsMutationLayout.root6)
  require (s.pc == AllowedipsImage.Lookup.entry) "c1.lookup-entry"
  require (s.data.regs.rdi.toNat == (← readNat s slot 8)) "c1.lookup-root"
  require (s.data.regs.rsi.toNat == width) "c1.lookup-width"
  require (Trie.networkKeyCheck s.data.dmem s.data.regs.rdx.toBitVec width key) "c1.lookup-address"
  frameReady L c s ra lookupWindow (s.data.regs.rdx.toNat, width/8) false true

def armed (w : World) : Bool :=
  ["allocNode190","allocNode205","allocNode234"].all w.ambient.allocArmed.contains

def emptyTable (L : Layout) (m : Mem 64) (d : Device) : Except String Unit := do
  let s : MachineState := ⟨{dmem := m},0⟩
  require (0 < L.table && L.table % 8 == 0) "c1.table-address"
  require ((← readNat s (L.table+AllowedipsMutationLayout.root4) 8) == 0 &&
    (← readNat s (L.table+AllowedipsMutationLayout.root6) 8) == 0) "c1.roots"
  require ((← readNat s (L.table+AllowedipsMutationLayout.seq) 8) == d.peerAllowedips.seq.toNat) "c1.seq"
  require (d.peerAllowedips.root4.isNone && d.peerAllowedips.root6.isNone && d.nodes.isEmpty) "c1.mirror-empty"
  require (L.peers.map (·.1) == d.peers.toList.map (·.1)) "c1.peer-identities"
  for (id,a) in L.peers do
    let some p := d.peers.get? id | throw "c1.peer"
    let head := a+AllowedipsMutationLayout.allowedips_list
    require (0 < a && a % 8 == 0 && p.allowedipsList.isEmpty) "c1.peer-address"
    require ((← readNat s head 8) == head && (← readNat s (head+8) 8) == head) "c1.peer-list"
    require ((← readNat s (a+Root.nodeOffsets.peerRefcount) 4) == p.refcount) "c1.peer-refcount"
  let objects := [(L.table,AllowedipsMutationLayout.tableSize)] ++ L.peers.map fun (_,a) => (a,Layouts.peerSize)
  require (objects.zipIdx.all fun ((a,size),i) => a+size < 2^64 &&
    (objects.drop (i+1)).all fun (b,size') => disjointRanges a size b size') "c1.object-overlap"
  require (spansApart objects L.arena) "c1.arena-overlap"

def Ran (fetch : Int64 → Option Decoded) (s t : MachineState) (ra : UInt64)
    (history : List MachineState) : Prop :=
  ActualHistory fetch s history ∧ history.getLast? = some t ∧ Returned s t ra

def HeapSame (L : Layout) (t s : MachineState) : Prop :=
  ∀ a, L.Heap a → t.data.dmem.get? a = s.data.dmem.get? a

def outcome (site : Nat) (ok : Bool) : HiddenRecord := ⟨site, (if ok then 1 else 0) :: List.replicate 39 0⟩

def LookupAfter (L : Layout) (t s : MachineState) (c : Context) (family key : Nat) (ra : UInt64) : Prop :=
  HeapSame L t s ∧ lookupReady L c s family key ra = .ok ()

def MirrorAccepts (w : World) (family key cidr pid : Nat) : Prop :=
  ∃ answer w' d' found w'', (liftWG (WG.insert family key cidr pid)).run w = .ok (answer, w') ∧
    w'.wg.dev = some d' ∧
    (Source.lookup (if family == 4 then d'.peerAllowedips.root4 else d'.peerAllowedips.root6)
      (if family == 4 then 32 else 128) key).run w' = .ok (found, w'')

def InsertThenLookup : Prop :=
  ∀ (fetch : Int64 → Option Decoded) (L : Layout) (A : Allocator), Premises fetch L A →
  ∀ (w : World) (d : Device) (c : Context) (s : MachineState) (family key cidr pid peer : Nat)
    (ra : UInt64) (stream : List HiddenRecord),
    w.wg.dev = some d → armed w = true →
    w.ambient.hidden = some (⟨77, 1 :: List.replicate 39 0⟩ :: stream) →
    (∀ record ∈ stream, record.site ∈ allocSites.map (·.2)) →
    emptyTable L s.data.dmem d = .ok () →
    A.Idle s.data.dmem [] (⟨77, 1 :: List.replicate 39 0⟩ :: stream) →
    insertReady L A c s family key cidr pid ra = .ok () →
    cidr ≤ (if family = 4 then 32 else 128) →
    Trie.address L.peers (some pid) = .ok peer →
    MirrorAccepts w family key cidr pid →
    Eventually (instructionStep fetch) (fun t =>
      Returned s t ra ∧ t.data.regs.get (.low .rax .W32) = 0#32 ∧
      ∀ (s' : MachineState) (c' : Context) (ra' : UInt64), LookupAfter L t s' c' family key ra' →
        Eventually (instructionStep fetch) (fun t' =>
          Returned s' t' ra' ∧ t'.data.regs.rax.toNat = peer ∧ peer ≠ 0) s') s

def FailedInsertInvisible : Prop :=
  ∀ (fetch : Int64 → Option Decoded) (L : Layout) (A : Allocator), Premises fetch L A →
  ∀ (w : World) (d : Device) (c : Context) (s : MachineState) (family key cidr pid : Nat)
    (ra : UInt64) (stream : List HiddenRecord),
    w.wg.dev = some d → armed w = true →
    w.ambient.hidden = some (⟨77, 0 :: List.replicate 39 0⟩ :: stream) →
    (∀ record ∈ stream, record.site ∈ allocSites.map (·.2)) →
    emptyTable L s.data.dmem d = .ok () →
    A.Idle s.data.dmem [] (⟨77, 0 :: List.replicate 39 0⟩ :: stream) →
    insertReady L A c s family key cidr pid ra = .ok () →
    cidr ≤ (if family = 4 then 32 else 128) →
    MirrorAccepts w family key cidr pid →
    Eventually (instructionStep fetch) (fun t =>
      Returned s t ra ∧ t.data.regs.get (.low .rax .W32) = BitVec.ofInt 32 (-12) ∧
      ∀ (s' : MachineState) (c' : Context) (ra' : UInt64), LookupAfter L t s' c' family key ra' →
        Eventually (instructionStep fetch) (fun t' =>
          Returned s' t' ra' ∧ t'.data.regs.rax.toNat = 0) s') s
```

`binary/StatementC1CallbackImage.lean`, whole:

```lean
import LiteralDecode
namespace Binary.StatementC1CallbackImage
-- Generated by binary/generate_c1_callbacks.py from the pinned ELF: __sanitizer_cov_trace_cmp1 and
-- __sanitizer_cov_trace_cmp8. A parser rejection is a missing PC, never a no-op.
def decoded : List (Nat × Nat × Option Instr) := [
  (18446744071579844672, 4, literalInstruction("mov    (%rsp),%rcx")),
  (18446744071579844676, 4, literalInstruction("movzbl %sil,%edx")),
  (18446744071579844680, 4, literalInstruction("movzbl %dil,%esi")),
  (18446744071579844684, 2, literalInstruction("xor    %edi,%edi")),
  (18446744071579844686, 5, literalInstruction("jmp L_ffffffff810f3fb0")),
  (18446744071579844768, 4, literalInstruction("mov    (%rsp),%rcx")),
  (18446744071579844772, 3, literalInstruction("mov    %rsi,%rdx")),
  (18446744071579844775, 3, literalInstruction("mov    %rdi,%rsi")),
  (18446744071579844778, 5, literalInstruction("mov    $0x6,%edi")),
  (18446744071579844783, 5, literalInstruction("jmp L_ffffffff810f3fb0"))]
def fetch (pc : Int64) : Option Decoded := do
  let (_, size, code) ← decoded.find? (fun row => row.1 == pc.toUInt64.toNat)
  match code with
  | some instruction => some ⟨instruction, size⟩
  | _ => none
end Binary.StatementC1CallbackImage
```

## Appendix B: reproduction

From the worktree root, with the saved s5 image (`LEANUX_BINARY_KERNEL_DIR`,
default `.artifacts/kernel-net-choice-s5` in the main checkout), a host
Python with pyelftools, and the package bootstrapped (`binary/README.md`):

```sh
cap() { if command -v capped >/dev/null 2>&1; then capped -- "$@"; else "$@"; fi; }
cap scripts/in-bundle lake -d binary build                                   # 1,123 jobs
cap scripts/in-bundle /usr/bin/python3 scripts/binary-proof-gate             # PASS
cap scripts/in-bundle /usr/bin/python3 -B binary/generate_c1_callbacks.py --check
cap scripts/in-bundle /usr/bin/python3 -B binary/allowedips_mutation.py      # writes the tests' input
binary/Statements/C1/run-tests.sh                                            # about 18 minutes; PASS
binary/Statements/C1/capture/run-capture.sh                                  # about 10 minutes
cap scripts/in-bundle /usr/bin/python3 -B binary/Statements/C1/measure-surface.py
```

`run-capture.sh` records each trace (`evaluator.check --binary-coverage
--binary-profile allowedips-insert`), captures it
(`capture_insertions.py`), analyses it (`analyse.py`), runs `Check.lean`
on it, runs the verbatim readiness check on the grid's first call with the
whole buffer loaded (about three minutes, 5.4 GiB), and prints the counts
(`summarise.py`). The grid trace is copied into `corpus/wireguard` for its
recording and removed again; it is not a corpus trace. Outputs are under
`.artifacts/check/c1-*` and `.tmp/c1/capture-*`, ignored and not committed:
up to about 90 MiB per trace, the RAM dumps deleted as they are compared.

The run reported here: s5 image `06513d05…e88e`, Kraken `43df9468`, QEMU's
`qemu64` CPU under TCG, 256 MiB, one CPU, `nokaslr`.

## Appendix C: the calls

`service@site:result`; sites 77, 78, 79 are the mirror's record sites for
`allowedips.c:190`, `:205`, `:234`. Steps are native instructions between
the wrapper's entry and its return.

| Trace | Call | Arguments | Service calls | `eax` | Steps |
| --- | ---: | --- | --- | ---: | ---: |
| `c1_capture_grid` | 0 | v4 0a010000/16 peer 0 | alloc@77:obj | 0 | 8274 |
| `c1_capture_grid` | 1 | v6 fd000001/32 peer 0 | alloc@77:obj | 0 | 6666 |
| `c1_capture_grid` | 2 | v4 0a010200/24 peer 0 | alloc@78:obj | 0 | 7075 |
| `c1_capture_grid` | 3 | v4 0a010300/24 peer 0 | alloc@78:obj alloc@79:obj | 0 | 13938 |
| `c1_capture_grid` | 4 | v4 0a01c800/24 peer 0 | alloc@78:obj | 0 | 7075 |
| `c1_capture_grid` | 5 | v4 0a010000/16 peer 1 | no service call | 0 | 480 |
| `c1_capture_grid` | 6 | v4 0a000000/8 peer 1 | alloc@78:obj | 0 | 7036 |
| `c1_capture_grid` | 7 | v4 c0a80000/16 peer 1 | alloc@78:obj alloc@79:obj | 0 | 13676 |
| `c1_capture_grid` | 8 | v4 0a018000/17 peer 1 | alloc@78:obj | 0 | 7790 |
| `c1_capture_grid` | 9 | v6 fd000002/32 peer 1 | alloc@78:obj alloc@79:obj | 0 | 13803 |
| `c1_capture_grid` | 10 | v6 fd000000/8 peer 1 | alloc@78:obj | 0 | 7101 |
| `c1_capture_grid` | 11 | v6 fd000001/32 peer 1 | no service call | 0 | 1276 |
| `c1_capture_grid` | 12 | v4 0a010203/32 peer 1 | alloc@78:obj | 0 | 8059 |
| `a2_allowedips_root_nomem` | 0 | v4 0a000000/8 peer 0 | alloc@77:NULL | -12 | 6616 |
| `a2_allowedips_newnode_nomem` | 0 | v4 0a000000/8 peer 0 | alloc@77:obj | 0 | 8340 |
| `a2_allowedips_newnode_nomem` | 1 | v4 0a010000/16 peer 0 | alloc@78:NULL | -12 | 6924 |
| `a2_allowedips_split_nomem` | 0 | v4 0a000000/8 peer 0 | alloc@77:obj | 0 | 8340 |
| `a2_allowedips_split_nomem` | 1 | v4 c0a80000/16 peer 0 | alloc@78:obj alloc@79:NULL free@:237 | -12 | 13718 |
| `b1_trie_routing` | 0 | v4 0a000000/8 peer 0 | alloc@77:obj | 0 | 8274 |
| `b1_trie_routing` | 1 | v6 fd000000/8 peer 0 | alloc@77:obj | 0 | 6666 |
| `b1_trie_routing` | 2 | v4 0a010000/16 peer 1 | alloc@78:obj | 0 | 7075 |
| `b1_trie_routing` | 3 | v6 fd000001/32 peer 1 | alloc@78:obj | 0 | 7140 |
| `b1_trie_routing` | 4 | v4 0a010200/24 peer 2 | alloc@78:obj | 0 | 7321 |
| `b1_trie_routing` | 5 | v4 0a010203/32 peer 3 | alloc@78:obj | 0 | 7567 |
| `b1_trie_routing` | 6 | v4 c0a80000/16 peer 3 | alloc@78:obj alloc@79:obj | 0 | 13676 |
| `b1_trie_routing` | 7 | v6 fd000002/32 peer 4 | alloc@78:obj alloc@79:obj | 0 | 14165 |

The arena drawn for the grid (23 spans; 5, 21, 22 and 22 for the other traces): the slab page
`0xffff888006e36000` (4,096 bytes), and byte ranges in
`kcov_alloc_unwind_cycles`, `kcov_alloc_unwinds`, `kcov_alloc_records`,
`kcov_choice_seq`, `vm_event_states`, `contig_page_data`, `vm_node_stat`,
the cache's per-CPU structure, its node structure, the per-CPU page lists
and the new page's `struct slab`. It is the set of bytes that changed, not
the objects: a proof-grade layout would name whole objects.
