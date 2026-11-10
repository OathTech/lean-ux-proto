# Independent review: statement packet C1 (the compiled allowed-IPs insertion)

2026-11-10. Reviewed: `docs/2026-11-10-statement-packet-c1-insertion.md` and
`binary/Statements/C1/` at `954f8c1d` (branch `task/binary-c1-statement`).
Written on `task/review-c1-statement` in its own worktree
(`.worktrees/review-c1-statement`), with build outputs copied from
`.worktrees/binary-reassessment` and replayed by Lake (1,119 jobs, nothing
recompiled). Inputs read: the packet and its six files; `binary/TrustBase.lean`,
`CommonBitsCoverage.lean`, `Execution.lean`, `Memory.lean`, `PairLoopCheck.lean`,
`PairAllowedipsMutation.lean`; the mirror's `Leanux/WG/AllowedIps.lean`,
`Device.lean`, `Peer.lean` and the allocation-record code of
`Leanux/Kernel/Defs.lean`; the s5 `vmlinux`
(`.artifacts/kernel-net-choice-s5`, sha256 `06513d05…`);
`kernel/patches/choice-stream.patch` (sha256 `630b602a…`, the s5 patch);
`kernel/config-x86_64-net-choice`; the pinned Kraken checkout; trial T4's
contract on `task/binary-trials`; the trust-surface definition in
`docs/decisions.md` at `5accd5fb`; the reassessment's review at `921a125d`.
The judgements are mine [AGENT]. Part of the evidence rerun (section 1,
items marked *delegated*) was done by a second agent instance I started and
whose report I spot-checked; the allocator reading and the reading of the
statements are my own.

## Verdict

**Do not sign the packet as it stands. The headline's shape is sound and can
be signed after four named changes to the allocator contract and the
witness; two of them are defects that make the statement, as written,
either unprovable or silent about every allocating call.**

- The headline's form is right. The existentially quantified invariant
  cannot be discharged trivially or clause by clause, and it gives what the
  packet says: agreement of every return value along a call sequence
  (section 2). Its limits are real but are the ones the packet lists, plus
  one it does not: the result is closed-world and cannot be composed with a
  later one (M3).
- The allocator and free contract is not yet a statement to sign.
  - It permits a conforming service to overwrite nodes it handed out
    earlier, so `InsertStep` cannot be proved from it and `Headline` is false
    for a conforming stub (H1).
  - It promises a return from states in which no code that uses its stack
    can return, and its own frame clause stops `Idle` from excluding them;
    for any such allocator the premise forces `Idle` to be false and the
    theorem says nothing about a call that allocates (H2).
  - Under the pinned semantics the image's own allocator cannot meet it in
    either mode, for reasons unrelated to its content: instructions with no
    semantics on every allocating path, and two boot-patched sites (H3).
    What would be proved is a property of WireGuard's six functions against
    *any* service meeting the contract. The packet should say that in those
    words.
- The reading of the recording hook the packet asked for is done
  (section 3). The two beliefs it was to test hold with one corner
  (a zero-capacity area). What it turned up is elsewhere: the hook writes
  six things outside the coverage buffer that the contract does not
  mention, its unwinder breaks the frame clause, and the recorded outcome is
  an output of the call, not an input (M1, M2).
- The packet's evidence reproduces exactly and no mirror/binary discrepancy
  appeared in it or in my additional runs. It does not test the contract:
  H1 and H2 are invisible to it (M5).

## 1. Checks run

| Check | Command or method | Result |
| --- | --- | --- |
| Packet's test | `binary/Statements/C1/run-tests.sh` after `lake -d binary build` and `/usr/bin/python3 -B binary/allowedips_mutation.py`, all through `capped` and `scripts/in-bundle` | `PASS`, exit 0; 32 `ok` rows per seed, eight variants rejected, five plus two refusals. 70 s wall (the packet says about ten). Run twice (once *delegated*, once by me) |
| Generator under the bundle's Python | `scripts/in-bundle python3 -B binary/allowedips_mutation.py` | Fails, `ModuleNotFoundError: elftools`; needs the host interpreter as `binary/README.md` says. The script header does not say so (*delegated*) |
| Literals | `nm`, `objdump -d`, `addr2line` on the s5 `vmlinux` | `allocEntry`, `freeEntry`, `cacheWord`, the three return sites (each after `mov node_cache(%rip),%rdi; mov $0xdc0,%esi; call kmem_cache_alloc_noprof`), `freeSite`, `nodeSize` 72 (the size passed by `wg_allowedips_slab_init`, alignment 8) all confirmed; sites 77/78/79 are lines 190/205/234 and the mirror's ids 7/8/9 (`Leanux/Kernel/Defs.lean:806-808`). The comment at `Contracts.lean:33` says `:236` for the release; `addr2line` gives 237 (*delegated*; I confirmed the entries and `node_cache`) |
| Instruction counts | `objdump` | 26, 29, 506, 103, 73, 76 = 813, 88 coverage calls: exact (*delegated*) |
| Text patching in range | parsed `.altinstructions` (847 entries); `readelf -S`; the config | No entry in any of the six functions; no jump-label, retpoline, return-thunk, ftrace or static-call section in the image. `kmem_cache_alloc_noprof+0x85`, `+0x91` and `kmem_cache_free+0xf4` are alternatives sites (H3) |
| Allocator and hook | `objdump -d` of `kmem_cache_alloc_noprof`, `kmem_cache_free`, `this_cpu_cmpxchg16b_emu`, `__kcov_alloc_pre`, `__kcov_alloc_post`, `kcov_alloc_chain`, `kcov_choice_write`, against the patch source | Section 3 |
| Kraken's instruction set | `grep` over the patched checkout's `Kraken/X64/Syntax.lean` and `Semantics.lean` | `pushf`, `cli`, `sti`, `stos`, `cmpxchg` present; no `popf`, `prefetch*`, `cmpxchg16b`, `rdtsc` |
| Mirror side | read `insert`, `add`, `allocNode`, `hiddenAlloc`, `allocRecord`, `lookup`, `peerGetMaybeZero` | Section 2 and M4 |
| Further executions | a copy of the test with v4 and v6 insertions interleaved on one table, repeated keys, a rollback then a retry, /0 and /128, and after each insertion a lookup of every earlier key in both families (11 insertions, about 90 lookups, two seeds); corruption of a parent word, a list link and the sequence word after two insertions | All agree with the mirror; `assertAt` rejects each corruption (*delegated*; files were untracked and are removed) |
| Surface measurement | `python3 binary/Statements/C1/measure-surface.py`; a computed transitive closure of `Headline` | Every figure of the packet's section 4 reproduces; the closure is 847 project constants (M6) (*delegated*) |
| The T4 address | `grep` on `task/binary-trials` | `0xffffffff81fe4a60` occurs only in T4's `Statement.md:81` and `LOG.md`; T4's Lean literal (`T4Regions.lean:70`) is the correct `0xffffffff81fdbe60`. A slip in the notes; no T4 proof depends on it (*delegated*) |

Not run: the package build from sources, the binary gate, `lake check`, any
guest boot or kernel capture, and any Lean proof of the arguments in H1, H2
and section 2 (they are arguments from the definitions, with the lines
cited).

## 2. What a signer would be asserting

In my words, from `Headline.lean` and everything it mentions.

For every instruction map `fetch`, layout `L` and allocator description `A`
such that: `fetch` returns the committed decoded instructions of the two
wrappers, `add.isra.0`, `lookup`, `common_bits` and `wg_peer_get_maybe_zero`;
the code `fetch` gives at the five coverage callbacks and BH-enable meets
their landed contracts; and the code `fetch` gives at two addresses meets the
allocator and free contract for some predicate `A.Idle` and stack bound
`A.depth` — there is a relation `Inv` between mirror worlds and memories with
four properties.

1. It holds whenever the mirror's table is empty, the three sites are armed,
   the mirror's whole pending record list consists of allocation records for
   these sites, the machine's table words are zero, peers' lists are empty
   and counts agree, and `A.Idle` holds with nothing handed out and that same
   list.
2. It depends only on the table's three words, each peer's count and list
   head, and the arena.
3. From any state in it, at either wrapper's entry with the caller's
   conditions, if the mirror's `insert` on the same arguments returns
   normally, the machine reaches the return address with `eax` the mirror's
   result, the relation holding for the mirror's next world, and memory
   changed only in the stack window, the coverage buffer and the heap.
4. The same for the compiled `lookup` against the mirror's `lookup`, with
   `rax` the layout's address of the peer the mirror returns.

**The existential cannot be gamed.** Any `Inv` meeting the four clauses
contains every pair (world, memory) reachable from a starting pair by calls
whose conditions hold and whose mirror runs are accepted, with arbitrary
changes outside the heap in between: clause 1 puts the start in, clause 3 and
4 put each successor in, clause 2 the changed memories. At each such pair
clauses 3 and 4 give the machine's result. So `Headline` implies the trace
statement the packet gives in words, and the least such relation shows the
converse. One relation serves both operations, so the lookup observes the
memory the insertions actually left; the clauses cannot be discharged
separately. An invariant that holds only at the empty table fails clause 3,
whose conclusion demands it at the mirror's next world.

There is one degenerate instance, and it is the allocator's: if `A.Idle` is
never true, the contract holds vacuously, clause 1 is empty, and `Inv :=
False` satisfies everything. The headline's content therefore lies entirely
in instances where `Idle` holds of real states, which is what H2, H3 and M4
are about.

**Which sequences.** Any finite interleaving of IPv4 and IPv6 insertions
(repeated keys, reassignments, failures and the rollback included) and
lookups of any key in either family, on one table with a fixed set of peers,
where:

- the mirror world after one call is exactly the mirror world before the
  next: no other mirror operation in between (no removal, no peer creation
  or release, no packet path taking or dropping a peer reference, no other
  consumer of the record list);
- the mirror's pending records are allocation records for these three sites
  and nothing else, from the start;
- nothing but these calls changes the table words, the peers' counts and
  list heads, or any byte of the arena between calls;
- each call meets `insertReady` / `lookupReady`, and the mirror accepts it.

Lookups raise the peer's count each time and nothing in scope lowers it.
The claim is about `eax` and `rax` only.

**Is the explicit alternative the better thing to sign?** No, with one
reservation. `HeadlineExplicit` would put 441 printed lines of relation into
the claim, of which the parent pointers, list links and sequence counter are
pinned by nothing a reader can check but tests. The reservation is M3:
under `Headline` the increment of the sequence counter, one of the two
things a wrapper does besides calling `add`, is not claimed at all, and the
result cannot be extended, only replaced.

## 3. The allocator's code against the contract

Image facts first (all from the disassembly; UP build, `CONFIG_PREEMPT_NONE`,
no `PREEMPT_COUNT`, `CONFIG_SLUB_DEBUG=y`, no failslab, memcg, KASAN, KFENCE).

`kmem_cache_alloc_noprof` (0x…81196d20, 134 instructions):

- pushes `rbp`, `r15`–`r12`, `rbx`, aligns the stack to 16 and takes 0x50
  bytes; zeroes the hook's context with `rep stos`;
- loads `gfp_allowed_mask` and `kcov_alloc_armed`. Armed: calls
  `__kcov_alloc_pre(ctx, return address, gfp & mask, s->object_size, 0)`; a
  true result returns NULL at once with no post call (the forced failure);
- fast path: reads `s->cpu_slab` (a direct address, no `%gs`), the per-CPU
  `freelist`, `tid`, `slab`; reads the next-free pointer inside the object;
  `call this_cpu_cmpxchg16b_emu` (`pushf; cli; cmp; mov; popf`);
  `prefetcht0`;
- slow path (`freelist` or `slab` NULL): `___slab_alloc`, then the page
  allocator;
- reads `init_on_free`, `init_on_alloc`, `slub_debug_enabled`; with
  `__GFP_ZERO` and a non-NULL object, `__memset(object, 0, s->object_size)`;
- if the context is active, `__kcov_alloc_post(ctx, object != NULL)`;
- restores the six registers and returns the object.

There is no call to `__cond_resched`, `__might_sleep` or `should_failslab`
on the fast path: it does not sleep. The flags are used for the zero bit,
passed to the slow path, and shown to the hook; nothing else reads them.

`kmem_cache_free` (0x…81199b10): no hook and no record. Reads
`slub_debug_enabled`, `phys_base`, `mem_section`, the object's `struct page`
(the slab type byte), `init_on_free`, the cache and its per-CPU state. Fast
path: stores the old `freelist` into the freed object at `s->offset` and
swaps the per-CPU `freelist`/`tid` through the same `cmpxchg16b` emulation.
Otherwise a tail jump to `__slab_free`.

The hook in recording mode (`__kcov_alloc_pre` 0x…810f3b00,
`__kcov_alloc_post` 0x…810f3ef0; the compiled code follows the patch source
at lines 1042-1091):

- reads `current`, the preempt count (tested against `0xff0100`, never
  written), `t->kcov_softirq` (0x704), `kcov_mode` (0x6e0), `kcov_size`
  (0x6e4), `kcov_area` (0x6e8): the same words and the same gate as the
  callbacks, which is what `Context.Needed` encodes;
- reads `kcov_alloc.n`, `.flags` and the armed ranges; reads and (when it
  proceeds) increments the task's `kcov_leanux_in_alloc` (0x710), decremented
  again by the post call;
- `kcov_alloc_chain`: `rdtsc`, `stack_trace_save` (the ORC unwinder over the
  task's stack above the call, up to 16 entries), increments
  `kcov_alloc_unwinds`, `rdtsc`, adds to `kcov_alloc_unwind_cycles`;
- `kcov_steer_alloc`: `kcov_steer_find(t)` (reads `t->kcov`, `t->kcov_handle`,
  the remote table under `pushf; cli … sti`), walks the schedule, and on a
  named encounter increments `steer->head` or `steer->mismatches`; a `fail`
  entry at the head forces NULL; with `KCOV_STEER_CHAIN` the match uses the
  unwound return addresses;
- `kcov_choice_write` → `kcov_choice_write_area`: reads `area[0]`; if the
  record does not fit, writes `size - 1` (PC mode) or `(size - 1) / 4`
  (comparison mode) to `area[0]` and increments `t->kcov_leanux_dropped`
  (0x708); otherwise increments the global `kcov_choice_seq`, advances
  `area[0]` by 8 (PC mode) or 3 records (comparison mode) and writes 8 or 12
  words inside the area. The outcome byte is bit 0 of the first data word.
  The record is written by the post call, after the allocation, or by the
  pre call for a forced failure. A mismatch marker (3 or 4 words) may
  precede it. `kcov_alloc_records` is incremented.

Clause by clause. "Non-recording" is `kcov_alloc_armed` clear, the task in no
KCOV mode, or the site outside the armed ranges. "Yes*" means: for a layout
whose arena is drawn to contain the named words, which the contract permits.

| Clause | Non-recording | Recording | Notes |
| --- | --- | --- | --- |
| Entry: `rdi` the cache, `esi = 0xdc0`, return address one of three (`alloc`); `rdi`, `rsi ∈ live`, one return address (`free`) | Yes | Yes | The three sites and the release site load exactly these. `0xdc0` is `GFP_KERNEL \| __GFP_ZERO` |
| Entry conditions the clause does not state | **No** | **No** | The code needs a mapped stack below `rsp` (first instruction `push %rbp`), the direction flag clear (`rep stos`), and in recording mode a capacity of at least one word and a mapped, well-formed stack *above* the call for the unwinder. The landed random-provider contract states the first three (`RandomReady.stackMapped`, `.forward`, `.capacity`, `TrustBase.lean:695-700`); this one states none. H2 |
| `Returned`: caller's return address, `rsp + 8`, six callee-saved registers | Yes on the fast path and the forced failure; slow path whenever it returns | Same | `lea -0x28(%rbp),%rsp` and six pops. `kmem_cache_free`'s slow path returns through `__slab_free`'s own epilogue |
| Writes only `Scratch`, the arena, the coverage buffer | Yes* on the fast path: its frame (about 150 bytes with the emulation's `pushf`), per-CPU `freelist`/`tid`, the object. Slow path: only if nothing else runs while it sleeps | Yes* for the buffer words (all inside `KcovBufferBytes`). **Not mentioned**: `kcov_choice_seq`, `kcov_alloc_records`, `kcov_alloc_unwinds`, `kcov_alloc_unwind_cycles`, `steer->head` / `->mismatches`, `t->kcov_leanux_dropped` on overflow. The in-progress counter at 0x710 is restored | The arena is "whatever the instantiator says", so these can be put in it; then the arena is not the slab's territory but a set containing a counter every recorded choice in the kernel increments. M1 |
| Writes do not touch nodes already handed out | Yes for the real allocator | Yes | **The contract does not require it** (`ServiceWrites` contains the whole arena, live objects included). H1 |
| `c.At` afterwards: same task, mode, capacity, area; count within capacity; every word readable; preempt count unchanged | Yes, trivially | **Yes, for capacity ≥ 1.** The count becomes `pos + 8`, `count + 3`, `size - 1` or `(size - 1)/4`, each ≤ capacity; no metadata word is written; the preempt count is only read | With `kcov_size = 0` the overflow branch stores `0xffffffff` in `area[0]`, outside `KcovBufferBytes`. Unreachable in a running kernel, but the clause quantifies over every context. Fix: the precedent's capacity condition |
| Result on record byte 0: NULL | Yes when the allocation fails | Yes, natural or forced | |
| Result on record byte 1: non-NULL, 8-aligned, inside the arena, apart from live objects, 72 zero bytes | Yes: the cache's size is 72 and alignment 8; zeroing is `memset(object, 0, s->object_size)` | Same | Zeroing depends on `s->object_size` in memory being 72 and the cache having no constructor; both are properties of the arena, hence of `Idle` |
| The outcome is the next pending record (`Idle … (record :: stream)` before the call) | No carrier: no record is produced in this mode | The record is **written by the call**, with outcome byte `object != NULL`; before the call nothing in memory holds it, except a `fail` entry at the head of a loaded steering schedule | As a precondition it is foreknowledge in both modes. It is consistent (the record a recorded run yields is the outcome), not checkable. If the record is dropped (area full) or the site is outside the armed ranges, the mirror's list is short and the mirror refuses. M2 |
| `frame`: `Idle` does not depend on bytes outside the arena or inside live objects | Yes* (globals, `struct kmem_cache`, per-CPU state, `struct page` for free, all in the arena); the allocator never reads a handed-out object | **No.** The unwinder reads the stack above the call (outside the arena by the caller's conditions) and the ORC tables; a store or load to unmapped memory is a failure in Kraken, so termination depends on those bytes. With a chain-flagged steering entry the *outcome* depends on return addresses above the wrapper's frame | M1 |
| `free`: returns, same write set, `Idle (live.erase object) stream` | Yes* on the fast path (one store into the freed object, the per-CPU swap); slow path as for `alloc` | Identical: `kmem_cache_free` has no hook | "Same stream" excludes a natural failure after a release. M2 |
| Sequential execution | Fast paths: yes, interrupts apart. Slow path: `GFP_KERNEL` may reclaim and schedule; what runs meanwhile can change peer counts, which are heap words the contract says the call does not write | Same; a reschedule inside a task section also writes a record | Disclosed by the packet (belief 1). The statement is about a quiescent machine |

What the code does that the contract neither permits nor mentions, in one
list: the stack, direction-flag and capacity entry conditions; six global or
task words written in recording mode; the unwinder's reads above the frame;
`rdtsc` (twice per recorded allocation); the interrupt flag (`pushf`/`cli`/
`popf` on every fast path); the dependence of a steered outcome on the
calling task's KCOV handle and schedule; the boot-time patching of three
sites.

## 4. Findings

### H1. The contract lets a conforming service overwrite nodes it has handed out; the headline is not provable from it

`ServiceWrites L A c s a := Scratch s A.depth a ∨ L.Arena a ∨ c.writes a`
(`Contracts.lean:57-59`), and the `alloc` and `free` clauses conclude only
`EqualOutside (ServiceWrites …)` (`:88`, `:95`). Objects handed out lie
inside the arena (`AllocResult`, `:69`). Nothing says a call leaves the
bytes of the objects in `live` (for `free`: of the others) unchanged, and
`Idle` cannot carry it, because the `frame` clause makes `Idle` independent
of exactly those bytes (`:80-82`).

Consequences:

- `InsertStep` cannot be proved for any path with an allocation after a node
  exists: the second allocation of the intermediate-node path may change the
  node the first returned, and any insertion may change every older node.
- `Headline` is false as stated, not just hard: a stub that meets every
  clause and also clears the peer word of earlier nodes yields a machine
  whose lookups differ from the mirror's, and every `Inv` must contain that
  state (section 2).

Trial T4's contract had the missing condition (`readApart`:
`… ¬aw a` for every read span of the existing names, `T4Boundary.lean`
`Entry`); it was lost in the rewrite. The tests cannot see this: the
supplied allocator is benign and the `ServiceWrites` clause is not checked.

Fix: exclude live objects from the services' write set (all of `live` for
`alloc`; all but the released object for `free`), or add the equivalent
conjunct. A proof would have found this on its first two-node path, after
signing.

### H2. The contract promises a return from states where no stack-using code can return, and `frame` prevents `Idle` from excluding them

The `alloc` and `free` clauses quantify over every state with the entry
`pc`, `EntryFrame`, `c.At`, the argument registers and `A.Idle`
(`Contracts.lean:83-96`). They do not require the stack below `rsp` to be
mapped, although they allow the service to write it (`Scratch`). In Kraken a
store to unmapped memory is a failure (`Execution.lean:12`,
`nonmem_store => False`). Take a memory satisfying `Idle` and unmap the
eight bytes below `rsp`: by `frame` it still satisfies `Idle` (those bytes
are outside the arena wherever the caller's conditions hold,
`Headline.lean:71`), the other hypotheses are untouched, and
`kmem_cache_alloc_noprof`'s first instruction is `push %rbp`.

So for the image's allocator, and for any stub that pushes anything, the
premise implies that `Idle m live (record :: stream)` is false for every
record of the three sites, and that `free` is never enabled. `Initial` then
applies only to worlds with no pending record, in which the mirror refuses
every allocation. The headline would be true and would say nothing about an
insertion that allocates.

The same holds for the direction flag (`rep stos` in the allocator's
prologue) and for a zero-capacity coverage area in recording mode
(section 3). `insertReady` does supply the mapped stack at the wrapper's
entry (`Headline.lean:61-62`, with `A.depth` added at `:93`), so the fix
costs the headline nothing: give the two clauses an explicit readiness
premise in the form of the landed `RandomReady` (mapped scratch of
`A.depth` bytes, direction flag clear, capacity positive when the buffer is
needed), and have `insertReady` supply the flag. The six WireGuard functions
contain no string instruction, so nothing else changes.

The packet says its form follows the landed random-provider contract. It
does not in this respect, nor in two others a signer should know of: the
precedent's private state is a concrete executable check where `Idle` is
abstract, and its coupling to the recorded input is a separate safety law
that does not assert termination, where here the two are merged.

### H3. The image's own allocator cannot meet the contract under the pinned semantics, in either mode; the claim should be worded accordingly

`instructionStep` is `False` where `fetch` gives nothing
(`Execution.lean:25-29`), and a `Decoded` holds a Kraken `Instr`. On every
successful fast path the image executes `popf` (in
`this_cpu_cmpxchg16b_emu`) and `prefetcht0` (`kmem_cache_alloc_noprof+0x91`);
a recorded allocation executes `rdtsc` twice. The pinned Kraken has no
`popf`, `prefetch*`, `cmpxchg16b` or `rdtsc` (section 1). No `fetch` that
agrees with the ELF at the allocator can satisfy the `alloc` clause where
`Idle` holds.

Separately, the bytes the CPU runs there are not the ELF's:
`.altinstructions` lists `kmem_cache_alloc_noprof+0x85` and
`kmem_cache_free+0xf4` (the call to the emulation, replaced by
`cmpxchg16b` on a CPU with CX16) and `+0x91` (the prefetch). The packet's
premise table says the absence of patching "in range" is assumed; for the
six WireGuard functions I checked it and it holds; for the two services it
does not.

Nothing in `Premises` requires `fetch` to hold the image's code at
`allocEntry` or `freeEntry`. That is the honest reading and the only
satisfiable one: the result would establish that the six compiled functions
behave as the mirror does *when linked against any service that meets the
contract*. Whether Linux's allocator is such a service is not a premise that
can be discharged, or even stated truthfully, in this semantic base; the
reading of section 3 is the evidence for it and will remain so. The packet's
"what a kernel reader would have to believe" invites the stronger reading
(a belief about `kmem_cache_zalloc`). It should state the weaker one, name
`allocEntry` and `freeEntry` as addresses rather than as the kernel's
functions, and list the unsupported instructions and the three patched
sites among the claim's limits.

### M1. Recording mode: three things to add to the contract or its description

From section 3.

1. The arena has to contain `kcov_choice_seq`, `kcov_alloc_records`,
   `kcov_alloc_unwinds`, `kcov_alloc_unwind_cycles`, the steering schedule
   and `t->kcov_leanux_dropped`. The packet names the depth counter, the
   schedule and the stack (which is read, not written). With these in, the
   condition between calls ("nothing else changes the arena") excludes any
   other recorded choice anywhere in the kernel, since each increments
   `kcov_choice_seq`, unless `Inv` ignores that word, which the hidden
   invariant does not let a reader know.
2. The `frame` clause is false of the hook: its unwinder reads the stack
   above the call and the ORC tables, and with a chain-flagged schedule entry
   the forced outcome depends on those return addresses. Either `frame`
   exempts a named read-only region that the caller's conditions keep fixed,
   or the claim excludes chain-flagged entries and says the unwinder is
   outside it.
3. Capacity at least one word when the buffer is needed (H2).

With those, beliefs 3 and 4 of the packet stand as read: the hook leaves the
callbacks' state valid, and the record a recorded run produces carries the
call's outcome.

### M2. The outcome's tie to the pending record is foreknowledge, and the `free` clause narrows what can carry it

In recording mode the record is written after the allocation by the post
hook. `Idle … (record :: stream)` before the call is therefore a statement
about the future in both modes; the packet's belief 3 says so for the
unrecorded mode only. One carrier exists: a loaded steering schedule whose
head entry is `fail`.

The `free` clause keeps `stream` unchanged across a release. For a slab,
releasing an object makes the next allocation succeed where it would have
failed for want of memory, so no predicate on memory can satisfy both
clauses for a natural failure while a node is handed out; the rollback path
is exactly that situation. The contract is consistent only for failures
that do not depend on the slab's state: forced ones, or a stub's. That is
an acceptable scope (natural failures of this allocation are not what the
oracle exercises), but it settles the question belief 3 leaves open, and
the packet should say it.

### M3. The hidden invariant makes the result closed-world

Sound as a claim (section 2), but:

- Between calls the user must keep the heap, arena included, byte-for-byte
  fixed, because the statement does not say which heap bytes `Inv` reads.
  With the relation explicit a later theorem could re-establish it after
  another operation; with it hidden, nothing can.
- A later result on removal or the dump cannot use this one. Two theorems
  each asserting some invariant do not share it. The packet's remark that a
  later result "would make those parts observable in the same way" means a
  new, larger headline with every operation as a clause of one existential,
  superseding this one and re-proving its clauses for the common invariant.
  That may be the right plan; it is a plan, and the owner should accept it
  knowingly.
- The sequence counter's increment is unclaimed. The variant "mirror is
  `add`, without the increment" is rejected in the tests only by `assertAt`;
  no return value distinguishes it. Under `Headline` the claim is relative
  to `insert` and to `add` alike.

### M4. The witness as proposed does not show what it should

`Satisfiable` (`Vacuity.lean:20-28`) asserts one enabled call from an empty
table. It does force `Idle` to hold with a pending record, which is the
point of it. But:

- as the contract stands (H2) only a service that never touches its stack
  can be the witness, and nothing asks it to write a record: the witness
  would be unlike the real service in the two respects the contract was
  rewritten to cover;
- one call does not exercise a second allocation with a node live (H1), the
  release, or the `frame` law;
- the two exclusions quantify over `Premises` and are as vacuous as it is;
  they are evidence about the conclusion, not about the premises.

Ask for: a stub that uses a stack frame, appends a record-shaped write to
the coverage buffer when the buffer is needed, keeps its answers in arena
memory, and is the fetched code at the two addresses; and a witness sequence
through one intermediate-node insertion (two allocations), one rollback
(a release) and one lookup. It remains a stub and should be called one.

### M5. The tests support the conclusion for one relation and one benign allocator; they do not test the contract

Reproduced exactly; no discrepancy. What they are:

- The conclusion is checked with `Inv` read as `Related`, on states built by
  the fixture. `insertReady`, `lookupReady` and `emptyTable` are the
  statement's own definitions; `Returned` and the write frame are renderings
  (the frame as a log of instruction writes against a 200-byte window,
  tighter than the statement's).
- `Idle` is `True`; the allocator is a Lean-level transition that uses no
  stack, writes no coverage and always conforms. `c.At` across a service,
  `ServiceWrites` and `frame` are unchecked. No test gives a non-zeroed,
  overlapping or out-of-arena object, or one that disturbs a live node.
- The record list is replaced before each call and required empty after it;
  the mirror world is not threaded from call to call as the statement
  threads it.
- All eight wrong variants change the expectation, none the machine or the
  service. Four are rejected for the stated reason; the missing increment is
  caught only through `Related`; "the other family" fails because the mirror
  asks for a record, not on a result; the two about sites and release fail
  on the test's own bookkeeping.
- The malformed entries are IPv4 only; none is tried against `lookupReady`
  (my additional run did: wrong root, width, family slot, key in the stack
  window, misaligned stack are refused).

The packet's own "not tested" list is candid about most of this. The
allocation-outcome variants a kernel capture with recording armed would add
(decision 10) are the cheapest real evidence for section 3 and I would do
that before proof.

### M6. Surface: the figures reproduce; the mirror's share is understated

`measure-surface.py` prints what the packet reports. Its groups are
hand-written name lists; a computed closure of `Headline` has 847 project
constants. On the package side the lists miss about 30 trivial ones. On the
mirror side the closure holds 229 constants of `Leanux.Kernel.Defs` (the
world, the ambient state, the record machinery, `hiddenAlloc`), 145 of
`WG.Types`, and `lookup` with `peerGetMaybeZero` and `refcountIncNotZero`.
Under the project's definition these are claimed surface: they are what
"the mirror's result" and "an accepted run" mean. "About 120 lines of `add`,
`insert` and helpers" describes the functions, not the definition of
acceptance, and acceptance is where the claim goes silent. The budget in
decision 7 should either count the mirror's closure or say in the result's
limits that it is uncounted.

### L1. Premises against the image and the source

- Caller conditions: consistent with the two calls in `set_allowedip`
  (`netlink.c:343-352`: a non-NULL peer, address bytes in the netlink
  message, the table of the peer's device). That caller checks the prefix
  length against the family's width before calling, so the over-long-prefix
  `-EINVAL` path of the claim is not reachable from it. The lock argument
  is ignored, as stated. Not derived from any entry, as stated.
- The empty-table condition is satisfiable in a running kernel
  (`wg_allowedips_init`).
- Callbacks: I did not re-examine the landed contracts; `cmp1` and `cmp8`
  unproved is as the packet says, and proving them (decision 6) is right.
- Decoder agreement: no patch site in the six functions (section 1).
- `c1.caller-separation` compares the address bytes with the window below
  `rsp` only, so a key overlapping the return word is accepted. Harmless
  (the callee does not write it), but looser than the comment.
- The mirror refuses on a record byte other than 0 or 1
  (`Leanux/Kernel/Defs.lean:2319-2324`), so `AllocResult`'s silence there is
  not a gap.

### L2. Cost and the source-side options

The estimate does not include repairing the contract (H1, H2, M1) or the
stronger witness (M4); both are small beside the "largest uncertainty" the
packet names (the ordering facts), which I could not assess. I have no
reason to move the 30-to-60-hour range; I would treat the lower half as
unlikely.

On where source-side facts live: the third option needs the standing rule
changed and the proof gate with it (the gate fails if anything outside the
proof tree imports it). For C1 alone, local re-proof is consistent with the
rules and I agree with the packet's recommendation; decide the rule for C2
on its own packet.

### L3. Slips

- `run-tests.sh` takes about 70 s, not ten, and its header does not say the
  generator needs the host Python.
- `Contracts.lean:33`: the release is at line 237 by the image's DWARF.
- The address in T4's notes is a transcription error there; the packet's
  third "discovery" item can be closed.

## 5. Verified, inferred, not checked

Verified by running or by reading the code named: section 1's table; the
disassembly facts of section 3; the absence of `popf`, `prefetch`,
`cmpxchg16b`, `rdtsc` from the pinned Kraken's syntax; the alternatives
entries; the definitions quoted in H1 and H2.

Inferred, by argument from the definitions and not machine-checked: the
equivalence of `Headline` with the trace statement (section 2); that
`Headline` is false for a suitable stub (H1; I did not construct the stub);
that the premise forces `Idle` false for stack-using services (H2); the
`free`-clause argument of M2.

Not checked: the slow paths (`___slab_alloc`, `__slab_free`, the page
allocator) beyond their entry; the ORC unwinder's own reads; which CPU
features the oracle's guest exposes, hence which alternative text runs;
whether the oracle's traces ever load a chain-flagged entry for these sites;
the landed callback contracts and the lookup theorem; the cost basis; the
trials. No guest was booted.

## 6. Reproduction

```sh
# from the review worktree, build outputs copied from .worktrees/binary-reassessment
capped -- scripts/in-bundle lake -d binary build
capped -- scripts/in-bundle /usr/bin/python3 -B binary/allowedips_mutation.py
binary/Statements/C1/run-tests.sh
V=<main checkout>/.artifacts/kernel-net-choice-s5/vmlinux
objdump -d --no-show-raw-insn --start-address=0xffffffff81196d20 --stop-address=0xffffffff81196f30 $V  # the allocator
objdump -d --no-show-raw-insn --start-address=0xffffffff81199b10 --stop-address=0xffffffff81199e30 $V  # free
objdump -d --no-show-raw-insn --start-address=0xffffffff815fc4d0 --stop-address=0xffffffff815fc4f7 $V  # the cmpxchg16b emulation
objdump -d --no-show-raw-insn --start-address=0xffffffff810f3b00 --stop-address=0xffffffff810f3fb0 $V  # the hooks
objdump -d --no-show-raw-insn --start-address=0xffffffff810f2930 --stop-address=0xffffffff810f29d0 $V  # the chain unwinder (rdtsc)
readelf -S -W $V | grep altinstructions   # 14-byte entries: s32 site offset, s32 replacement offset, u32 feature, u8, u8
grep -n "pushf\|popf\|prefetch\|cmpxchg\|rdtsc" .deps/kraken/Kraken/X64/Syntax.lean
```

## To the signer

**Sign with these named changes; not as it stands.**

The headline (`Headline`, the internal-invariant form) says what it appears
to say and is the right one of the two to sign. The allocator and free
contract, on which all of its content rests, has to change first:

1. **Live nodes are outside the services' write set** (H1). Without this
   the statement cannot be proved and is false for a conforming service.
2. **A readiness premise on both clauses**, in the landed provider's form:
   mapped stack scratch, direction flag clear, positive capacity when the
   buffer is needed (H2). Without it the statement is true but empty for any
   service that uses its stack.
3. **The recording-mode description completed** (M1, M2): the words the
   hook writes besides the buffer, the unwinder's reads and chain-flagged
   entries either exempted or excluded, and the statement that a failure's
   only carrier is the steering schedule.
4. **The claim worded as about any service meeting the contract**, with the
   image's allocator named as unable to meet it under this semantics and
   the reasons listed (H3); and **a witness that uses its stack, writes the
   buffer, and runs through two allocations, a release and a lookup** (M4).

Three things to accept knowingly, none of which blocks: the result is
closed-world and will be replaced, not extended, by a later one (M3); the
sequence counter, parent pointers and peer lists are unclaimed; the mirror's
definition of an accepted run is part of the claim and is not in the
counted surface (M6).

Why not as is: items 1 and 2 are defects in the statement itself, cheap to
fix now and expensive to discover after signature, since the track's
standing rule is that preconditions and relations are not narrowed to fit a
proof.
The revised contract is short enough to re-read in one sitting; I would
want to see it, and the recording-armed kernel capture of decision 10,
before proof work starts.

## Follow-up on revision 2 (2026-11-10)

Reviewed: revision 2 of the packet at `eb67564b` on
`task/binary-c1-statement` (one commit on the `954f8c1d` reviewed above):
the revised `Contracts.lean`, `Headline.lean`, `Vacuity.lean`, the rewritten
`Test.lean`, the new `Closure.lean`, and the packet document with its table
of dispositions. I read the Lean first and the table second. The run was
made in a temporary detached worktree at `eb67564b`
(`.worktrees/review-c1-r2-run`, removed afterwards) with the same copied
build outputs. The sections above are unchanged; this section supersedes
their advice to the signer. Judgements are mine [AGENT].

### Verdict on revision 2

**`Signed` can be signed.** Both defects of the statement are repaired in
the Lean, the repair introduced nothing I could find that makes a premise
too strong or a conclusion weaker, and the contract as it now stands is, by
my reading, both satisfiable by a service that uses its stack and writes
the buffer and sufficient to prove the headline from. Two small additions
(F1, F2) would make what is signed say what the prose around it says; one
piece of evidence I asked for is still outstanding (F3). None of the three
is a reason to withhold signature; F1 is a one-line change I would make
first.

### Dispositions, checked against the Lean

| Finding | Resolved? | What I checked |
| --- | --- | --- |
| H1 | **Yes** | `ServiceWrites` takes a `kept` list and its arena disjunct is `L.Arena a ∧ ¬Kept kept a` (`Contracts.lean`, `Kept`, `ServiceWrites`); `alloc` passes `live`, `free` passes `live.erase` of the released object; `frame` is stated with the same `Kept`. A node handed out is now unchanged by every later service call until it is released. The new object is disjoint from `live` by `AllocResult`, so `live` has no duplicates and `erase` removes the right thing |
| H2 | **Yes** | `ServiceReady` (coverage state, positive capacity when the buffer is needed, direction flag clear, `A.depth` mapped bytes at exactly the `Scratch` range) is a hypothesis of both clauses. `frameReady` now checks the stack byte by byte over the window plus `A.depth` and, for insertion only, the capacity and the flag. I checked that the three non-memory conditions can be re-established at each service call inside `add`, which a proof needs: capacity is a property of `c`; the direction flag and mappedness are invariants of every execution under this semantics, proved from the interpreter in the landed package (`SystemInvariant.eventually_mode`, `MemoryInvariant.eventually_mapped`), so no callback or service contract has to preserve them; `c.At` follows from each callback contract's stated effect, as in the landed proofs, and is concluded by both service clauses |
| H3 | **Yes** | The doc comments of `allocEntry`, `freeEntry`, `Premises` and `AllocatorContract` now say the premise is about whatever code `fetch` holds at two addresses; section 2's table and the first bullet of section 3 state the limits; decision 11 puts the consequence to the owner |
| M1 | Capacity fixed; the rest described, by the author's choice | I accept the reasoning: once the contract is not a description of the hook, an exemption in `frame` shaped to the unwinder would be surface with no job. The six words and the unwinder are in section 2's table as limits |
| M2 | Stated | Section 2's table carries it as I put it |
| M3 | Closed-world stated; the increment now claimed | `SeqAdvanced` is a conjunct of `InsertStep`'s conclusion (below) |
| M4 | **Yes, as a statement**, with F1 | `Witness` (below) |
| M5 | **Yes**, within what execution can show | "The search" below |
| M6 | Yes | `Closure.lean` computes the closure by declaring module; the packet's budget says Kraken and the mirror's closure are uncounted |
| L1-L3 | Yes | `Contracts.lean` says `:237`; the script header names the host Python and the run time; the T4 item is closed |

### Is the contract now satisfiable, and can the headline be proved from it?

Both by argument from the definitions; neither is machine-checked, and the
packet says a stub in instruction terms has not been written.

*Satisfiable by a stack-using, buffer-writing service.* What such a service
reads is now pinned by its hypotheses: its scratch is mapped
(`stackMapped`); the return word by `EntryFrame`; the coverage metadata and
the count word by `c.At`; its own state by `Idle`, which may constrain
arena bytes outside kept nodes. Whether the buffer is in use
(`c.Needed`) is determined by memory through the same gated reads the
callbacks make, so a stub can decide it; with `capacity` positive it can
keep the count within bounds. Nothing in the clauses now quantifies over a
state such a service cannot return from. The test's service is a
Lean-level transition of exactly this kind and passes every rendered clause
on every transition of the run reported below.

*Sufficient for the headline.* Walking a two-allocation insertion and the
rollback against the clauses: after a service call the table and peer words,
the caller's frames above the service's entry, the address bytes, the
`node_cache` word and the coverage metadata are outside `ServiceWrites` (by
the separations of `insertReady`), and so now are the bytes of every node
that stays handed out; the new node is zeroed, in the arena and disjoint
from the others; `Idle` survives the insertion's own stores because they
fall in kept nodes or outside the arena, which `frame` allows; the released
node leaves `live` and the invariant together. I found no step that needs a
fact the contract withholds. The trie-ordering facts remain the open part
of the proof, as the packet says; they are not a contract matter.

### Did the repair introduce anything?

- **No premise made too strong.** The capacity and direction conditions
  are on insertion only (`frameReady`'s `if cache`); `lookupReady` passes
  `cache := false` and is as in revision 1 apart from the byte-wise stack
  check, which for a 144-byte window is the same condition. The narrowing of
  `lookupReady` that the author reports catching is not in the committed
  file. Positive capacity when the buffer is in use and a clear direction
  flag hold at any real call. Using the `cache` flag to mean "this is an
  insertion" is a small wart in an executable definition a signer reads.
- **No conclusion weakened.** `InsertStep` differs from revision 1 only by
  the added conjunct; `LookupStep`, `Initial`, `Framed`, the write sets and
  both exclusions are textually unchanged.
- **`SeqAdvanced`** says the 8-byte word at the table's sequence offset
  after the call is the word before plus one modulo 2^64. It is a
  machine-level observation, costs seven printed lines, is true on every
  path including the early `-EINVAL` (the wrappers increment before calling
  `add`), and removes the reservation at the end of section 2 above: the
  claim now distinguishes `insert` from `add`.
- **`ServiceReady.coverage` replaces the bare `c.At` hypothesis**: same
  content.
- The refusal the packet lists for a zero-capacity area is reported under
  `c1.coverage`, not the new `c1.coverage-capacity`; the new check is
  therefore not itself exercised by a refusal. Cosmetic.

### The search: what it tests

It is the right kind of test and a large improvement; its limits are the
ones execution has.

- **The statement's own definitions**: `emptyTable`, `insertReady`,
  `lookupReady`, `armed`, the literals, the windows, `Layout`,
  `nodeSize`. The record list and the mirror world are now built once and
  threaded.
- **Renderings, necessarily**: every clause of `AllocatorContract`
  (`contractStep`), `Returned`, the write frames (as a log of instruction
  writes plus the service's own log of its stores), `SeqAdvanced`, and
  `Idle` (a concrete model reading a block of arena memory). I read
  `contractStep` against `Contracts.lean` clause by clause: the hypotheses,
  the kept-node exclusion, the result clauses and `Idle` before and after
  correspond. The `Allocator` value handed to the statement's definitions
  still has `Idle := True`; only its `depth` is used there, so this is
  harmless.
- **What the service is**: a Lean function on machine states, not fetched
  code. The `Eventually (instructionStep fetch)` of the two clauses, and
  the witness, are not exercised. The packet says so.
- **What the rows show**: that across 23 families the compiled code's
  results do not depend on the service's scratch, the caller-saved
  registers it returns, free arena bytes, object spacing, address range,
  coverage mode or fill, preempt count, or stack alignment. The H1 and H2
  probes do what I could only argue: the revision 1 contract admits a
  service under which a compiled lookup returns NULL where the mirror
  returns a peer, and admits a state from which a stack-using service does
  not return; the revised contract refuses both.
- **What I would still want covered before signature**: nothing that
  blocks. Before *proof*: (a) the kernel capture with allocation recording
  armed (F3); (b) an arena of more than one span and more than two peers,
  since `Layout` allows both and every run has one and two; (c) a caller
  that changes non-heap memory between calls beyond registers and the
  return word, which is all `Framed` is exercised by.

**Run.** `binary/Statements/C1/run-tests.sh` at `eb67564b`, after the build
replay (1,119 jobs, nothing recompiled) and the generator under the host
Python: `PASS`, exit 0, about 21 minutes. All 23 families print `holds`
with the packet's counts (108 insertions and 486 lookups for the baseline,
36 and 168 for each other family, 110 lookups where the mirror refuses on
saturating reference counts; deepest stack write 200; 23 distinct mirror
decisions in each). The five refusals, the H1 service under both contracts
(revision 1: every premise met and a lookup returns 0 where the mirror's
peer is at 6295552; revision 2: refused at `contract.writes`) and the H2
state under both (`store to unmapped stack`; `contract.ready.stack-mapped`)
print as the packet reports. The frame probe changes a byte outside the
arena, the answer index and the stream; it does not change a byte inside a
kept node, the other half of `frame`.

### `Signed`, and the witness

`Signed := Headline ∧ Witness ∧ InsertThenLookup ∧ FailedInsertInvisible`
is what I would advise the owner to sign. Putting the witness inside what is
signed is right: without it the headline is satisfied by a service that is
never idle (section 2 above), and with it that reading is excluded by a
theorem rather than by prose. The exclusions add source-side obligations and
are worth it as the two instances a reader can check by eye.

`Witness` asks for an actual execution from an empty table with five named
answers pending through an insertion into the empty table, an insertion that
allocates twice, an insertion whose second allocation is refused, and a
lookup that finds a peer; each call meeting its caller conditions with the
mirror accepting and consuming exactly those records; `0 < A.depth`; the
buffer in use in the second call; and, inside that call, an entry to
`allocEntry` and a return from it between which a scratch byte and a buffer
byte differ. That is what I asked for. The release is not named but is
forced: the decoded code of `add` calls `freeEntry` when the second
allocation returns NULL, and the execution is required to return.

**F1 (low). The witness does not say which code is at the callbacks.**
`Witness` requires `Premises`, which constrains the code at the five
callback addresses and BH-enable only through their contracts. The packet's
prose says the intended witness has the image's own callbacks and a stub at
the two service addresses only; the Lean lets every service be a stub. As
signed, a witness with stub callbacks would satisfy it. Either add a
conjunct (agreement of `fetch` with the image's decoded code at the
callback addresses), or have the
result's summary say the witness's callbacks may be stubs. The first is
cheap if `cmp1` and `cmp8` are proved from the image as decision 7
recommends, and is what "named as a stub" should mean.

**F2 (low). The summary sentence should say what is established about the
allocator's use, not only what is not.** See decision 11 below.

**F3 (carried over). The recording-armed kernel capture has not been run.**
It is the only evidence that would connect the contract's conclusion clauses
to the image's allocator, and after H3 it is all there will be. It does not
bear on whether `Signed` says what it appears to say; I would still want it
seen before proof work is commissioned, because a surprise there changes
what decision 11 is deciding.

### On decision 11

The author asks whether a result whose service is specified by assumption
on every interesting path is worth having. My view: yes, on two conditions,
and with a more exact account of what it is.

It is not a result about allocation, and the packet now says so without
hedging. But "correct given an allocator specified by assumption"
undersells one thing and oversells another.

- What it does establish about the allocator's *use*, which is where
  insertion code goes wrong: the compiled code calls the service only with
  the cache and flags the contract names; relies on nothing about the
  returned object but that it is zeroed, aligned and disjoint; never depends
  on its scratch, on caller-saved registers, or on bytes of a released
  object; and releases exactly the node it allocated, once, on the one
  failing path. Each of these is forced by the contract's shape: a call
  outside the clause's hypotheses gives the proof nothing to continue with.
  That is a real property of 561 instructions of compiled code, and the
  summary should state it in those terms.
- What it leaves a reader likely to over-read: "given an allocator" suggests
  the kernel's. The sentence should say "given any code at the two service
  addresses that meets the stated contract; the image's allocator is not
  shown to, and in this semantic base cannot be".

The conditions: that sentence, in that form, in the result's summary and
register entry; and the capture of F3 looked at first. The cost is the
owner's to weigh; nothing in this review bears on the estimate beyond L2
above.

### What I did and did not verify in this follow-up

Verified by reading: the four revised or new Lean files in full where they
changed (`git diff 954f8c1d eb67564b`), `contractStep`, `service`, `idle`,
`insertCall`, `runConfig` and the configuration list of `Test.lean`;
`Closure.lean`; the statements of `SystemInvariant.eventually_mode` and
`MemoryInvariant.eventually_mapped`; sections 2, 3, 5 and 7 and the
dispositions of the packet. Verified by running: see the run result above.
Argued and not machine-checked: satisfiability by a stack-using service and
sufficiency for the headline. Not checked: `measure-surface.py`'s revised
figures and the closure counts (970 and 372 by the author's method); the
bridge from the callbacks' history-step contracts to the two invariants,
which the landed insertion already uses; sections 4 and 6 of the packet
beyond a reading.

### To the signer (revision 2)

**Sign `Signed`.** The contract defects that made revision 1 unprovable or
empty are fixed in the Lean; the headline is the same sound, closed-world
claim with the sequence increment restored; the witness now excludes the
degenerate reading by theorem.

Make one change first if it is cheap, or accept it knowingly: the witness
does not pin the callbacks to the image's code (F1).

Decide 11 with the sentence above in the summary, and have the
recording-armed capture run and looked at before proof work starts (F3).
Still to accept knowingly, unchanged from the first review: the result is
closed-world and will be replaced, not extended; parent pointers and peer
lists are unclaimed; the mirror's definition of an accepted run is part of
the claim and uncounted; nothing is claimed about Linux's allocator.
