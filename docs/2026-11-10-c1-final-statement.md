# C1: the final statement, revision 4

2026-11-10, branch `task/binary-c1`. The signed statement of result C1 (the
compiled allowed-IPs insertion) revised in the five places decided in
`docs/decisions.md` (2026-11-10; revision 3) and, after the independent
review of revision 3 and a finding of the trunk's proof, in two more
(the last entry there; revision 4: changes A and B below), for the reviewer
and then the owner. **Nothing is proved here** about the image:
the statement files contain `def … : Prop` and executable definitions only.
Revision 2 of this document (the capture's result and the text then signed)
is commit `7d39d508`; its capture section is appendix C, unchanged except
where marked. Every judgement below is mine [AGENT]; the decisions to make
the seven changes are the owner's [USER].

What I ask the reader to look at hardest: the form I gave change 2
(`Referenced`, section 1), what the restated witness no longer shows
(change 5), the placement of change B, and the four things in [section 7](#7-what-i-could-not-do-as-decided-and-what-i-flag).

## 1. The changes: five in revision 3, two in revision 4

**Change 1: the returned object ends below 2^64.** One conjunct in
`AllocResult`'s success clause, in the form the landed `Trie.validate` uses:

```lean
  (record.bytes.head? = some 1 →
    a ≠ 0 ∧ a % 8 = 0 ∧ a + nodeSize < 2^64 ∧
    (∃ span ∈ L.arena, span.1 ≤ a ∧ a+nodeSize ≤ span.1+span.2) ∧ …
```

The assembly's open hypothesis `NodeBelowTop` is now the one-line theorem
`C1Assembly.nodeBelowTop` and is gone from `signed_of_parts`.
`Statements/C1/proof/TopOfMemory.lean` is a regression test: it fails to
elaborate unless the object at `2^64 - 72` is admitted by revision 2's
clause, excluded by revision 3's, and refused by the landed check.

**Change 2: the closed world admits the caller's reference on a peer.** A
fifth clause in `Headline`, beside `Framed`:

```lean
def CountMoved (L : Layout) (pid : PeerId) (before after : Nat) (m m' : Mem 64) : Prop :=
  ∃ peer, Trie.address L.peers (some pid) = .ok peer ∧
    readNat ⟨{dmem := m},0⟩ (peer+Root.nodeOffsets.peerRefcount) 4 = .ok before ∧
    readNat ⟨{dmem := m'},0⟩ (peer+Root.nodeOffsets.peerRefcount) 4 = .ok after ∧
    ∀ a, L.Heap a → ¬InRange (.ofNat 64 (peer+Root.nodeOffsets.peerRefcount)) 4 a → m.get? a = m'.get? a

def Referenced (L : Layout) (Inv : World → Mem 64 → Prop) : Prop :=
  ∀ (w w' : World) (m m' : Mem 64) (pid : PeerId) (count : Nat), Inv w m →
    ((liftWG (WG.peerGetMaybeZero (some pid))).run w = .ok (some pid, w') ∧
      CountMoved L pid count (count+1) m m') ∨
    ((liftWG (WG.peerPut (some pid))).run w = .ok ((), w') ∧ 1 < count ∧
      CountMoved L pid count (count-1) m m') →
    Inv w' m'
```

(The take is shown as revision 4 has it: change A below.) Exactly what may change: the four bytes of one registered peer's reference
count, by one, with every other heap byte the same (bytes outside the heap
are free, as in `Framed`); paired with exactly one mirror operation, an
accepted `peerGetMaybeZero` on that peer that returns the peer for `+1`,
an accepted `peerPut` for `-1`. These are the operations the kernel
performs: for a peer that already exists `set_peer` takes its reference
through `wg_pubkey_hashtable_lookup`, which is `wg_peer_get_maybe_zero`
(`netlink.c:386`, `peerlookup.c:68`), and drops it with `wg_peer_put`
(`netlink.c:486`); `wg_peer_get` is called only on a peer just created
(`netlink.c:421`), which the clause excludes.
A drop must start above one: dropping the last reference releases the peer
in the mirror, which changes the peer set, and stays outside. A move of a
reference between two peers is two steps. I chose single steps over one
"move" clause because that is how `set_peer` does it (it drops its
reference on one peer and later takes one on the next) and because each
step is then one mirror operation.

On the capture: the grid's one change of peer is `peerPut 0: 2 -> 1`, then
`peerGetMaybeZero 1: 1 -> 2`, no other heap byte changed (captured states and whole
RAM). **The headline now covers 13 of the grid's 13 calls (5 before) and
still 2 of `b1_trie_routing`'s 8**: in `b1` each later peer is *created*
between the insertions (its count goes 0 to 2, and the layout's peers are
fixed at the empty table), which this clause does not and should not admit.
So a `wg set` or `wg setconf` that creates its peers and gives them allowed
addresses in one message, which is how an interface is usually configured,
is covered for its first peer only.

**Change 3: the ten-instruction listing stays.** `CallbacksFromImage` and
`StatementC1CallbackImage.lean` are textually unchanged; the counts in
section 4 include the listing (75 printed lines).

**Change 4: `ServiceReady` carries the separation.** In the statement file,
field for field the service prover's `Separated`:

```lean
structure Separated (L : Layout) (A : Allocator) (c : CommonBitsCoverage.Context) (s : MachineState) : Prop where
  stackArena : ∀ a, Scratch s A.depth a ∨ InRange s.data.regs.rsp.toBitVec 8 a → ¬L.Arena a
  stackCoverage : ∀ a, Scratch s A.depth a ∨ InRange s.data.regs.rsp.toBitVec 8 a → ¬c.bytes a
  coverageArena : ∀ a, c.bytes a → ¬L.Arena a
  bufferMetadata : ∀ a, c.writes a → ¬c.metadataBytes a ∧ ¬InRange preemptCountAddress 4 a
```

and `ServiceReady` gains the field `separated : Separated L A c s`, hence the
layout as a parameter (`ServiceReady L A c s` in the two clauses of the
contract). Checked three ways:

- *Derivable inside an insertion.* The prover's own theorem `separated`
  (from `insertReady` and `InFlight`), moved in front of its `serviceReady`
  with one field added, compiles against this text, and its `allocRule` and
  `freeRule` are then proved unchanged (scratch copy, standard axioms).
- *Does not exclude the image's allocator as captured.* The four conjuncts
  hold at all 23 captured service entries evaluated in Lean, under both
  seeds, with the arena drawn around every byte the allocator changed, its
  stack 736 to 968 bytes deep and the whole 32 MiB buffer: stack apart from
  arena, stack apart from the coverage bytes, coverage bytes apart from the
  arena, buffer apart from the metadata and the preemption count.
- *`word_kept` and `no_state_word` no longer go through.* Compiled against
  this text (scratch copy), `word_kept` fails at exactly its step
  `readyMoved`, which must now supply the separation for the aliased
  context. `Statements/C1/proof/StateWord.lean` proves from the statement
  files that it cannot when the word is the allocator's (`mode_apart`: an
  admitted context's mode word is not in the arena or the service's stack),
  and that a conforming service cannot touch an admitted context's metadata
  at all (`metadata_kept`). Executably: the packet's test service advances
  an index word at `arena+16`; at the aliased state revision 2 admits the
  state and the service then breaks `c.At` (it did not conform), revision 3
  refuses the state; at ordinary states it meets every clause.

**Change 5: the witness in two halves.**

```lean
def Witness : Prop :=
  ∃ (fetch : Int64 → Option Decoded) (L : Layout) (A : Allocator),
    Premises fetch L A ∧ CallbacksFromImage fetch ∧ Executed fetch L A ∧ ServiceActive fetch L A
```

`Executed` is revision 2's four calls with its last clause removed: an
actual run from a physically empty table through an insertion, a
two-allocation insertion with the coverage buffer in use, a rollback with
its release, and a lookup that finds a peer, stated through the entry and
final states of the calls. `ServiceActive` is about the code at
`allocEntry` on its own:

```lean
def ServiceActive (fetch : Int64 → Option Decoded) (L : Layout) (A : Allocator) : Prop :=
  0 < A.depth ∧
  ∃ (c : Context) (s t : MachineState) (ra : UInt64) (live : List Nat) (record : HiddenRecord)
    (stream : List HiddenRecord) (history : List MachineState),
    s.pc = allocEntry ∧ EntryFrame s ra ∧ ServiceReady L A c s ∧
    s.data.regs.rdi.toNat = L.cache ∧ s.data.regs.get (.low .rsi .W32) = 0xdc0#32 ∧
    (ra.toNat, record.site) ∈ allocSites ∧ A.Idle s.data.dmem live (record :: stream) ∧
    c.Needed ∧ record.bytes.head? = some 1 ∧
    Ran fetch s t ra history ∧
    (∃ a, Scratch s A.depth a ∧ s.data.dmem.get? a ≠ t.data.dmem.get? a) ∧
    (∃ a, c.writes a ∧ s.data.dmem.get? a ≠ t.data.dmem.get? a)
```

Why this shape. Revision 2 asked for a scratch byte and a buffer byte
changed between a service entry and its return *inside* the second
insertion's history. The headline's steps conclude `Eventually` to a final
state and expose nothing in between, and no fact about final states can
show that a byte *did* change (the steps say only what did not), so the
clause was not derivable from the headline. The service's activity is
therefore stated where it can be established: by executing the service's
own instructions from one entry state that the contract's `alloc` clause
admits (all seven of its hypotheses, plus the buffer in use and a success
pending). Both halves are about the same `fetch`, layout and allocator.

| Conjunct | Vacuous reading it rules out |
| --- | --- |
| `Premises fetch L A` | Premises nothing meets |
| `CallbacksFromImage fetch` | Coverage and BH-enable callbacks that are stubs |
| `Executed`: `emptyTable …` and `A.Idle s1.data.dmem [] (five answers ++ stream)` | A never-idle allocator; an `Initial` that never applies |
| `Executed`: each call's `…Ready = .ok ()`, the mirror's accepted run, `Ran` | Caller conditions no state meets; a mirror that refuses; calls that cannot return, for each kind of call (first insertion, two allocations, rollback and release, lookup hit) |
| `Executed`: `c2.Needed` | A run with the coverage buffer unused |
| `ServiceActive`: `0 < A.depth`, the scratch byte | A contract only a service without stack could meet |
| `ServiceActive`: `c.Needed`, the buffer byte | A contract only a service that writes no record could meet |
| `ServiceActive`: `A.Idle s.data.dmem live (record :: stream)`, `Ran` | `Idle` false of every memory; an `alloc` clause that never applies |

**What it no longer rules out, against revision 2: a service that is active
only at entry states no insertion reaches.** Revision 2 placed the two
changed bytes in the second insertion; here they are shown at one admissible
entry state that need not be one of `Executed`'s. A stub could, in
principle, write only when called from a state the six functions never
produce. I could not close this within the headline's shape; the reviewer
may see a way.

A stub in instruction terms can satisfy `ServiceActive` under the revised
contract, where the prover's could write neither byte under revision 2:
`metadata_kept` (above) is the reason, the test service is an executable
instance (`ServiceActive` evaluated on it holds; on the quiet service it
fails), and one concrete design is a stub that calls the image's own
`__sanitizer_cov_trace_pc`, whose landed contract already gives the write
frame and `c.At`. **That a stub does satisfy it is not proved here**; it is
package 4's work.

**Change A (revision 4): the take is `peerGetMaybeZero`.** The reviewer's
finding R1. Revision 3 paired a taken reference with the mirror's `peerGet`,
a stand-in with the same count effect for the operation `set_peer` actually
performs on an existing peer. The hunk:

```diff
-    ((liftWG (WG.peerGet pid)).run w = .ok ((), w') ∧ CountMoved L pid count (count+1) m m') ∨
+    ((liftWG (WG.peerGetMaybeZero (some pid))).run w = .ok (some pid, w') ∧
+      CountMoved L pid count (count+1) m m') ∨
```

On every count the clause admits the two agree: at a count of zero
`peerGetMaybeZero` returns no peer (the step is not admitted) where
`peerGet` is refused by the mirror; both refuse saturation. `peerGet` and
`refcountInc` leave the claim's closure (section 4); `peerGetMaybeZero` was
already in it, through the mirror's lookup. The drop is unchanged.

**Change B (revision 4): the stack window is apart from whole peers.** The
trunk's finding (`task/binary-c1-wp2`, `C1TrunkCut`): the landed
`NodeInit.boundary` needs three bytes of `add`'s stack apart from every peer
as a whole 1520-byte object, and the signed heap separation kept the window
apart from a peer's reference count (offset 1056) and list head (1096)
only. The hunk, in `insertReady` before its call of `frameReady`:

```diff
   require ((← readNat s cacheWord 8) == L.cache) "c1.node-cache"
+  require (spansApart [((s.data.regs.rsp.toBitVec - .ofNat 64 (insertWindow + A.depth)).toNat, insertWindow + A.depth)]
+    (L.peers.map fun (_,a) => (a,Layouts.peerSize))) "c1.stack-peers"
   frameReady L c s ra (insertWindow + A.depth) (s.data.regs.rsi.toNat, width/8) true false
```

The window is the one the existing clauses use, `[rsp − (insertWindow +
A.depth), rsp)`, without the return word; the peers are the layout's, each
`Layouts.peerSize` bytes. I put it in `insertReady` and not in `frameReady`
so that the lookup's caller conditions keep their text.
`C1Trunk.StackOffPeers`, the trunk's hypothesis, follows in one step: take
the clause out of `insertReady = .ok ()` and apply `spansApart_sound` to
the window's span and the peer's span (the window's `InRange` is the span's
`contains` after `BitVec.ofNat_toNat`).
`Statements/C1/proof/StackOffPeers.lean` proves exactly that, with the
trunk's statement copied verbatim, and carries the trunk's layout as two
`#guard`s (the heap separation holds of it; the new clause refuses it).
The clause holds at all 20 captured wrapper entries under both seeds, every
test state of the packet still satisfies `insertReady`, and a stack window
inside a peer object below its count and list head, of which every
separation of `frameReady` holds, is refused at `c1.stack-peers`.

The interface proposition `PremisesMet` was weaker than its description (an
allocator with `Idle := False` closed it). It now also asks that the
allocator be idle in some memory, and its description says only what it
states.

## 2. The signed text, in reading order

`binary/StatementC1Contracts.lean` (135 source lines, 116 in revision 2),
`binary/StatementC1Headline.lean` (291, 252),
`binary/StatementC1CallbackImage.lean` (21, generated, unchanged) and
`binary/StatementC1Vacuity.lean` (198, 155). Doc comments are left out
below; the files carry them. `InsertStep`, `LookupStep`, `Initial`,
`frameReady`, `lookupReady`, `emptyTable` and the two exclusions are
textually unchanged from revision 2; `insertReady` gained one clause
(change B, appendix A).

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
      Initial L A Inv ∧ Framed L Inv ∧ Referenced L Inv ∧
      InsertStep fetch L A Inv ∧ LookupStep fetch L Inv

def Initial (L : Layout) (A : Allocator) (Inv : World → Mem 64 → Prop) : Prop :=
  ∀ w d m stream, w.wg.dev = some d → armed w = true → w.ambient.hidden = some stream →
    (∀ record ∈ stream, record.site ∈ allocSites.map (·.2)) →
    emptyTable L m d = .ok () → A.Idle m [] stream → Inv w m

def Framed (L : Layout) (Inv : World → Mem 64 → Prop) : Prop :=
  ∀ w m m', Inv w m → (∀ a, L.Heap a → m.get? a = m'.get? a) → Inv w m'

def CountMoved (L : Layout) (pid : PeerId) (before after : Nat) (m m' : Mem 64) : Prop :=
  ∃ peer, Trie.address L.peers (some pid) = .ok peer ∧
    readNat ⟨{dmem := m},0⟩ (peer+Root.nodeOffsets.peerRefcount) 4 = .ok before ∧
    readNat ⟨{dmem := m'},0⟩ (peer+Root.nodeOffsets.peerRefcount) 4 = .ok after ∧
    ∀ a, L.Heap a → ¬InRange (.ofNat 64 (peer+Root.nodeOffsets.peerRefcount)) 4 a → m.get? a = m'.get? a

def Referenced (L : Layout) (Inv : World → Mem 64 → Prop) : Prop :=
  ∀ (w w' : World) (m m' : Mem 64) (pid : PeerId) (count : Nat), Inv w m →
    ((liftWG (WG.peerGetMaybeZero (some pid))).run w = .ok (some pid, w') ∧
      CountMoved L pid count (count+1) m m') ∨
    ((liftWG (WG.peerPut (some pid))).run w = .ok ((), w') ∧ 1 < count ∧
      CountMoved L pid count (count-1) m m') →
    Inv w' m'

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

structure Separated (L : Layout) (A : Allocator) (c : CommonBitsCoverage.Context) (s : MachineState) : Prop where
  stackArena : ∀ a, Scratch s A.depth a ∨ InRange s.data.regs.rsp.toBitVec 8 a → ¬L.Arena a
  stackCoverage : ∀ a, Scratch s A.depth a ∨ InRange s.data.regs.rsp.toBitVec 8 a → ¬c.bytes a
  coverageArena : ∀ a, c.bytes a → ¬L.Arena a
  bufferMetadata : ∀ a, c.writes a → ¬c.metadataBytes a ∧ ¬InRange preemptCountAddress 4 a

structure ServiceReady (L : Layout) (A : Allocator) (c : CommonBitsCoverage.Context) (s : MachineState) : Prop where
  coverage : c.At s.data.dmem
  capacity : c.Needed → 0 < c.coverage.capacity.toNat
  forward : s.data.system.bits[10] = false
  stackMapped : ∀ i < A.depth,
    (s.data.dmem.get? (s.data.regs.rsp.toBitVec - .ofNat 64 A.depth + .ofNat 64 i)).isSome = true
  separated : Separated L A c s

def AllocResult (L : Layout) (A : Allocator) (live : List Nat) (record : HiddenRecord)
    (stream : List HiddenRecord) (t : MachineState) : Prop :=
  let a := t.data.regs.rax.toNat
  (record.bytes.head? = some 0 → a = 0 ∧ A.Idle t.data.dmem live stream) ∧
  (record.bytes.head? = some 1 →
    a ≠ 0 ∧ a % 8 = 0 ∧ a + nodeSize < 2^64 ∧
    (∃ span ∈ L.arena, span.1 ≤ a ∧ a+nodeSize ≤ span.1+span.2) ∧
    (∀ other ∈ live, disjointRanges a nodeSize other nodeSize = true) ∧
    readNat t a nodeSize = .ok 0 ∧ A.Idle t.data.dmem (live ++ [a]) stream)

structure AllocatorContract (fetch : Int64 → Option Decoded) (L : Layout) (A : Allocator) : Prop where
  frame : ∀ m m' live stream, A.Idle m live stream →
    (∀ a, L.Arena a → ¬Kept live a → m.get? a = m'.get? a) → A.Idle m' live stream
  alloc : ∀ (c : CommonBitsCoverage.Context) (s : MachineState) (ra : UInt64) live record stream,
    s.pc = allocEntry → EntryFrame s ra → ServiceReady L A c s →
    s.data.regs.rdi.toNat = L.cache → s.data.regs.get (.low .rsi .W32) = 0xdc0#32 →
    (ra.toNat, record.site) ∈ allocSites → A.Idle s.data.dmem live (record :: stream) →
    Eventually (instructionStep fetch) (fun t =>
      Returned s t ra ∧ EqualOutside (ServiceWrites L A c s live) s.data.dmem t.data.dmem ∧
      c.At t.data.dmem ∧ AllocResult L A live record stream t) s
  free : ∀ (c : CommonBitsCoverage.Context) (s : MachineState) (ra : UInt64) live stream,
    s.pc = freeEntry → EntryFrame s ra → ServiceReady L A c s → ra.toNat = freeSite →
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

def Executed (fetch : Int64 → Option Decoded) (L : Layout) (A : Allocator) : Prop :=
  ∃ (w0 w1 w2 w3 w4 : World) (d0 d3 : Device) (c1 c2 c3 c4 : Context)
    (s1 t1 s2 t2 s3 t3 s4 t4 : MachineState) (h1 h2 h3 h4 : List MachineState)
    (k1 n1 p1 k2 n2 p2 k3 n3 p3 key pointer : Nat) (found : PeerId) (ra : UInt64)
    (stream : List HiddenRecord),
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
    c2.Needed

def ServiceActive (fetch : Int64 → Option Decoded) (L : Layout) (A : Allocator) : Prop :=
  0 < A.depth ∧
  ∃ (c : Context) (s t : MachineState) (ra : UInt64) (live : List Nat) (record : HiddenRecord)
    (stream : List HiddenRecord) (history : List MachineState),
    s.pc = allocEntry ∧ EntryFrame s ra ∧ ServiceReady L A c s ∧
    s.data.regs.rdi.toNat = L.cache ∧ s.data.regs.get (.low .rsi .W32) = 0xdc0#32 ∧
    (ra.toNat, record.site) ∈ allocSites ∧ A.Idle s.data.dmem live (record :: stream) ∧
    c.Needed ∧ record.bytes.head? = some 1 ∧
    Ran fetch s t ra history ∧
    (∃ a, Scratch s A.depth a ∧ s.data.dmem.get? a ≠ t.data.dmem.get? a) ∧
    (∃ a, c.writes a ∧ s.data.dmem.get? a ≠ t.data.dmem.get? a)

def Witness : Prop :=
  ∃ (fetch : Int64 → Option Decoded) (L : Layout) (A : Allocator),
    Premises fetch L A ∧ CallbacksFromImage fetch ∧ Executed fetch L A ∧ ServiceActive fetch L A
```

`SeqAdvanced`, the write sets, `Ran`, `HeapSame`, `outcome`, the two
exclusions, the layout, the literals, the executable caller conditions and
the ten instruction terms are in [appendix A](#appendix-a-the-rest-of-the-signed-text).
They are part of what is signed.

## 3. The difference from revision 2

`git diff 7d39d508 -- binary/StatementC1*.lean`: 142 lines added, 41
removed, in twelve hunks; the raw diff is [appendix D](#appendix-d-the-diff-against-revision-2).
`StatementC1CallbackImage.lean` has no hunk.

| File, hunk | What | Reason | Decision |
| --- | --- | --- | --- |
| Contracts `@@ -64` (1) | New `Separated`; `ServiceReady` gains the parameter `L` and the field `separated`; its comment | Without it a context could read the allocator's state as its mode word, and no allocator with ordinary state met the contract | 4 |
| Contracts `@@ -64` (2) | `a + nodeSize < 2^64 ∧` in `AllocResult`; its comment | The landed relation demands it of every node | 1 |
| Contracts `@@ -98` | `ServiceReady A c s` becomes `ServiceReady L A c s`, twice | Follows from the new parameter | 4 |
| Headline `@@ -7` | File comment: the sequences covered include reference moves | Comment only | 2 |
| Headline `@@ -85`, `@@ -98` | `insertReady`: the clause `c1.stack-peers`; its comment | The landed `NodeInit.boundary` needs `add`'s stack bytes apart from whole peer objects; without it the trunk's cut needs an extra hypothesis | B |
| Headline `@@ -158` | New `CountMoved`, `Referenced` | The clause itself | 2 |
| Headline `@@ -158`, within `Referenced` | The take is `peerGetMaybeZero (some pid)` returning `some pid`; the comment cites the kernel's lines | The operation `set_peer` performs on an existing peer (R1); `peerGet` leaves the claim | A |
| Headline `@@ -215` | `Referenced L Inv` in `Headline`'s conjunction; its comment | The clause is claimed | 2 |
| Headline `@@ -241` | The same conjunct in `HeadlineExplicit` (not signed) | Keeps "implies `Headline`" true | 2 |
| Vacuity `@@ -3` | File comment | Comment only | 5 |
| Vacuity `@@ -30`, `@@ -67` | `Witness` split into `Executed`, `ServiceActive` and the conjunction; the mid-history clause removed; comments | Provable from the headline's shape | 5 |
| Vacuity `@@ -133` | The comment on `Signed` (the register wording): the witness's relation to the headline; "with the caller's references on registered peers taken and dropped between them"; "ending below 2^64" | Says what the revised result establishes. Comment only, but it is the wording the register entry will use | 1, 2, 5 |

Not statement text, changed to follow: `C1Interfaces.lean`, `C1Assembly.lean`
(section 6), `Statements/C1/Test.lean`, `run-tests.sh`,
`capture/Check.lean`, `capture/summarise.py`, `measure-surface.py`,
`proof/TopOfMemory.lean`, new `proof/StateWord.lean` and
`proof/StackOffPeers.lean`, and a note at the top
of `proof/PLAN.md` section 0.

## 4. Sizes

By the project's definition of trust surface (`docs/decisions.md`,
2026-11-10), in printed lines the way `binary/surface.py` prints the landed
file (`measure-surface.py`):

| | Revision 2 | Revision 3 | Revision 4 | What changed |
| --- | ---: | ---: | ---: | --- |
| **Assumed**: layout, service contract, `Premises` | 230 | 257 | 257 | Revision 3: `Separated` 24; `ServiceReady`, `AllocResult` and the contract +3 |
| **Assumed**: caller conditions and the starting point | 183 | 183 | 197 | Revision 4: `insertReady` +14 (change B) |
| **Assumed**: existing package definitions the premises draw in, not in the landed file | 174 | 187 | 187 | Revision 3: `Context.bytes` 4, `Context.metadataBytes` 9 |
| **Assumed, total new** | **587** | **627** | **641** | |
| **Claimed**: `Headline` and its clauses, `SeqAdvanced`, the write sets | 80 | 110 | 111 | Revision 3: `CountMoved` 19, `Referenced` 10, `Headline` +1. Revision 4: `Referenced` 11 (change A) |
| **Claimed**: existing definitions the conclusion draws in | 22 | 22 | 22 | |
| **Claimed**: the witness, the exclusions, `Signed` | 127 | 167 | 167 | Revision 3: `Witness` 24 becomes `Executed` 26, `ServiceActive` 31 and `Witness` 7 |
| **Claimed**: the ten instruction terms and their `fetch` (change 3) | 75 | 75 | 75 | |
| **Claimed, total new** | **304** | **374** | **375** | |

Uncounted in printed lines, as before, the definitional closure of `Signed`
in hand-written declarations:

| | Revision 2 | Revision 3 | Revision 4 |
| --- | ---: | ---: | ---: |
| Closure of `Signed` | 988 | 1,015 | 1,013 |
| of which the mirror's | 372 | 391 | 389 |
| of which Kraken's | 188 | 188 | 188 |

Change A takes `peerGet` and `refcountInc` out (`Leanux.WG.Peer` 4 to 3,
`Leanux.Kernel.Refcount` 3 to 2); change B adds none. What `Referenced` still draws in
beyond revision 2 is `peerPut`, its release path included, although
`1 < count` keeps every admitted run off it. The packet's proposed budgets
were 600 assumed and 230 claimed: **the assumed kind is now 41 lines over
its budget**, and the claim proper (without the listing) is 300.

## 5. The reruns on the revised text

All numbers in this section are of revision 4's text.

**Build and gate.** `lake -d binary build`: 1,131 jobs. `scripts/binary-proof-gate`:
PASS, printed surface unchanged. `#print axioms signed_of_parts`: `propext`,
`Classical.choice`, `Quot.sound`.

**The packet's tests** (`binary/Statements/C1/run-tests.sh`): `PASS`.

- The search, with the separation of `ServiceReady` now evaluated at every
  service entry and the bound on every returned object: 23 families, 900
  insertions, 4,124 lookups, every family `holds`, deepest stack write 200,
  23 distinct mirror decisions in each. The same numbers as revision 2: the
  new premises (the service's separation, the stack window apart from the
  peers) refuse none of the families and the test service meets the
  revised clauses in all of them. The invariant, step, walk and cut checks
  the architect added run inside these and pass.
- The 5 refusals, H1 under the revision 1 contract (conclusion broken) and
  under revision 3 (excluded by the write clause), H2 under both, the frame
  probes: as before.
- New, change 4: the test service with its index word at `arena+16`, at a
  plain entry state, meets every clause of revisions 2 and 3 and advances
  the word; at the aliased state revision 2 admits the state and the
  service fails `c.At` afterwards, revision 3 refuses the state
  (`ready.separated.coverage-arena`); a stack scratch inside the arena is
  refused (`ready.separated.stack-arena`).
- New, change 5: `ServiceActive` evaluated on the test service at that
  state holds; on the quiet service it fails.
- New, change B: a stack window inside a peer object, below its count and
  list head, satisfies `frameReady` whole and is refused by `insertReady`
  at `c1.stack-peers`.
- New, changes 2 and A: a reference moved from one peer to another (`peerPut`
  then `peerGetMaybeZero` returning the peer, each with its count word) is accepted and the invariant's
  decidable part holds after each step; refused are a count raised with no
  mirror step, a count raised by two with one take, a paired step with
  a root word or an arena byte changed as well, the last reference dropped,
  and a peer the layout does not name; the invariant's decidable part fails
  after an unpaired change in either direction. Two more families run the
  whole scenario with the caller's reference following the peer being
  configured, as `set_peer` does: 36 insertions, 168 lookups and 21
  reference steps each, `holds`.
- The three regression files elaborate: `TopOfMemory.lean`,
  `StateWord.lean` (two theorems) and `StackOffPeers.lean` (the trunk's
  hypothesis as a theorem), standard axioms.

**The capture's checks** on the captured states (raw captures still in
`.tmp/c1`; no guest was booted again, so nothing new was captured):

| | Revision 2 | Revisions 3 and 4 |
| --- | --- | --- |
| Calls evaluated in Lean, each under two seeds | 20 | 20 |
| Every check of revision 2 (entry, 23 service calls, return, frame, the landed relation, the invariant, step and walk checks, 33 lookups) | pass | pass, same counts |
| `ServiceReady.separated`, four conjuncts, at each captured service entry | not stated | 23/23 ×2 each |
| `AllocResult` with the bound | 22/22 ×2 without it | 22/22 ×2 |
| `insertReady` with `c1.stack-peers` (window); the clause on its own | 20/20 ×2 without it | 20/20 ×2; 20/20 ×2 |
| Gaps between calls read as steps of the closed world | counts re-read from memory | 2 reference steps at the grid's change of peer, each accepted; every other gap empty |
| Calls covered from the empty table: `c1_capture_grid` | 5 of 13 | **13 of 13** |
| Calls covered: `b1_trie_routing` | 2 of 8 | 2 of 8 |
| Calls covered: the three failure traces | 1, 2, 2 (all) | 1, 2, 2 (all) |
| `emptyTable` and `insertReady` verbatim on the first call with the 32 MiB buffer loaded | ok | ok (rerun) |

Under revision 2 the grid's last 8 calls were checked with the mirror's
counts overwritten from memory; under revision 3 the same calls are reached
by two steps of the clause (`peerPut`, then `peerGetMaybeZero` returning the
peer) and nothing is overwritten. The whole-RAM
comparison of the gaps (from the first run's dumps, which are deleted as
they are compared) agrees: the only heap bytes the caller changed in the
grid are the two counts.

Could not be rerun: nothing. Not run at all, as before: `Idle` and `frame`
(abstract), anything concurrent.

## 6. The interfaces and the assembly

`signed_of_parts` is proved for the revised `Signed` from the interface
propositions (no `sorry`; standard axioms). It lost the hypothesis
`NodeBelowTop` and gained `ReferencedHolds`; revision 4 changes nothing in
`C1Assembly.lean`. What changed, and what it does to the closed proofs on
`task/binary-c1-wp1` (`73387d54`), `task/binary-c1-wp4` (`93226094`) and the
trunk on `task/binary-c1-wp2` (`bccece9c`); "compiled" means I compiled that
branch's files against revision 4 in a scratch directory, without touching
the branch:

| Proposition (package) | Statement | Definitions under it | Closed proof |
| --- | --- | --- | --- |
| `RunIsStep` (1) | unchanged | none changed | **unchanged**: compiled |
| `InitialHolds`, `FramedHolds`, `LookupHolds` (1) | unchanged | `Premises` (through the contract) | **unchanged**: compiled |
| `ExclusionOne`, `ExclusionTwo` (1) | unchanged | `Premises`; `HeadlineFor` keeps its four clauses for this reason | **unchanged**: compiled |
| `ReferencedHolds` (1) | **new** in revision 3; same text over revision 4's `Referenced` | `Referenced` (the take) | **real work**, not yet proved, so change A costs nothing. It is easier than before: the take is the operation the mirror's lookup runs, so what `lookup_checked` already proves of `peerGetMaybeZero` (`target_mapCounts`, `heap_mapCounts`) applies directly |
| `AllocRule`, `FreeRule` (4) | unchanged | `AllocResult` (one more conjunct in the conclusion, from the contract), `ServiceReady`, `insertReady` | **mechanical**: the package's `separated` moved before `serviceReady`, one field and the layout argument added; for revision 4 one more line in `ready_of_insertReady` (the new clause is taken off before `frameReady` is unfolded); then both compiled |
| `Cmp1FromImage`, `Cmp8FromImage` (4) | unchanged | none changed | **unchanged**: compiled |
| `PremisesMet` (4) | **restated**: gains `∃ m stream, A.Idle m [] stream` | `Premises` | **mechanical**: the layout argument at two places and one arithmetic conjunct in `Stub.contract`; the new conjunct from the package's `idle_initial`; then compiled |
| `WitnessHolds` (4) | same text | `Witness` restated | **real work**, and was not closed: `Executed` through the headline (the package's `ran_of_eventually`), and a stub that uses its stack and writes the buffer, re-proved against the contract |
| `NodeBelowTop` | unchanged | `AllocResult` | now a theorem; the path propositions that take it as a hypothesis are unchanged |
| `Path k`, the nine path propositions, `TrunkToNode`, `TrunkHolds` (2, 3) | unchanged | `Premises`; `AllocRule`'s `AllocResult`; `insertReady` | proofs that take `AllocResult`'s success clause apart by position meet one more component, third; proofs that take `insertReady` apart clause by clause meet one more clause before `frameReady` |
| The trunk's `trunkToNodePlus_of_stackOffPeers`, `trunkHolds_of_stackOffPeers`, `pathChild_of_stackOffPeers` (2) | not interface propositions: each is the interface's with the extra hypothesis `C1Trunk.StackOffPeers` | `insertReady` | **closed by change B**: `C1Trunk.StackOffPeers` is now a theorem (one step from the new clause: `proof/StackOffPeers.lean`), so the three become the interface's `TrunkHolds`, `PathChild` and the strengthened trunk package 3 takes. Compiled: the trunk's 42 modules at `bccece9c` against revision 4 with two one-line repairs (`insertReady_facts` takes the new clause off; `object_of_result` skips revision 3's bound), then the hypothesis derived and all three applied to it, standard axioms |
| `HeadlineFor`, `InsertPost`, `StepFacts`, `InFlight`, `Protected`, `NodeCut`, `Exits` | unchanged | none changed | |

The service package's finding file (`C1ServiceContractFinding`) no longer
compiles, as intended: `word_kept` and `no_state_word` are theorems about
revision 2.

## 7. What I could not do as decided, and what I flag

Each change was made as decided. Four things the owner and the reviewer
should know that the decision did not anticipate:

0. **Revision 4.** Both changes were made as decided and neither forced
   another. Change B is in `insertReady` only; `frameReady` and the
   lookup's conditions keep their text. The window in the new clause leaves
   out the return word, as decided and as the trunk's hypothesis has it;
   the return word is therefore still kept apart from a peer's count and
   list head only, which no proof so far needs more of.
1. **Change 4 forces a parameter.** `ServiceReady` cannot state separation
   from the arena without the layout, so it is now `ServiceReady L A c s`.
   This is inside the named change but it touches the two contract clauses.
2. **Change 2 does not reach `b1_trie_routing`.** The decision's wording
   (what a real `wg set` does between peers) is met for a `wg set` over
   peers that exist when the table is empty. A `wg set` or `wg setconf` that
   creates its peers and gives them allowed addresses in one message, which
   is how an interface is usually configured, is covered for its first peer
   only.
3. **The assumed kind is over the packet's budget** (641 against 600), and
   the mirror's share of the claim grew by `peerPut` (revision 3's `peerGet`
   left with change A).
4. **The witness is weaker in one respect** (section 1, change 5), and its
   satisfiability by a stub is argued and tested, not proved.

Smaller: `HeadlineExplicit` (unsigned) gained the same conjunct; the comment
on `Signed`, which is the register wording, changed in three phrases.

## 8. What the owner is accepting knowingly

1. **Closed-world, now one step wider.** The invariant is hidden, so the
   conclusion holds only along sequences made of: insertions; lookups;
   changes outside the heap (`Framed`); and, new, a registered peer's
   reference count going up by one with the mirror's `peerGetMaybeZero`
   returning that peer, or down by one from above one with the mirror's
   `peerPut`. Those are the mirror's operations for what `set_peer` does to
   an existing peer: the take through `wg_pubkey_hashtable_lookup`
   (`wg_peer_get_maybe_zero`), the drop by `wg_peer_put`. Exactly that wide: not
   peer creation or removal, not the last reference dropped, not a count
   changed by more than one at a step, not a count changed while any other
   heap byte changes, not a reference the mirror refuses to take (a count
   of zero, or saturation). A later result on removal or the dump replaces
   this one; it cannot extend it. **A `wg set` or `wg setconf` that creates
   its peers and gives them allowed addresses in one message, which is how
   an interface is usually configured, is covered for its first peer only**:
   creating a peer changes the peer set, and the layout's peers are fixed at
   the empty table. The mirror's `peerPut` is now inside the claim
   (`peerGetMaybeZero` already was, through the lookup).
2. **What the witness shows and does not.** It shows that one decoder,
   layout and allocator meet every premise with the image's callbacks; that
   with them an actual execution runs through each kind of call from an
   empty table and returns; and that the service at the allocation address,
   under the same contract, uses its stack and writes the coverage buffer
   from an admissible entry state. It does not show that the service does
   so during an insertion, and it says nothing of the image's allocator:
   the service is a stub.
3. **Parent pointers, the peers' node lists and the internal nodes' list
   heads are not claimed.** Nothing with an observable conclusion reads
   them.
4. **The mirror's definition of an accepted run is inside the claim** and
   is not in the printed line counts: 391 declarations of the closure.
5. **Nothing is claimed of the kernel's allocator.** The result is about
   the six functions given any code at the two service addresses that meets
   the contract. Revision 3's contract is one an allocator with ordinary
   internal state can meet, which revision 2's was not; the image's
   allocator still cannot, under this semantic base (appendix C).
6. **Where the mirror refuses, the claim is silent**: a trie deeper than
   its bound, a lookup that would retry on a dying peer, a peer with a
   pending worker, a short record list, and reference-count saturation,
   which is reachable inside the closed world.
7. **Decoder agreement is tested, not proved**; at the two service
   addresses the guest does not run the ELF's bytes at three sites.
8. **Sequential model**, and **an instrumented image**: one CPU stepping
   these instructions alone, on the saved s5 oracle build with KCOV
   callbacks.

Unchanged and still to be accepted: the caller's conditions are not shown
to hold at any real call by proof (the capture shows them at 20); the
over-long-prefix exit is not reachable from the real caller; the NULL-peer
exit is outside. New with revision 4 among the caller's conditions: the
insertion's stack window does not lie in a peer object (true of the 20
captured calls, where the stack is a kernel stack).

## Appendix A: the rest of the signed text

```lean
def SeqAdvanced (L : Layout) (s t : MachineState) : Prop :=
  ∃ before, readNat s (L.table+AllowedipsMutationLayout.seq) 8 = .ok before ∧
    readNat t (L.table+AllowedipsMutationLayout.seq) 8 = .ok ((before+1) % 2^64)

def InsertWrites (L : Layout) (A : Allocator) (c : Context) (s : MachineState) (a : BitVec 64) : Prop :=
  Scratch s (insertWindow + A.depth) a ∨ c.writes a ∨ L.Heap a

def LookupWrites (L : Layout) (c : Context) (s : MachineState) (a : BitVec 64) : Prop :=
  AllowedipsEntry.TotalWrites s c.coverage c.preempt a ∨ L.Heap a

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
  require (spansApart [((s.data.regs.rsp.toBitVec - .ofNat 64 (insertWindow + A.depth)).toNat, insertWindow + A.depth)]
    (L.peers.map fun (_,a) => (a,Layouts.peerSize))) "c1.stack-peers"
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

`binary/StatementC1CallbackImage.lean`, whole (unchanged):

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
cap scripts/in-bundle lake -d binary build                                   # 1,131 jobs
cap scripts/in-bundle /usr/bin/python3 scripts/binary-proof-gate             # PASS
cap scripts/in-bundle /usr/bin/python3 -B binary/generate_c1_callbacks.py --check
cap scripts/in-bundle /usr/bin/python3 -B binary/allowedips_mutation.py      # writes the tests' input
binary/Statements/C1/run-tests.sh                                            # about 20 minutes; PASS
binary/Statements/C1/capture/run-capture.sh                                  # about 10 minutes
cap scripts/in-bundle /usr/bin/python3 -B binary/Statements/C1/measure-surface.py
```

`run-tests.sh` first elaborates the three regression files, then runs
`Test.lean`; `lean --run Statements/C1/Test.lean INPUT.json probes` runs
everything but the search over the 23 families (about two minutes).

`run-capture.sh` records each trace (`evaluator.check --binary-coverage
--binary-profile allowedips-insert`), captures it
(`capture_insertions.py`), analyses it (`analyse.py`), runs `Check.lean`
on it, runs the verbatim readiness check on the grid's first call with the
whole buffer loaded (about three minutes, 5.4 GiB), and prints the counts
(`summarise.py`). The grid trace is copied into `corpus/wireguard` for its
recording and removed again; it is not a corpus trace. Outputs are under
`.artifacts/check/c1-*` and `.tmp/c1/capture-*`, ignored and not committed:
up to about 90 MiB per trace, the RAM dumps deleted as they are compared.
For revisions 3 and 4 the captures of the first run were kept and only
`Check.lean` and `summarise.py` were run again on them.

The capture reported here: s5 image `06513d05…e88e`, Kraken `43df9468`,
QEMU's `qemu64` CPU under TCG, 256 MiB, one CPU, `nokaslr`.

## Appendix C: the capture

This is section 1 of revision 2 of this document: the recording-armed
capture of real insertions, run against revision 2's text. Its counts are
revision 2's; the rerun of its checks on revision 3 is in section 5. Its
closing judgement, that the proof could start as signed, was overtaken by
the three findings behind this revision and is not repeated.

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
   is silent there. (Revision 3 changes this for the grid: change 2 in
   section 1.)

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

### The calls

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

## Appendix D: the diff against revision 2

`git diff 7d39d508 -- binary/StatementC1Contracts.lean binary/StatementC1Headline.lean binary/StatementC1CallbackImage.lean binary/StatementC1Vacuity.lean`:

```diff
diff --git a/binary/StatementC1Contracts.lean b/binary/StatementC1Contracts.lean
--- a/binary/StatementC1Contracts.lean
+++ b/binary/StatementC1Contracts.lean
@@ -64,26 +64,45 @@ def ServiceWrites (L : Layout) (A : Allocator) (c : CommonBitsCoverage.Context)
     (s : MachineState) (kept : List Nat) (a : BitVec 64) : Prop :=
   Scratch s A.depth a ∨ (L.Arena a ∧ ¬Kept kept a) ∨ c.writes a
 
+/-- Where the service's bytes are, relative to the coverage context it is
+called under (revision 3): its stack (the scratch and the return word), the
+arena and the bytes the coverage context reads are pairwise apart, and the
+coverage buffer is apart from the coverage metadata and the preemption
+count. An insertion's caller conditions give this at every service call
+(`frameReady`'s separations); without it a context could place its mode
+word on the allocator's own state, and no allocator that changes a word of
+the arena would meet the contract. -/
+structure Separated (L : Layout) (A : Allocator) (c : CommonBitsCoverage.Context) (s : MachineState) : Prop where
+  stackArena : ∀ a, Scratch s A.depth a ∨ InRange s.data.regs.rsp.toBitVec 8 a → ¬L.Arena a
+  stackCoverage : ∀ a, Scratch s A.depth a ∨ InRange s.data.regs.rsp.toBitVec 8 a → ¬c.bytes a
+  coverageArena : ∀ a, c.bytes a → ¬L.Arena a
+  bufferMetadata : ∀ a, c.writes a → ¬c.metadataBytes a ∧ ¬InRange preemptCountAddress 4 a
+
 /-- What a service may assume at its entry besides its arguments, in the form
 of the landed `RandomReady`: valid coverage state with room for a record
-when the buffer is in use, the direction flag clear, and `depth` mapped
-bytes of stack below the return word. Revision 2. -/
-structure ServiceReady (A : Allocator) (c : CommonBitsCoverage.Context) (s : MachineState) : Prop where
+when the buffer is in use, the direction flag clear, `depth` mapped bytes of
+stack below the return word (revision 2), and the separation of its stack,
+the arena and the coverage bytes (revision 3). -/
+structure ServiceReady (L : Layout) (A : Allocator) (c : CommonBitsCoverage.Context) (s : MachineState) : Prop where
   coverage : c.At s.data.dmem
   capacity : c.Needed → 0 < c.coverage.capacity.toNat
   forward : s.data.system.bits[10] = false
   stackMapped : ∀ i < A.depth,
     (s.data.dmem.get? (s.data.regs.rsp.toBitVec - .ofNat 64 A.depth + .ofNat 64 i)).isSome = true
+  separated : Separated L A c s
 
 /-- What one `kmem_cache_zalloc(node_cache, GFP_KERNEL)` leaves behind, by the
 recorded outcome byte: NULL and nothing handed out, or an aligned, zeroed
-72-byte object inside the arena that overlaps no object already handed out. -/
+72-byte object inside the arena that overlaps no object already handed out
+and ends strictly below 2^64 (revision 3: the bound the landed
+interpretation check `Trie.validate` demands of every node). -/
 def AllocResult (L : Layout) (A : Allocator) (live : List Nat) (record : HiddenRecord)
     (stream : List HiddenRecord) (t : MachineState) : Prop :=
   let a := t.data.regs.rax.toNat
   (record.bytes.head? = some 0 → a = 0 ∧ A.Idle t.data.dmem live stream) ∧
   (record.bytes.head? = some 1 →
-    a ≠ 0 ∧ a % 8 = 0 ∧ (∃ span ∈ L.arena, span.1 ≤ a ∧ a+nodeSize ≤ span.1+span.2) ∧
+    a ≠ 0 ∧ a % 8 = 0 ∧ a + nodeSize < 2^64 ∧
+    (∃ span ∈ L.arena, span.1 ≤ a ∧ a+nodeSize ≤ span.1+span.2) ∧
     (∀ other ∈ live, disjointRanges a nodeSize other nodeSize = true) ∧
     readNat t a nodeSize = .ok 0 ∧ A.Idle t.data.dmem (live ++ [a]) stream)
 
@@ -98,14 +117,14 @@ structure AllocatorContract (fetch : Int64 → Option Decoded) (L : Layout) (A :
   frame : ∀ m m' live stream, A.Idle m live stream →
     (∀ a, L.Arena a → ¬Kept live a → m.get? a = m'.get? a) → A.Idle m' live stream
   alloc : ∀ (c : CommonBitsCoverage.Context) (s : MachineState) (ra : UInt64) live record stream,
-    s.pc = allocEntry → EntryFrame s ra → ServiceReady A c s →
+    s.pc = allocEntry → EntryFrame s ra → ServiceReady L A c s →
     s.data.regs.rdi.toNat = L.cache → s.data.regs.get (.low .rsi .W32) = 0xdc0#32 →
     (ra.toNat, record.site) ∈ allocSites → A.Idle s.data.dmem live (record :: stream) →
     Eventually (instructionStep fetch) (fun t =>
       Returned s t ra ∧ EqualOutside (ServiceWrites L A c s live) s.data.dmem t.data.dmem ∧
       c.At t.data.dmem ∧ AllocResult L A live record stream t) s
   free : ∀ (c : CommonBitsCoverage.Context) (s : MachineState) (ra : UInt64) live stream,
-    s.pc = freeEntry → EntryFrame s ra → ServiceReady A c s → ra.toNat = freeSite →
+    s.pc = freeEntry → EntryFrame s ra → ServiceReady L A c s → ra.toNat = freeSite →
     s.data.regs.rdi.toNat = L.cache → s.data.regs.rsi.toNat ∈ live →
     A.Idle s.data.dmem live stream →
     Eventually (instructionStep fetch) (fun t =>
diff --git a/binary/StatementC1Headline.lean b/binary/StatementC1Headline.lean
--- a/binary/StatementC1Headline.lean
+++ b/binary/StatementC1Headline.lean
@@ -7,7 +7,9 @@ compiled allowed-IPs insertion of the pinned s5 image, as `def … : Prop`.
 `Headline` keeps the memory relation internal (an existentially quantified
 invariant): what a reader takes away is machine-observable, the 32-bit
 result of every insertion and the peer pointer returned by every later
-lookup, along any call sequence that starts at a physically empty table.
+lookup, along any call sequence that starts at a physically empty table,
+with the caller's references on registered peers taken and dropped between
+the calls (revision 3).
 `HeadlineExplicit` is the alternative with the landed relation in its
 conclusion; it implies `Headline`, and it is what a proof would exhibit. -/
 namespace Binary.Statements.C1
@@ -85,7 +87,11 @@ def frameReady (L : Layout) (c : Context) (s : MachineState) (ra : UInt64)
 /-- A call of `wg_allowedips_insert_v4/_v6(table, ip, cidr, peer, lock)`:
 the wrapper's entry, the table, the address bytes in network order, the
 8-bit prefix length, a non-NULL registered peer, the `node_cache` word, and
-room below the stack for the allocator's scratch. -/
+room below the stack for the allocator's scratch. Revision 4: the stack
+window below the return word is apart from every peer as a whole object
+(`frameReady` keeps it apart from the heap, which holds only a peer's
+reference count and list head; the landed `NodeInit.boundary` needs `add`'s
+stack bytes apart from the whole 1520-byte object). -/
 def insertReady (L : Layout) (A : Allocator) (c : Context) (s : MachineState)
     (family key cidr pid : Nat) (ra : UInt64) : Except String Unit := do
   require (family == 4 || family == 6) "c1.family"
@@ -98,6 +104,8 @@ def insertReady (L : Layout) (A : Allocator) (c : Context) (s : MachineState)
   require (s.data.regs.rdx.toNat % 256 == cidr) "c1.insert-cidr"
   require (Trie.networkKeyCheck s.data.dmem s.data.regs.rsi.toBitVec width key) "c1.insert-address"
   require ((← readNat s cacheWord 8) == L.cache) "c1.node-cache"
+  require (spansApart [((s.data.regs.rsp.toBitVec - .ofNat 64 (insertWindow + A.depth)).toNat, insertWindow + A.depth)]
+    (L.peers.map fun (_,a) => (a,Layouts.peerSize))) "c1.stack-peers"
   frameReady L c s ra (insertWindow + A.depth) (s.data.regs.rsi.toNat, width/8) true false
 
 /-- A call of the compiled `lookup(root, bits, ip)` as its two callers make
@@ -158,6 +166,35 @@ between calls. -/
 def Framed (L : Layout) (Inv : World → Mem 64 → Prop) : Prop :=
   ∀ w m m', Inv w m → (∀ a, L.Heap a → m.get? a = m'.get? a) → Inv w m'
 
+/-- Memory `m'` is memory `m` with peer `pid`'s four-byte reference count
+changed from `before` to `after`: both are readable, and every other heap
+byte is the same. Bytes outside the heap are unconstrained, as in `Framed`. -/
+def CountMoved (L : Layout) (pid : PeerId) (before after : Nat) (m m' : Mem 64) : Prop :=
+  ∃ peer, Trie.address L.peers (some pid) = .ok peer ∧
+    readNat ⟨{dmem := m},0⟩ (peer+Root.nodeOffsets.peerRefcount) 4 = .ok before ∧
+    readNat ⟨{dmem := m'},0⟩ (peer+Root.nodeOffsets.peerRefcount) 4 = .ok after ∧
+    ∀ a, L.Heap a → ¬InRange (.ofNat 64 (peer+Root.nodeOffsets.peerRefcount)) 4 a → m.get? a = m'.get? a
+
+/-- Revisions 3 and 4. The invariant survives the caller taking or dropping
+one reference on a registered peer between calls: the peer's count word goes
+up by one together with the mirror's `peerGetMaybeZero` on that peer
+returning the peer, or down by one, from a count above one, together with
+the mirror's `peerPut` on it (the last reference is not dropped here: that
+is the peer's removal). No other heap byte changes and no other mirror
+operation runs. This is what a `wg set` over existing peers does between
+the insertions for one peer and those for the next: `set_peer` drops its
+reference on the first (`wg_peer_put`, netlink.c:486) and takes one on the
+second through `wg_pubkey_hashtable_lookup`, that is
+`wg_peer_get_maybe_zero` (netlink.c:386, peerlookup.c:68). `wg_peer_get` is
+called only on a peer just created (netlink.c:421), which is outside. -/
+def Referenced (L : Layout) (Inv : World → Mem 64 → Prop) : Prop :=
+  ∀ (w w' : World) (m m' : Mem 64) (pid : PeerId) (count : Nat), Inv w m →
+    ((liftWG (WG.peerGetMaybeZero (some pid))).run w = .ok (some pid, w') ∧
+      CountMoved L pid count (count+1) m m') ∨
+    ((liftWG (WG.peerPut (some pid))).run w = .ok ((), w') ∧ 1 < count ∧
+      CountMoved L pid count (count-1) m m') →
+    Inv w' m'
+
 /-- The table's sequence word after the call is the word before plus one,
 modulo 2^64: what a wrapper does besides calling `add`. -/
 def SeqAdvanced (L : Layout) (s t : MachineState) : Prop :=
@@ -215,14 +252,16 @@ def LookupStep (fetch : Int64 → Option Decoded) (L : Layout)
       EqualOutside (LookupWrites L c s) s.data.dmem t.data.dmem) s
 
 /-- THE HEADLINE. Under the premises there is an invariant, holding
-at every empty table, insensitive to memory outside the heap, preserved by
-every insertion and every lookup, under which each returns what the mirror
-returns. The relation between memory and the mirror is not part of the
+at every empty table, insensitive to memory outside the heap, surviving the
+caller's reference on a peer being taken or dropped between calls
+(revision 3), preserved by every insertion and every lookup, under which
+each returns what the mirror returns. The relation between memory and the mirror is not part of the
 claim; a proof must exhibit one. -/
 def Headline : Prop :=
   ∀ (fetch : Int64 → Option Decoded) (L : Layout) (A : Allocator), Premises fetch L A →
     ∃ Inv : World → Mem 64 → Prop,
-      Initial L A Inv ∧ Framed L Inv ∧ InsertStep fetch L A Inv ∧ LookupStep fetch L Inv
+      Initial L A Inv ∧ Framed L Inv ∧ Referenced L Inv ∧
+      InsertStep fetch L A Inv ∧ LookupStep fetch L Inv
 
 /-! ## The alternative: the landed relation in the conclusion -/
 
@@ -241,12 +280,12 @@ def Related (L : Layout) (A : Allocator) (w : World) (m : Mem 64) : Prop :=
     (∀ node ∈ names.trie.nodes, ∃ span ∈ L.arena, span.1 ≤ node.2 ∧ node.2+nodeSize ≤ span.1+span.2) ∧
     A.Idle m (names.trie.nodes.map (·.2)) stream
 
-/-- The same four clauses with the invariant fixed to `Related`. It implies
+/-- The same five clauses with the invariant fixed to `Related`. It implies
 `Headline`; it additionally tells a reader what memory looks like after
 each call, in terms nothing but tests and reading pin down. -/
 def HeadlineExplicit : Prop :=
   ∀ (fetch : Int64 → Option Decoded) (L : Layout) (A : Allocator), Premises fetch L A →
-    Initial L A (Related L A) ∧ Framed L (Related L A) ∧
+    Initial L A (Related L A) ∧ Framed L (Related L A) ∧ Referenced L (Related L A) ∧
     InsertStep fetch L A (Related L A) ∧ LookupStep fetch L (Related L A)
 
 end Binary.Statements.C1
diff --git a/binary/StatementC1Vacuity.lean b/binary/StatementC1Vacuity.lean
--- a/binary/StatementC1Vacuity.lean
+++ b/binary/StatementC1Vacuity.lean
@@ -3,7 +3,8 @@ import StatementC1CallbackImage
 
 /-! Result C1, final statement: the kernel-checked evidence against vacuity that
 the result carries, as statements (no theorem, no proof), and `Signed`. `Witness` says the
-premises can be met along an actual execution through every kind of call;
+premises can be met along an actual execution through every kind of call,
+by a service that uses its stack and writes the coverage buffer;
 the two exclusions are consequences with no mirror state in their
 conclusion, naming machine behaviours the headline rules out. -/
 namespace Binary.Statements.C1
@@ -30,25 +31,22 @@ def CallbacksFromImage (fetch : Int64 → Option Decoded) : Prop :=
   ServiceDecoderAgreement fetch ∧
   ∀ pc instruction, StatementC1CallbackImage.fetch pc = some instruction → fetch pc = some instruction
 
-/-- WITNESS. Some `fetch`, layout and allocator meet every premise, the
-callbacks being the image's own code (`CallbacksFromImage`: only the code at
-`allocEntry` and `freeEntry` may be a stub), and an actual execution runs, from a physically empty table with
-the allocator idle and five answers pending, through: an insertion into the
-empty table; an insertion that allocates twice (the intermediate node,
-while a node is handed out); an insertion whose second allocation is
-refused (the rollback and the release); and a lookup that finds a peer.
-Each call meets its caller conditions and the mirror accepts it, consuming
-exactly those records. The code at `allocEntry` uses a nonempty stack
-scratch and, with the coverage buffer in use, changes a scratch byte and a
-buffer byte during the second call's allocation. The service will be a
-stub and is to be called one. -/
-def Witness : Prop :=
-  ∃ (fetch : Int64 → Option Decoded) (L : Layout) (A : Allocator)
-    (w0 w1 w2 w3 w4 : World) (d0 d3 : Device) (c1 c2 c3 c4 : Context)
+/-- EXECUTED (the end-to-end half of the witness, revision 3). With this
+`fetch`, layout and allocator an actual execution runs, from a physically
+empty table with the allocator idle and five answers pending, through: an
+insertion into the empty table; an insertion that allocates twice (the
+intermediate node, while a node is handed out) with the coverage buffer in
+use; an insertion whose second allocation is refused (the rollback and the
+release); and a lookup that finds a peer. Each call meets its caller
+conditions and the mirror accepts it, consuming exactly those records.
+Everything here is about the entry and final states of the four calls
+(`Ran` gives an actual history between them and says nothing of its
+interior), so it follows from the headline's steps at this `fetch`. -/
+def Executed (fetch : Int64 → Option Decoded) (L : Layout) (A : Allocator) : Prop :=
+  ∃ (w0 w1 w2 w3 w4 : World) (d0 d3 : Device) (c1 c2 c3 c4 : Context)
     (s1 t1 s2 t2 s3 t3 s4 t4 : MachineState) (h1 h2 h3 h4 : List MachineState)
     (k1 n1 p1 k2 n2 p2 k3 n3 p3 key pointer : Nat) (found : PeerId) (ra : UInt64)
     (stream : List HiddenRecord),
-    Premises fetch L A ∧ CallbacksFromImage fetch ∧
     w0.wg.dev = some d0 ∧ armed w0 = true ∧
     w0.ambient.hidden = some ([outcome 77 true, outcome 78 true, outcome 79 true,
       outcome 78 true, outcome 79 false] ++ stream) ∧
@@ -67,11 +65,54 @@ def Witness : Prop :=
     HeapSame L t3 s4 ∧ lookupReady L c4 s4 4 key ra = .ok () ∧ w3.wg.dev = some d3 ∧
     (Source.lookup d3.peerAllowedips.root4 32 key).run w3 = .ok (some found, w4) ∧
     Trie.address L.peers (some found) = .ok pointer ∧ Ran fetch s4 t4 ra h4 ∧
-    0 < A.depth ∧ c2.Needed ∧
-    ∃ (enter leave : MachineState) (back : UInt64), enter ∈ h2 ∧ leave ∈ h2 ∧
-      enter.pc = allocEntry ∧ Returned enter leave back ∧
-      (∃ a, Scratch enter A.depth a ∧ enter.data.dmem.get? a ≠ leave.data.dmem.get? a) ∧
-      (∃ a, c2.writes a ∧ enter.data.dmem.get? a ≠ leave.data.dmem.get? a)
+    c2.Needed
+
+/-- ACTIVE SERVICE (the service half of the witness, revision 3). The code
+at `allocEntry`, taken on its own: its stack scratch is nonempty, and from
+some entry state that the contract's `alloc` clause admits (every
+hypothesis of that clause, with the coverage buffer in use and a success
+pending) an actual execution returns having changed a byte of its scratch
+and a byte of the coverage buffer. The allocator is idle in that state, so
+`Idle` holds of an actual memory. Revision 2 asked for these two changes
+between a service entry and its return inside the second insertion's
+history; the headline's steps conclude about final states only, so that
+could not be derived from them. -/
+def ServiceActive (fetch : Int64 → Option Decoded) (L : Layout) (A : Allocator) : Prop :=
+  0 < A.depth ∧
+  ∃ (c : Context) (s t : MachineState) (ra : UInt64) (live : List Nat) (record : HiddenRecord)
+    (stream : List HiddenRecord) (history : List MachineState),
+    s.pc = allocEntry ∧ EntryFrame s ra ∧ ServiceReady L A c s ∧
+    s.data.regs.rdi.toNat = L.cache ∧ s.data.regs.get (.low .rsi .W32) = 0xdc0#32 ∧
+    (ra.toNat, record.site) ∈ allocSites ∧ A.Idle s.data.dmem live (record :: stream) ∧
+    c.Needed ∧ record.bytes.head? = some 1 ∧
+    Ran fetch s t ra history ∧
+    (∃ a, Scratch s A.depth a ∧ s.data.dmem.get? a ≠ t.data.dmem.get? a) ∧
+    (∃ a, c.writes a ∧ s.data.dmem.get? a ≠ t.data.dmem.get? a)
+
+/-- WITNESS (revision 3). One `fetch`, layout and allocator meet every
+premise, with the callbacks the image's own code (`CallbacksFromImage`: only
+the code at `allocEntry` and `freeEntry` may be a stub), run the four calls
+of `Executed`, and have the active service of `ServiceActive`. The service
+will be a stub and is to be called one.
+
+What each conjunct rules out. `Premises`: premises that nothing meets.
+`CallbacksFromImage`: a witness whose coverage and BH-enable callbacks are
+stubs. `Executed`: an allocator that is never idle (it is idle at an actual
+empty table, with five answers pending); premises met only where no call
+can start or finish (each kind of call, the two-allocation insertion and
+the rollback included, starts from the caller's conditions and returns);
+a mirror that accepts none of them; a run with the coverage buffer unused.
+`ServiceActive`: a contract that only a service with no stack and no
+record could meet (this one, at the same addresses and under the same
+contract, uses its scratch and writes the buffer).
+
+What it no longer rules out, against revision 2: that the service is
+active only at entry states no insertion reaches. Revision 2 placed the
+two changed bytes inside the second insertion; here they are shown at one
+admissible entry state, which need not be one of `Executed`'s. -/
+def Witness : Prop :=
+  ∃ (fetch : Int64 → Option Decoded) (L : Layout) (A : Allocator),
+    Premises fetch L A ∧ CallbacksFromImage fetch ∧ Executed fetch L A ∧ ServiceActive fetch L A
 
 /-- The caller's conditions for a lookup of `key` in any state that agrees
 with `t` on the heap. -/
@@ -133,19 +174,21 @@ def FailedInsertInvisible : Prop :=
 
 /-- WHAT IS SIGNED: the headline together with the evidence against vacuity
 it relies on. The exclusions follow from `Headline` and facts about the
-mirror; the witness is independent of it.
+mirror; of the witness, `Executed` follows from the headline's steps at one
+`fetch` that meets the premises, and `ServiceActive` is independent of it.
 
 What it establishes, in the words its summary and register entry use: the
 compiled `wg_allowedips_insert_v4`, `_v6`, `add.isra.0`, `lookup`,
 `common_bits` and `wg_peer_get_maybe_zero` of the s5 image return what the
 mirror returns along any sequence of insertions and lookups from an empty
-table, **given any code at the two service addresses that meets the stated
+table, with the caller's references on registered peers taken and dropped
+between them, **given any code at the two service addresses that meets the stated
 contract; the image's allocator is not shown to, and under this semantic
 base cannot be**. About how the compiled code uses that service it
 establishes that the code calls it only with the cache and the flags the
 contract names and from states the contract covers; relies on nothing about
-a returned object but that it is zeroed, aligned, inside the arena and apart
-from the nodes handed out; never depends on the service's stack scratch, on
+a returned object but that it is zeroed, aligned, inside the arena, ending
+below 2^64 and apart from the nodes handed out; never depends on the service's stack scratch, on
 the caller-saved registers it returns, on free arena bytes or on the bytes
 of a released object; and releases exactly the node it allocated, once, on
 the one failing path. -/
```
