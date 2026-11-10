import StatementC1Contracts
import PairAllowedipsLookupAdequacy

/-! Result C1, final statement (no theorem, no proof): the headline for the
compiled allowed-IPs insertion of the pinned s5 image, as `def … : Prop`.

`Headline` keeps the memory relation internal (an existentially quantified
invariant): what a reader takes away is machine-observable, the 32-bit
result of every insertion and the peer pointer returned by every later
lookup, along any call sequence that starts at a physically empty table,
with the caller's references on registered peers taken and dropped between
the calls (revision 3).
`HeadlineExplicit` is the alternative with the landed relation in its
conclusion; it implies `Headline`, and it is what a proof would exhibit. -/
namespace Binary.Statements.C1
open Leanux Leanux.WG Binary.Pair Binary.Pair.Allowedips Binary.TrustBase
open Binary.CommonBitsCoverage
local instance : Labels := Image.linkedLabels

/-! ## Premises about the code and its services -/

/-- Everything assumed about `fetch`: it returns the committed decoded
instructions of both wrappers, `add.isra.0`, `lookup`, `common_bits` and
`wg_peer_get_maybe_zero`; the coverage and BH-enable callbacks meet their
landed contracts; whatever it holds at `allocEntry` and `freeEntry` meets
the new contract. Nothing requires that to be the image's allocator, and
under the pinned semantics the image's allocator cannot meet it. -/
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

/-! ## What the caller of each function must supply (executable) -/

/-- Stack bytes below the return word that a call may write: the wrapper's
and `add`'s frames and their callbacks' return words (insertion; 200 is the
deepest write the executed tests saw, on the IPv6 wrapper), or `lookup`'s
with its two callees (the landed 144), before any service scratch. -/
def insertWindow : Nat := 200
def lookupWindow : Nat := 144

/-- The caller's own memory that a call reads or writes: its stack window
with the return word, the address bytes, and for an insertion the
`node_cache` word. -/
def callerSpans (s : MachineState) (window : Nat) (query : Pair.Span) (cache : Bool) : List Pair.Span :=
  [((s.data.regs.rsp.toBitVec - .ofNat 64 window).toNat, window+8), query] ++
    (if cache then [(cacheWord,8)] else [])

/-- Kernel ABI at the call, mapped stack, readable coverage state, and
separation: the heap (table words, peer words, arena) is apart from the
caller's spans and from every coverage and per-CPU word the callbacks touch;
the coverage buffer is apart from the stack, the address bytes and the
metadata; for an insertion (`cache`) the buffer has room for a record when
in use and the direction flag is clear, which the services need; the
address bytes are apart from the window below the return word (they may
overlap the return word itself, which no callee writes). `bh` adds what `lookup`'s BH section needs (the second coverage
phase, no hard interrupt count, no pending softirq). -/
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

/-- A call of `wg_allowedips_insert_v4/_v6(table, ip, cidr, peer, lock)`:
the wrapper's entry, the table, the address bytes in network order, the
8-bit prefix length, a non-NULL registered peer, the `node_cache` word, and
room below the stack for the allocator's scratch. Revision 4: the stack
window below the return word is apart from every peer as a whole object
(`frameReady` keeps it apart from the heap, which holds only a peer's
reference count and list head; the landed `NodeInit.boundary` needs `add`'s
stack bytes apart from the whole 1520-byte object). -/
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

/-- A call of the compiled `lookup(root, bits, ip)` as its two callers make
it: the root pointer is the word in the table's slot for the family. -/
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

/-! ## The starting point (executable, machine-level) -/

/-- The mirror consumes one record per `kmem_cache_zalloc` in `add`. -/
def armed (w : World) : Bool :=
  ["allocNode190","allocNode205","allocNode234"].all w.ambient.allocArmed.contains

/-- A physically empty table beside an empty mirror table: both root words
NULL, the sequence word equal to the mirror's, every peer's list head
pointing at itself and its reference count equal to the mirror's; the
layout's peers are the mirror's, and the table and peer objects are
aligned, non-NULL, pairwise separate and apart from the arena. -/
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

/-! ## The headline -/

/-- The invariant starts at every physically empty table whose allocator is
idle with nothing handed out and whose answers are the mirror's pending
records (allocation records for these three sites only). -/
def Initial (L : Layout) (A : Allocator) (Inv : World → Mem 64 → Prop) : Prop :=
  ∀ w d m stream, w.wg.dev = some d → armed w = true → w.ambient.hidden = some stream →
    (∀ record ∈ stream, record.site ∈ allocSites.map (·.2)) →
    emptyTable L m d = .ok () → A.Idle m [] stream → Inv w m

/-- The invariant reads only the heap: the caller may change anything else
between calls. -/
def Framed (L : Layout) (Inv : World → Mem 64 → Prop) : Prop :=
  ∀ w m m', Inv w m → (∀ a, L.Heap a → m.get? a = m'.get? a) → Inv w m'

/-- Memory `m'` is memory `m` with peer `pid`'s four-byte reference count
changed from `before` to `after`: both are readable, and every other heap
byte is the same. Bytes outside the heap are unconstrained, as in `Framed`. -/
def CountMoved (L : Layout) (pid : PeerId) (before after : Nat) (m m' : Mem 64) : Prop :=
  ∃ peer, Trie.address L.peers (some pid) = .ok peer ∧
    readNat ⟨{dmem := m},0⟩ (peer+Root.nodeOffsets.peerRefcount) 4 = .ok before ∧
    readNat ⟨{dmem := m'},0⟩ (peer+Root.nodeOffsets.peerRefcount) 4 = .ok after ∧
    ∀ a, L.Heap a → ¬InRange (.ofNat 64 (peer+Root.nodeOffsets.peerRefcount)) 4 a → m.get? a = m'.get? a

/-- Revisions 3 and 4. The invariant survives the caller taking or dropping
one reference on a registered peer between calls: the peer's count word goes
up by one together with the mirror's `peerGetMaybeZero` on that peer
returning the peer, or down by one, from a count above one, together with
the mirror's `peerPut` on it (the last reference is not dropped here: that
is the peer's removal). No other heap byte changes and no other mirror
operation runs. This is what a `wg set` over existing peers does between
the insertions for one peer and those for the next: `set_peer` drops its
reference on the first (`wg_peer_put`, netlink.c:486) and takes one on the
second through `wg_pubkey_hashtable_lookup`, that is
`wg_peer_get_maybe_zero` (netlink.c:386, peerlookup.c:68). `wg_peer_get` is
called only on a peer just created (netlink.c:421), which is outside. -/
def Referenced (L : Layout) (Inv : World → Mem 64 → Prop) : Prop :=
  ∀ (w w' : World) (m m' : Mem 64) (pid : PeerId) (count : Nat), Inv w m →
    ((liftWG (WG.peerGetMaybeZero (some pid))).run w = .ok (some pid, w') ∧
      CountMoved L pid count (count+1) m m') ∨
    ((liftWG (WG.peerPut (some pid))).run w = .ok ((), w') ∧ 1 < count ∧
      CountMoved L pid count (count-1) m m') →
    Inv w' m'

/-- The table's sequence word after the call is the word before plus one,
modulo 2^64: what a wrapper does besides calling `add`. -/
def SeqAdvanced (L : Layout) (s t : MachineState) : Prop :=
  ∃ before, readNat s (L.table+AllowedipsMutationLayout.seq) 8 = .ok before ∧
    readNat t (L.table+AllowedipsMutationLayout.seq) 8 = .ok ((before+1) % 2^64)

def InsertWrites (L : Layout) (A : Allocator) (c : Context) (s : MachineState) (a : BitVec 64) : Prop :=
  Scratch s (insertWindow + A.depth) a ∨ c.writes a ∨ L.Heap a

def LookupWrites (L : Layout) (c : Context) (s : MachineState) (a : BitVec 64) : Prop :=
  AllowedipsEntry.TotalWrites s c.coverage c.preempt a ∨ L.Heap a

/-- One insertion. From any state satisfying the invariant and the caller's
conditions, and for any accepted run of the mirror's `Leanux.WG.insert` on
the same arguments, the machine reaches the caller's return address with
the mirror's result in `eax`, the table's sequence word advanced by one,
the invariant re-established for the mirror's final world, and memory unchanged outside the stack window, the coverage
buffer and the heap. Every path of `add` is covered by the mirror run's
own branching: the `-EINVAL` exit for an over-long prefix, the empty root,
exact reassignment, child attachment, covering and intermediate nodes at
the root and below a parent, the three allocation failures and the
rollback. The NULL-peer `-EINVAL` exit is outside it: the caller's
conditions demand a registered, non-NULL peer, as the mirror's `insert`
does by taking a peer identity. -/
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

/-- One lookup, the consumer that makes the invariant observable. For any
accepted run of the mirror's lookup from the mirror's root, the machine
returns in `rax` the address the layout gives the selected peer, or NULL. -/
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

/-- THE HEADLINE. Under the premises there is an invariant, holding
at every empty table, insensitive to memory outside the heap, surviving the
caller's reference on a peer being taken or dropped between calls
(revision 3), preserved by every insertion and every lookup, under which
each returns what the mirror returns. The relation between memory and the mirror is not part of the
claim; a proof must exhibit one. -/
def Headline : Prop :=
  ∀ (fetch : Int64 → Option Decoded) (L : Layout) (A : Allocator), Premises fetch L A →
    ∃ Inv : World → Mem 64 → Prop,
      Initial L A Inv ∧ Framed L Inv ∧ Referenced L Inv ∧
      InsertStep fetch L A Inv ∧ LookupStep fetch L Inv

/-! ## The alternative: the landed relation in the conclusion -/

/-- The landed executable relation and structural check (`assertAt`), for
names whose table and peers are the layout's and whose node objects are the
ones the allocator has handed out, with the allocator's answers tied to the
mirror's pending records. -/
def Related (L : Layout) (A : Allocator) (w : World) (m : Mem 64) : Prop :=
  ∃ (names : Allowedips.Names) (stream : List HiddenRecord),
    names.table = L.table ∧ names.trie.peers = L.peers ∧
    assertAt names Root.nodeOffsets m w = .ok () ∧
    armed w = true ∧ w.ambient.hidden = some stream ∧
    (∀ record ∈ stream, record.site ∈ allocSites.map (·.2)) ∧
    spansApart ([(L.table,AllowedipsMutationLayout.tableSize)] ++
      L.peers.map fun (_,a) => (a,Layouts.peerSize)) L.arena = true ∧
    (∀ node ∈ names.trie.nodes, ∃ span ∈ L.arena, span.1 ≤ node.2 ∧ node.2+nodeSize ≤ span.1+span.2) ∧
    A.Idle m (names.trie.nodes.map (·.2)) stream

/-- The same five clauses with the invariant fixed to `Related`. It implies
`Headline`; it additionally tells a reader what memory looks like after
each call, in terms nothing but tests and reading pin down. -/
def HeadlineExplicit : Prop :=
  ∀ (fetch : Int64 → Option Decoded) (L : Layout) (A : Allocator), Premises fetch L A →
    Initial L A (Related L A) ∧ Framed L (Related L A) ∧ Referenced L (Related L A) ∧
    InsertStep fetch L A (Related L A) ∧ LookupStep fetch L (Related L A)

end Binary.Statements.C1
