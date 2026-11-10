import PairAllowedipsMutation
import AllowedipsRootRecord

/-! Result C1, final statement (no theorem, no proof): the layout a reader is told
about and the allocator/free contract. Everything here is a premise of the
headline in `StatementC1Headline`: nothing in a proof polices it. -/
namespace Binary.Statements.C1
open Leanux Leanux.WG Binary.Pair Binary.Pair.Allowedips Binary.TrustBase
local instance : Labels := Image.linkedLabels

/-- Where one device's allowed-IPs data lives. `arena` is the allocator's
territory: slab metadata and every `allowedips_node` object, free or handed
out, and anything else `kmem_cache_alloc`/`kmem_cache_free` may touch. -/
structure Layout where
  table : Nat
  peers : List (PeerId × Nat)
  arena : List Pair.Span
  cache : Nat

/-- The words of the table and of each peer that the subsystem reads or
writes, at the committed s5 offsets (root4, root6, seq; refcount, list head). -/
def Layout.fixed (L : Layout) : List Pair.Span :=
  tableFields.map (fun (offset,size) => (L.table+offset,size)) ++
  L.peers.flatMap (fun (_,a) => (peerFields Allowedips.Root.nodeOffsets).map (fun (offset,size) => (a+offset,size)))

def Layout.heap (L : Layout) : List Pair.Span := L.fixed ++ L.arena

def Layout.Arena (L : Layout) (a : BitVec 64) : Prop := ∃ span ∈ L.arena, span.contains a
def Layout.Heap (L : Layout) (a : BitVec 64) : Prop := ∃ span ∈ L.heap, span.contains a

/-- The s5 image's service entries and the three allocation return sites in
`add.isra.0` with the mirror's record site for each (allowedips.c:205, :234,
:190), and the one release return site (:237). These are addresses: the
premises say nothing about which code `fetch` holds there. -/
def allocEntry : Int64 := .ofNat 0xffffffff81196d20   -- where the image has kmem_cache_alloc_noprof
def freeEntry : Int64 := .ofNat 0xffffffff81199b10    -- where the image has kmem_cache_free
def cacheWord : Nat := 0xffffffff81fdbe60             -- &node_cache
def allocSites : List (Nat × Nat) :=
  [(0xffffffff813a0d04,78),(0xffffffff813a0e52,79),(0xffffffff813a0ff2,77)]
def freeSite : Nat := 0xffffffff813a1252
def nodeSize : Nat := 72

/-- The allocator as the caller sees it. `Idle m live stream` is abstract
and never unfolded: "in memory `m` the node cache is consistent, the objects
at `live` are handed out, and its next answers are `stream`" (the mirror's
pending allocation records). `depth` bounds the stack the services use. -/
structure Allocator where
  Idle : Mem 64 → List Nat → List HiddenRecord → Prop
  depth : Nat

def Scratch (s : MachineState) (depth : Nat) : BitVec 64 → Prop :=
  InRange (s.data.regs.rsp.toBitVec - .ofNat 64 depth) depth

/-- The bytes of the objects in `kept`: nodes handed out that a call must
leave alone. -/
def Kept (kept : List Nat) (a : BitVec 64) : Prop :=
  ∃ object ∈ kept, InRange (.ofNat 64 object) nodeSize a

/-- A service may write its stack scratch, the arena outside the objects in
`kept`, and the coverage buffer (in the s5 image the allocator carries the
oracle build's recording hook, which appends to the calling task's coverage
area). Revision 2: live nodes are no longer in the write set. -/
def ServiceWrites (L : Layout) (A : Allocator) (c : CommonBitsCoverage.Context)
    (s : MachineState) (kept : List Nat) (a : BitVec 64) : Prop :=
  Scratch s A.depth a ∨ (L.Arena a ∧ ¬Kept kept a) ∨ c.writes a

/-- Where the service's bytes are, relative to the coverage context it is
called under (revision 3): its stack (the scratch and the return word), the
arena and the bytes the coverage context reads are pairwise apart, and the
coverage buffer is apart from the coverage metadata and the preemption
count. An insertion's caller conditions give this at every service call
(`frameReady`'s separations); without it a context could place its mode
word on the allocator's own state, and no allocator that changes a word of
the arena would meet the contract. -/
structure Separated (L : Layout) (A : Allocator) (c : CommonBitsCoverage.Context) (s : MachineState) : Prop where
  stackArena : ∀ a, Scratch s A.depth a ∨ InRange s.data.regs.rsp.toBitVec 8 a → ¬L.Arena a
  stackCoverage : ∀ a, Scratch s A.depth a ∨ InRange s.data.regs.rsp.toBitVec 8 a → ¬c.bytes a
  coverageArena : ∀ a, c.bytes a → ¬L.Arena a
  bufferMetadata : ∀ a, c.writes a → ¬c.metadataBytes a ∧ ¬InRange preemptCountAddress 4 a

/-- What a service may assume at its entry besides its arguments, in the form
of the landed `RandomReady`: valid coverage state with room for a record
when the buffer is in use, the direction flag clear, `depth` mapped bytes of
stack below the return word (revision 2), and the separation of its stack,
the arena and the coverage bytes (revision 3). -/
structure ServiceReady (L : Layout) (A : Allocator) (c : CommonBitsCoverage.Context) (s : MachineState) : Prop where
  coverage : c.At s.data.dmem
  capacity : c.Needed → 0 < c.coverage.capacity.toNat
  forward : s.data.system.bits[10] = false
  stackMapped : ∀ i < A.depth,
    (s.data.dmem.get? (s.data.regs.rsp.toBitVec - .ofNat 64 A.depth + .ofNat 64 i)).isSome = true
  separated : Separated L A c s

/-- What one `kmem_cache_zalloc(node_cache, GFP_KERNEL)` leaves behind, by the
recorded outcome byte: NULL and nothing handed out, or an aligned, zeroed
72-byte object inside the arena that overlaps no object already handed out
and ends strictly below 2^64 (revision 3: the bound the landed
interpretation check `Trie.validate` demands of every node). -/
def AllocResult (L : Layout) (A : Allocator) (live : List Nat) (record : HiddenRecord)
    (stream : List HiddenRecord) (t : MachineState) : Prop :=
  let a := t.data.regs.rax.toNat
  (record.bytes.head? = some 0 → a = 0 ∧ A.Idle t.data.dmem live stream) ∧
  (record.bytes.head? = some 1 →
    a ≠ 0 ∧ a % 8 = 0 ∧ a + nodeSize < 2^64 ∧
    (∃ span ∈ L.arena, span.1 ≤ a ∧ a+nodeSize ≤ span.1+span.2) ∧
    (∀ other ∈ live, disjointRanges a nodeSize other nodeSize = true) ∧
    readNat t a nodeSize = .ok 0 ∧ A.Idle t.data.dmem (live ++ [a]) stream)

/-- NEW TRUST SURFACE: the contract for whatever code `fetch` holds at
`allocEntry` and `freeEntry`, assumed, not proved. Both services return to
their caller with the callee-saved registers kept, change memory only in
their stack scratch, the coverage buffer and the arena outside the nodes
that stay handed out, and leave the coverage state valid. -/
structure AllocatorContract (fetch : Int64 → Option Decoded) (L : Layout) (A : Allocator) : Prop where
  /-- The allocator's state does not depend on bytes outside the arena, nor
  on the contents of objects it has handed out. -/
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

end Binary.Statements.C1
