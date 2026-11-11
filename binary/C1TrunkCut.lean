import C1TrunkNode
import AllowedipsNodeBoundaryFields
/-! Result C1, package 2: the cut at `add+0x156`. From the stored result of
the allocation at :205 (non-NULL) through the callback at `+0x151` to the
landed `NodeInit.boundary`, with every field of `NodeCut` and `CutExtra`.

STATEMENT FINDING (see `StackOffPeers`). `NodeInit.boundary` checks that the
three stack bytes the initialization writes (`rsp+36`, `rsp+43`, `rsp+44`)
are apart from every peer OBJECT (`allocations names o`, 1520 bytes each).
The caller's conditions (`frameReady`'s `c1.heap-separation`) keep the stack
window apart from `L.heap`, which holds only the peer's WORDS (the reference
count and the list head: `Layout.fixed`). A stack window lying inside a peer
object between those words meets every stated condition, and the landed
boundary then fails. The two `example`s below execute both checks on such a
layout. The cut is proved here from `StackOffPeers`, stated as an explicit
hypothesis; nothing is restated. -/
namespace C1Trunk
open Binary Binary.Pair Binary.Pair.Allowedips Binary.AllowedipsMutationImage
open Binary.TrustBase Binary.CommonBitsCoverage Binary.Instrumentation
open Binary.Statements.C1 Binary.Statements.C1.Proof Leanux Leanux.WG
local instance : Labels := Image.linkedLabels

/-- NOT DERIVABLE FROM THE STATEMENT'S TEXT (as it stood at revision 3) (a statement finding of this
package, beside `NodeBelowTop`). The insertion's stack window is apart from
every peer object. `insertReady` keeps the window apart from the peer's
reference count and list head only. -/
def StackOffPeers : Prop :=
  ∀ (L : Statements.C1.Layout) (A : Allocator) (c : Context) (s : MachineState)
    (family key cidr pid : Nat) (ra : UInt64),
    insertReady L A c s family key cidr pid ra = .ok () →
    ∀ peer ∈ L.peers, ∀ x,
      InRange (s.data.regs.rsp.toBitVec - .ofNat 64 (insertWindow + A.depth)) (insertWindow + A.depth) x →
      ¬Pair.Span.contains (peer.2,Layouts.peerSize) x

/-- Evidence, executed: one peer at 0x10000, a stack pointer 600 bytes into
it, a window of 208 bytes below it with the return word. The stated
separation of the heap from the window holds. -/
example : spansApart (Statements.C1.Layout.heap ⟨0x1000,[(1,0x10000)],[(0x20000,0x1000)],0⟩)
    [(0x10000+600-208,216)] = true := by decide

/-- ... and the landed boundary's separation of `add`'s stack bytes (the
IPv4 frame: `rsp = entry - 144`, bytes 36, 43, 44) from the peer object fails. -/
example : spansApart [(0x10000+600-144+36,1),(0x10000+600-144+43,1),(0x10000+600-144+44,1)]
    [(0x10000,Layouts.peerSize)] = false := by decide

/-- The converse of the landed `NodeInit.boundary_fields`. -/
theorem node_boundary_of_fields {names o world machine key cidr pid base}
    (f : NodeInit.BoundaryFields names o world machine key cidr pid base) :
    NodeInit.boundary names o world machine key cidr pid = .ok base := by
  have family : (machine.data.regs.rbp.toNat==32 || machine.data.regs.rbp.toNat==128) = true := by
    simpa only [Bool.or_eq_true,beq_iff_eq] using f.family
  have m36 := f.stackMapped 36 (by simp)
  have m43 := f.stackMapped 43 (by simp)
  have m44 := f.stackMapped 44 (by simp)
  have apart := f.stackApart
  simp only [List.cons_append, List.nil_append] at apart
  unfold NodeInit.boundary
  simp [f.asserted,f.baseRead,f.pc,family,f.owner,f.cidrRead,f.cidrBound,f.original,f.bits,f.allocated,
    f.zero,f.query,m36,m43,m44,f.queryApart,apart,require,bind,Except.bind,Except.mapError,
    pure,Except.pure]

/-- The other direction of the finding: whatever state a trunk delivers with
`NodeCut`, the landed boundary there says the three stack bytes are apart
from every peer object. So `TrunkToNode` as stated implies this separation at
its cut state, for every state the stated conditions admit. -/
theorem cut_stack_off_peers {fetch : Int64 → Option Decoded} {L : Statements.C1.Layout} {A : Allocator}
    {c : Context} {s : MachineState} {ra : UInt64} {w : World} {d : Device} {key cidr pid : Nat}
    {stream : List HiddenRecord} {placed : Option NodeId} {names : Allowedips.Names} {base : Nat}
    {e : MachineState}
    (cut : NodeCut fetch L A c s ra w d key cidr pid stream placed names base e) :
    ∀ peer ∈ L.peers, ∀ offset ∈ [36,43,44], ∀ x,
      Pair.Span.contains (e.data.regs.rsp.toNat+offset,1) x →
      ¬Pair.Span.contains (peer.2,Layouts.peerSize) x := by
  intro peer member offset which x inside covered
  have fields := NodeInit.boundary_fields cut.boundary
  have atStack : (e.data.regs.rsp.toNat+offset,1) ∈
      [(e.data.regs.rsp.toNat+36,1),(e.data.regs.rsp.toNat+43,1),(e.data.regs.rsp.toNat+44,1)] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at which
    rcases which with rfl | rfl | rfl <;> simp
  have isPeer : (peer.2,Layouts.peerSize) ∈
      [(base,72),(names.table,24)] ++ allocations names Root.nodeOffsets := by
    refine List.mem_append_right _ (List.mem_append_right _ (List.mem_map.mpr ⟨peer,?_,rfl⟩))
    rw [cut.peers]
    exact member
  exact spansApart_sound fields.stackApart atStack isPeer inside covered

section
variable {fetch : Int64 → Option Decoded} {L : Statements.C1.Layout} {A : Allocator} {c : Context}
  {s : MachineState} {w : World} {v4 : Bool} {key cidr pid : Nat} {ra : UInt64}
  {names : Allowedips.Names} {stream : List HiddenRecord} {d : Device} {seq : BitVec 64}
  {a : MachineData} {bits : Nat} {placed : Option NodeId}

/-- The sequence word advanced, at a state after the service. -/
theorem Mid.seqAdvanced (trunk : Trunk L A c s w v4 key cidr pid ra names stream d seq a)
    {word : UInt64} {m : MachineData} (mid : Mid L A c s v4 names d seq a bits placed word m) (pc : Int64) :
    SeqAdvanced L s ⟨m,pc⟩ := by
  have address := seq_address s.data.regs.rdi L.table trunk.tableReg
  refine ⟨seq.toNat,readNat_of_load ?_,readNat_of_load ?_⟩
  · rw [← address]
    exact trunk.caller.seqWord
  · rw [mid.seqWord]
    congr 2
    rw [BitVec.toNat_add]
    show (1 + seq.toNat) % 2^64 = (seq.toNat + 1) % 2^64
    rw [Nat.add_comm]

/-- The landed boundary of the node initialization holds at +0x156. -/
theorem node_boundary (trunk : Trunk L A c s w v4 key cidr pid ra names stream d seq a)
    (peersOff : ∀ peer ∈ L.peers, ∀ x,
      InRange (s.data.regs.rsp.toBitVec - .ofNat 64 (insertWindow + A.depth)) (insertWindow + A.depth) x →
      ¬Pair.Span.contains (peer.2,Layouts.peerSize) x)
    (bound : cidr ≤ (if v4 then 32 else 128)) {word : UInt64} {v : MachineState}
    (pcV : v.pc = Add.entry+0x156)
    (mid : Mid L A c s v4 names d seq a (if v4 then 32 else 128) placed word v.data)
    (object : Object L names word.toNat) (zero : readNat v word.toNat 72 = .ok 0) :
    NodeInit.boundary names Root.nodeOffsets (bumped w d) v key cidr pid = .ok word.toNat := by
  have fs := frameSize_range v4
  have wide := window_wide A
  have room' : insertWindow + A.depth ≤ s.data.regs.rsp.toBitVec.toNat := trunk.sep.room
  have top' : s.data.regs.rsp.toBitVec.toNat + 8 ≤ 2^64 := trunk.sep.top
  have vspBV := mid.stackAt trunk
  have vspNat : v.data.regs.rsp.toNat = s.data.regs.rsp.toBitVec.toNat - (frameSize v4 + 96) := by
    show v.data.regs.rsp.toBitVec.toNat = _
    rw [vspBV, toNat_sub_ofNat _ _ (by omega)]
  have nq : 0 < (if v4 then 32 else 128)/8 ∧ (if v4 then 32 else 128)/8 ≤ (if v4 then 36 else 48) := by
    cases v4 <;> decide
  have kq : 36 ≤ (if v4 then 36 else 48) ∧ (if v4 then 36 else 48) + 8 ≤ frameSize v4 := by
    cases v4 <;> decide
  have r13BV : v.data.regs.r13.toBitVec = s.data.regs.rsp.toBitVec - .ofNat 64 (if v4 then 36 else 48) := by
    rw [mid.r13, trunk.atAdd.query]
    cases v4 <;> rfl
  have r13Nat : v.data.regs.r13.toNat = s.data.regs.rsp.toBitVec.toNat - (if v4 then 36 else 48) := by
    show v.data.regs.r13.toBitVec.toNat = _
    rw [r13BV, toNat_sub_ofNat _ _ (by omega)]
  have aboveLoad (k m : Nat) (hk : k + 8 ≤ frameSize v4) (hm : m ≤ k) :
      v.data.dmem.loadInt (s.data.regs.rsp.toBitVec - .ofNat 64 k) m =
        a.dmem.loadInt (s.data.regs.rsp.toBitVec - .ofNat 64 k) m := by
    refine (mid.frame.loadInt _ m (fun i hi h => ?_)).symm
    have inWindow : InRange (s.data.regs.rsp.toBitVec - .ofNat 64 (insertWindow + A.depth))
        (insertWindow + A.depth + 8) (s.data.regs.rsp.toBitVec - .ofNat 64 k + .ofNat 64 i) :=
      below_sub _ k m _ _ (by omega) (by omega) _ ⟨i,hi,rfl⟩
    rcases h with h | h | h
    · exact below_under _ k m (insertWindow + A.depth) _ (by omega) (by omega) (by omega) _ ⟨i,hi,rfl⟩ h
    · exact trunk.sep.bytesStack _ (writes_bytes h) inWindow
    · exact trunk.sep.heapStack _ h inWindow
  have argCidr : (a.regs.get (.low .rcx .W32)).toNat = cidr := trunk.atAdd.cidr.trans trunk.cidr
  have valid := related_valid trunk.relatedA
  obtain ⟨tableTop,_⟩ := Root.table_valid_geometry valid
  have trieValid : Trie.validate names.trie Root.nodeOffsets = .ok () := by
    unfold validate at valid
    obtain ⟨_,trieValid,_⟩ := bind_ok valid
    exact trieValid
  have ranges := trie_validate_ranges trieValid
  -- the stack bytes, as bytes of the insertion's window
  have stackByte (k : Nat) (hk : k < 48) (x : BitVec 64)
      (inside : Pair.Span.contains (v.data.regs.rsp.toNat+k,1) x) :
      InRange (s.data.regs.rsp.toBitVec - .ofNat 64 (insertWindow + A.depth)) (insertWindow + A.depth) x := by
    have inside' : InRange (.ofNat 64 (v.data.regs.rsp.toNat+k)) 1 x := inside
    rw [BitVec.ofNat_add, Root.ofNat_uint64, vspBV, sub_add_ofNat _ _ k (by omega)] at inside'
    exact below_sub _ _ _ _ _ (by omega) (by omega) x inside'
  have windowTop (x : BitVec 64)
      (h : InRange (s.data.regs.rsp.toBitVec - .ofNat 64 (insertWindow + A.depth)) (insertWindow + A.depth) x) :
      InRange (s.data.regs.rsp.toBitVec - .ofNat 64 (insertWindow + A.depth)) (insertWindow + A.depth + 8) x :=
    range_mono _ _ _ (by omega) x h
  have heapOff (k : Nat) (hk : k < 48) (x : BitVec 64)
      (inside : Pair.Span.contains (v.data.regs.rsp.toNat+k,1) x) (heap : L.Heap x) : False :=
    trunk.sep.heapStack x heap (windowTop x (stackByte k hk x inside))
  -- the write spans of the root boundary at a machine whose rbx is the object: the same heap spans
  let fake : MachineData := {v.data with regs := {v.data.regs with rbx := word}}
  have spans := object.writeSpans trunk fake rfl
  have heapSpan (span : Pair.Span)
      (member : span = (word.toNat,72) ∨
        span ∈ (names.allocated word.toNat).trie.nodes.map (fun p => (p.2+56,16)) ∨
        span ∈ (names.allocated word.toNat).trie.peers.map (fun p => (p.2+1096,16))) :
      (span.1 + span.2 ≤ 2^64 ∧ 0 < span.2) ∧ ∀ x, span.contains x → L.Heap x := by
    have inRoot : span ∈ Root.writeSpans (names.allocated word.toNat) fake := by
      simp only [Root.writeSpans, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      rcases member with rfl | node | peer
      · exact .inl (.inl (.inl rfl))
      · exact .inl (.inr node)
      · exact .inr peer
    exact ⟨(spans span inRoot).1,(spans span inRoot).2.1⟩
  apply node_boundary_of_fields
  refine {
    asserted := assertAt_of_related rfl mid.related mid.shape
    baseRead := ?_
    pc := pcV
    family := by rw [mid.rbp]; cases v4 <;> simp
    owner := by rw [mid.r14, trunk.atAdd.peer, trunk.peers]; exact trunk.peer
    cidrRead := ?_
    cidrBound := by rw [mid.rbp]; exact bound
    original := by rw [mid.r12, zext32_toNat]; exact argCidr
    bits := by rw [mid.r15, mid.rbp]
    allocated := object.valid
    zero := zero
    query := ?_
    stackMapped := ?_
    queryApart := ?_
    stackApart := ?_ }
  · apply readNat_of_load
    rw [Root.ofNat_uint64]
    exact mid.base
  · apply readNat_of_load
    show v.data.dmem.loadInt (.ofNat 64 (v.data.regs.rsp.toNat+16)) 4 = some (cidr : Int)
    rw [mid.stack, frame_address, mid.loads (8+16) 4 (by decide) (.inl (by decide))]
    have read := memory_cidr a
    rw [slot_base a 7 (by decide)] at read
    have same : a.regs.get (.low .rcx .W32) = BitVec.extractLsb' 0 32 a.regs.rcx.toBitVec := by
      simp [Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,BitVec.take,BitVec.drop]
    rw [← argCidr, same]
    exact read
  · rw [mid.rbp]
    have keyWord := trunk.atAdd.keyWord
    cases v4
    · simp only [Bool.false_eq_true, ↓reduceIte] at keyWord r13BV
      have rdHigh : readNat v v.data.regs.r13.toNat 8 = .ok (key/2^64) := by
        apply readNat_of_load
        rw [Root.ofNat_uint64, r13BV, aboveLoad 48 8 (by decide) (by decide)]
        exact keyWord.1
      have rdLow : readNat v (v.data.regs.r13.toNat+8) 8 = .ok (key % 2^64) := by
        apply readNat_of_load
        rw [BitVec.ofNat_add, Root.ofNat_uint64, r13BV, sub_add_ofNat _ 48 8 (by omega),
          show (48-8 : Nat) = 40 from rfl, aboveLoad 40 8 (by decide) (by decide)]
        exact keyWord.2
      simp [Placement.queryLocals, Placement.query6, rdHigh, rdLow, require, bind, Except.bind,
        Nat.div_add_mod']
    · simp only [↓reduceIte] at keyWord r13BV
      have rd : readNat v v.data.regs.r13.toNat 4 = .ok key := by
        apply readNat_of_load
        rw [Root.ofNat_uint64, r13BV, aboveLoad 36 4 (by decide) (by decide)]
        exact keyWord
      simp [Placement.queryLocals, Placement.query4, rd, require, bind, Except.bind]
  · intro offset member
    have small : offset < 48 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      omega
    rw [BitVec.ofNat_add, Root.ofNat_uint64, vspBV, sub_add_ofNat _ _ offset (by omega)]
    exact mid.mapped _ _ (trunk.caller.below.load _ 1 (by omega) (by omega))
  · apply apart_of_bytes
    · intro span member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      subst member
      rw [mid.rbp]
      exact ⟨by show v.data.regs.r13.toNat + _ ≤ 2^64; rw [r13Nat]; omega,nq.1⟩
    · intro span member
      simp only [NodeInit.writeSpans, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with ((rfl | rfl | rfl | rfl) | node) | peer
      · exact (heapSpan _ (.inl rfl)).1
      · exact ⟨by show v.data.regs.rsp.toNat + 36 + 1 ≤ 2^64; rw [vspNat]; omega,Nat.zero_lt_succ _⟩
      · exact ⟨by show v.data.regs.rsp.toNat + 43 + 1 ≤ 2^64; rw [vspNat]; omega,Nat.zero_lt_succ _⟩
      · exact ⟨by show v.data.regs.rsp.toNat + 44 + 1 ≤ 2^64; rw [vspNat]; omega,Nat.zero_lt_succ _⟩
      · exact (heapSpan _ (.inr (.inl node))).1
      · exact (heapSpan _ (.inr (.inr peer))).1
    · intro querySpan member writeSpan written x inside covered
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      subst member
      have inside' : InRange (.ofNat 64 v.data.regs.r13.toNat) (v.data.regs.rbp.toNat/8) x := inside
      rw [Root.ofNat_uint64, r13BV, mid.rbp] at inside'
      have inWindow : InRange (s.data.regs.rsp.toBitVec - .ofNat 64 (insertWindow + A.depth))
          (insertWindow + A.depth + 8) x := below_sub _ _ _ _ _ (by omega) (by omega) x inside'
      have atQuery := Span.location (span := (v.data.regs.r13.toNat,v.data.regs.rbp.toNat/8))
        (by show v.data.regs.r13.toNat + v.data.regs.rbp.toNat/8 ≤ 2^64; rw [r13Nat, mid.rbp]; omega) inside
      have queryLow : v.data.regs.rsp.toNat + 48 ≤ x.toNat := by
        have h := atQuery.1
        change v.data.regs.r13.toNat ≤ x.toNat at h
        rw [r13Nat] at h
        rw [vspNat]
        omega
      have stackCase (k : Nat) (hk : k < 48) (covered : Pair.Span.contains (v.data.regs.rsp.toNat+k,1) x) :
          False := by
        have h := (Span.location (span := (v.data.regs.rsp.toNat+k,1))
          (by show v.data.regs.rsp.toNat + k + 1 ≤ 2^64; rw [vspNat]; omega) covered).2
        change x.toNat < v.data.regs.rsp.toNat + k + 1 at h
        omega
      simp only [NodeInit.writeSpans, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at written
      rcases written with ((rfl | rfl | rfl | rfl) | node) | peer
      · exact trunk.sep.heapStack x ((heapSpan _ (.inl rfl)).2 x covered) inWindow
      · exact stackCase 36 (by omega) covered
      · exact stackCase 43 (by omega) covered
      · exact stackCase 44 (by omega) covered
      · exact trunk.sep.heapStack x ((heapSpan _ (.inr (.inl node))).2 x covered) inWindow
      · exact trunk.sep.heapStack x ((heapSpan _ (.inr (.inr peer))).2 x covered) inWindow
  · apply apart_of_bytes
    · intro span member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · exact ⟨by show v.data.regs.rsp.toNat + 36 + 1 ≤ 2^64; rw [vspNat]; omega,Nat.zero_lt_succ _⟩
      · exact ⟨by show v.data.regs.rsp.toNat + 43 + 1 ≤ 2^64; rw [vspNat]; omega,Nat.zero_lt_succ _⟩
      · exact ⟨by show v.data.regs.rsp.toNat + 44 + 1 ≤ 2^64; rw [vspNat]; omega,Nat.zero_lt_succ _⟩
    · intro span member
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with (rfl | rfl) | allocation
      · exact ⟨by have := object.top; show word.toNat + 72 ≤ 2^64; omega,Nat.zero_lt_succ _⟩
      · exact ⟨by show names.table + 24 ≤ 2^64; omega,Nat.zero_lt_succ _⟩
      · have bound := (ranges span allocation).2
        refine ⟨by omega,?_⟩
        simp only [allocations, List.mem_append, List.mem_map] at allocation
        rcases allocation with ⟨p,_,rfl⟩ | ⟨p,_,rfl⟩
        · show 0 < Root.nodeOffsets.nodeSize
          decide
        · show 0 < Layouts.peerSize
          decide
    · intro stackSpan member object' other x inside covered
      have inWindow : InRange (s.data.regs.rsp.toBitVec - .ofNat 64 (insertWindow + A.depth))
          (insertWindow + A.depth) x := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact stackByte 36 (by omega) x inside
        · exact stackByte 43 (by omega) x inside
        · exact stackByte 44 (by omega) x inside
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at other
      rcases other with (rfl | rfl) | allocation
      · exact trunk.sep.heapStack x ((heapSpan _ (.inl rfl)).2 x covered) (windowTop x inWindow)
      · apply trunk.sep.heapStack x _ (windowTop x inWindow)
        obtain ⟨i,hi,eq⟩ := covered
        have tableEq : names.table = L.table := trunk.table
        have shift (b : Nat) (hb : b ≤ i) : x = BitVec.ofNat 64 (L.table+b) + .ofNat 64 (i-b) := by
          rw [eq, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
          congr 1
          show names.table + i = L.table + b + (i - b)
          omega
        by_cases first : i < 8
        · exact ⟨(L.table+0,8),by simp [Layout.heap, Layout.fixed, tableFields,
            AllowedipsMutationLayout.root4],⟨i-0,by omega,shift 0 (by omega)⟩⟩
        · by_cases second : i < 16
          · exact ⟨(L.table+8,8),by simp [Layout.heap, Layout.fixed, tableFields,
              AllowedipsMutationLayout.root6],⟨i-8,by omega,shift 8 (by omega)⟩⟩
          · exact ⟨(L.table+16,8),by simp [Layout.heap, Layout.fixed, tableFields,
              AllowedipsMutationLayout.seq],⟨i-16,by omega,shift 16 (by omega)⟩⟩
      · simp only [allocations, List.mem_append, List.mem_map] at allocation
        rcases allocation with ⟨p,isNode,rfl⟩ | ⟨p,isPeer,rfl⟩
        · obtain ⟨home,isArena,low,high⟩ := trunk.inArena p isNode
          exact trunk.sep.heapStack x (arena_heap x ⟨home,isArena,
            span_within _ _ _ _ low (by unfold nodeSize at high; exact high) x covered⟩)
            (windowTop x inWindow)
        · exact peersOff p (trunk.peers ▸ isPeer) x inWindow covered

/-- The cut: every field of `NodeCut` and `CutExtra` at +0x156. -/
theorem node_cut (framed : FramedHolds) (premises : Premises fetch L A)
    (trunk : Trunk L A c s w v4 key cidr pid ra names stream d seq a)
    (peersOff : ∀ peer ∈ L.peers, ∀ x,
      InRange (s.data.regs.rsp.toBitVec - .ofNat 64 (insertWindow + A.depth)) (insertWindow + A.depth) x →
      ¬Pair.Span.contains (peer.2,Layouts.peerSize) x)
    (bound : cidr ≤ (if v4 then 32 else 128))
    (present : ∀ id, placed = some id → ∃ n, (bump d).nodes.get? id = some n)
    (family : Nat) (families : family = if v4 then 4 else 6)
    {word : UInt64} {v : MachineState} (pcV : v.pc = Add.entry+0x156)
    (mid : Mid L A c s v4 names d seq a (if v4 then 32 else 128) placed word v.data)
    (object : Object L names word.toNat) (zero : readNat v word.toNat 72 = .ok 0)
    (idle : A.Idle v.data.dmem (names.trie.nodes.map (·.2) ++ [word.toNat]) (stream.drop 1)) :
    NodeCut fetch L A c s ra w d key cidr pid stream placed names word.toNat v ∧
    CutExtra L s v family := by
  refine ⟨{
    boundary := node_boundary trunk peersOff bound pcV mid object zero
    table := trunk.table
    peers := trunk.peers
    arena := trunk.inArena
    fresh := object.arena
    apart := trunk.objectsApart
    idle := idle
    placedAt := (placed_address mid.related present mid.rbx).1
    flight := mid.flight trunk v.pc
    calls := mid.ready
    seq := mid.seqAdvanced trunk v.pc
    exits := mid.exits framed premises trunk v.pc },?_⟩
  exact cutExtra_of_frame trunk family families v mid.stack mid.r13 mid.rbp
    (mid.loads (8+8) 8 (by decide) (.inl (by decide)))
end

#print axioms node_boundary_of_fields
#print axioms cut_stack_off_peers
#print axioms node_boundary
#print axioms node_cut
end C1Trunk
