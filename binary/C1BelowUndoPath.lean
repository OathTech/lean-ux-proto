import C1BelowUndoLayout
import C1BelowUndoCase
import C1BelowUndo
import C1BelowAlloc
import C1BelowSeq

/-! Result C1, work package 3: the rollback segment (case `splitNoMem`) from
the comparison at `add+0x267` to the common exit, composed from the second
allocation (`AllocRule`), the rollback's machine tail (`FreeRule`) and the
rollback's data side. The hypotheses about the state at `add+0x267` are what
the prefix establishes there; nothing is assumed of an execution. -/
namespace Binary.Statements.C1.Proof.Undo
open Leanux Leanux.WG Binary.Pair Binary.Pair.Allowedips Binary.TrustBase
open Binary.CommonBitsCoverage Binary.Statements.C1 Binary.AllowedipsMutationImage
open Binary.Statements.C1.Proof.Rollback Binary.Pair.Allowedips.Root
local instance : Labels := Image.linkedLabels

variable {L : Layout} {A : Allocator} {c : Context} {s : MachineState} {family : Nat} {ra : UInt64}

/-- A byte of `add`'s frame or of the frames above it, up to the wrapper's
return word: its natural address, that it is in the caller's window, and
which of the stack words the segment writes it misses. -/
theorem stack_byte (facts : ReadyFacts L A c s family ra) {r : UInt64}
    (high : r.toNat + 48 ≤ s.data.regs.rsp.toNat)
    (low : s.data.regs.rsp.toNat + 48 ≤ r.toNat + insertWindow) {k : Nat}
    (bound : k < s.data.regs.rsp.toNat + 8 - r.toNat) :
    Window A s (r.toBitVec + .ofNat 64 k) ∧ ¬InRange (r.toBitVec - 8) 8 (r.toBitVec + .ofNat 64 k) ∧
    (8 ≤ k → ¬InRange r.toBitVec 8 (r.toBitVec + .ofNat 64 k)) ∧
    (k < 24 ∨ 32 ≤ k → ¬InRange (r.toBitVec + 0x18) 8 (r.toBitVec + .ofNat 64 k)) := by
  have window := window_bounds facts
  unfold insertWindow at low window
  have size := r.toBitVec.isLt
  have rsp : r.toBitVec.toNat = r.toNat := rfl
  have value : (r.toBitVec + .ofNat 64 k).toNat = r.toNat + k := by
    simp only [BitVec.toNat_add,BitVec.toNat_ofNat,rsp]
    omega
  have eight : (8 : BitVec 64).toNat = 8 := rfl
  have offset : (0x18 : BitVec 64).toNat = 24 := rfl
  have pushAt : (r.toBitVec - 8).toNat = r.toNat - 8 := by
    simp only [BitVec.toNat_sub,eight,rsp]
    omega
  have savedAt : (r.toBitVec + 0x18).toNat = r.toNat + 24 := by
    simp only [BitVec.toNat_add,offset,rsp]
    omega
  refine ⟨window_nat (by unfold insertWindow; omega) (by unfold insertWindow; omega) (by omega),?_,?_,?_⟩
  · intro inside
    have at_ := range_nat (by rw [pushAt]; omega) inside
    rw [pushAt,value] at at_
    omega
  · intro far inside
    have at_ := range_nat (by omega) inside
    rw [value] at at_
    omega
  · intro far inside
    have at_ := range_nat (by rw [savedAt]; omega) inside
    rw [savedAt,value] at at_
    omega

/-- The three bytes the first initialization writes on the stack are in the window. -/
theorem stack_writes_window (facts : ReadyFacts L A c s family ra) {r : UInt64}
    (high : r.toNat + 48 ≤ s.data.regs.rsp.toNat)
    (low : s.data.regs.rsp.toNat + 48 ≤ r.toNat + insertWindow) {x : BitVec 64}
    (written : NodeInit.StackWrites r.toNat x) : Window A s x := by
  obtain ⟨offset,member,i,bound,at_⟩ := written
  have window := window_bounds facts
  unfold insertWindow at low window
  have size := r.toNat_lt_size
  have small : offset < 48 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    omega
  have value : x.toNat = r.toNat + offset := by
    have raw := congrArg BitVec.toNat at_
    simp only [BitVec.toNat_add,BitVec.toNat_ofNat] at raw
    simp only [UInt64.size] at size
    omega
  exact window_nat (by unfold insertWindow; omega) (by unfold insertWindow; omega) (by omega)

/-- THE ROLLBACK SEGMENT. From the comparison at `add+0x267` in case
`splitNoMem` to the common exit with everything `Exits` and `InsertStep`
need: `-ENOMEM` in `ebx`, the frames above `add`'s locals intact, and the
invariant for the mirror's final world. -/
theorem rollback_segment (alloc : AllocRule) (free : FreeRule)
    {fetch : Int64 → Option Decoded} {L : Layout} {A : Allocator} (premises : Premises fetch L A)
    {c : Context} {s : MachineState} {w w' : World} {family key cidr pid : Nat} {ra : UInt64}
    {answer : Int} {d : Device} {stream : List HiddenRecord} {placed : Option NodeId} {exact : Bool}
    {st : Step} {names : Allowedips.Names} {base : Nat} {e a : MachineState}
    {downId : NodeId} {down : AipNode} {m1 : DataMem}
    (ready : insertReady L A c s family key cidr pid ra = .ok ())
    (inv : Inv L A w s.data.dmem)
    (facts : StepFacts w family key cidr pid answer w' d stream placed exact st)
    (case : st.case = .splitNoMem)
    (cut : NodeCut fetch L A c s ra w d key cidr pid stream placed names base e)
    (high : e.data.regs.rsp.toNat + 48 ≤ s.data.regs.rsp.toNat)
    (low : s.data.regs.rsp.toNat + 48 ≤ e.data.regs.rsp.toNat + insertWindow)
    (lower : below (bump d) (rootOf d family) key placed = some downId)
    (present : (bump d).nodes.get? downId = some down)
    (pc : a.pc = Add.entry + 0x267) (stack : a.data.regs.rsp = e.data.regs.rsp)
    (flight : InFlight L A c s a) (calls : CallsReady c a.data)
    (cidrByte : a.data.dmem.loadInt (a.data.regs.rsp.toBitVec+0x10) 1 = some ((BitVec.ofNat 8 cidr).toNat : Int))
    (baseWord : a.data.dmem.loadInt (a.data.regs.rsp.toBitVec+0x18) 8 = some ((BitVec.ofNat 64 base).toNat : Int))
    (common : (a.data.regs.get (.low .r13 .W8)).toNat =
      AllowedipsRelation.common (widthOf family) down.bits key)
    (topMapped : (a.data.dmem.loadInt a.data.regs.rsp.toBitVec 8).isSome = true)
    (idle : A.Idle a.data.dmem (names.trie.nodes.map (·.2) ++ [base]) (stream.drop 1))
    (summary : NodeInit.effect e.data = .ok (m1,base))
    (heap : ∀ x, L.Heap x → a.data.dmem.get? x = m1.get? x)
    (saved : ∀ x, InRange (e.data.regs.rsp.toBitVec + 48)
        (s.data.regs.rsp.toNat + 8 - (e.data.regs.rsp.toNat + 48)) x →
      a.data.dmem.get? x = e.data.dmem.get? x) :
    Eventually (instructionStep fetch) (AtExit L A c s e w' answer) a := by
  have rfacts := ready_facts ready
  have window := window_bounds rfacts
  obtain ⟨shorter,fits,result,device,first,second,rest,shape,site,dropped,refused⟩ :=
    rollback_case facts case lower present
  obtain ⟨last,ring⟩ := ringed cut.boundary summary
  have fields := NodeInit.boundary_fields cut.boundary
  have highA : a.data.regs.rsp.toNat + 48 ≤ s.data.regs.rsp.toNat := by rw [stack]; exact high
  have lowA : s.data.regs.rsp.toNat + 48 ≤ a.data.regs.rsp.toNat + insertWindow := by rw [stack]; exact low
  have member : base ∈ names.trie.nodes.map (·.2) ++ [base] := List.mem_append_right _ (List.mem_singleton_self _)
  have arena : ∀ node ∈ names.trie.nodes.map (·.2) ++ [base], InArena L node := by
    intro node present
    rcases List.mem_append.mp present with old | new
    · obtain ⟨pair,named,rfl⟩ := List.mem_map.mp old
      exact cut.arena pair named
    · rw [List.mem_singleton.mp new]; exact cut.fresh
  have absent : base ∉ names.trie.nodes.map (·.2) := by
    intro present
    obtain ⟨pair,named,same⟩ := List.mem_map.mp present
    exact fields.fresh pair named same
  have baseSmall : base < 2^64 := by have := ring.extent; omega
  have cidrSmall : cidr < 2^8 := by have := widthOf_le family; omega
  have idleA : A.Idle a.data.dmem (names.trie.nodes.map (·.2) ++ [base]) (second :: rest) := by
    have h := idle
    rw [shape] at h
    exact h
  have step1 := Second.second_allocation alloc fetch L A premises c s a family key cidr pid ra _ second rest
    (BitVec.ofNat 8 cidr) (BitVec.ofNat 64 base) ready cut.apart arena pc flight highA lowA calls cidrByte baseWord
    (by rw [common,BitVec.toNat_ofNat,Nat.mod_eq_of_lt cidrSmall]; exact shorter) site idleA
  apply eventually_trans (instructionStep fetch) _ _ _ step1
  rintro t ⟨pcT,stackT,_,_,_,_,_,_,result1,flightT,callsT,covered1,frame1,guarded1⟩
  obtain ⟨nullCase,_⟩ := result1
  obtain ⟨zero,idleT⟩ := nullCase refused
  have raxT : t.data.regs.rax = 0 := UInt64.toNat_inj.mp zero
  have highT : t.data.regs.rsp.toNat + 48 ≤ s.data.regs.rsp.toNat := by rw [stackT]; exact highA
  have lowT : s.data.regs.rsp.toNat + 48 ≤ t.data.regs.rsp.toNat + insertWindow := by rw [stackT]; exact lowA
  -- classes of heap bytes
  have keptOld {y : BitVec 64} (kept : Kept (names.trie.nodes.map (·.2)) y) :
      Kept (names.trie.nodes.map (·.2) ++ [base]) y := by
    obtain ⟨object,named,inside⟩ := kept
    exact ⟨object,List.mem_append_left _ named,inside⟩
  have keptHeap {y : BitVec 64} (kept : Kept (names.trie.nodes.map (·.2) ++ [base]) y) : L.Heap y :=
    arena_heap (kept_arena arena kept)
  have byteA (k : Nat) (bound : k < s.data.regs.rsp.toNat + 8 - a.data.regs.rsp.toNat) :=
    stack_byte rfacts highA lowA bound
  have windowOf {y : BitVec 64} {n : Nat} (within : n ≤ s.data.regs.rsp.toNat + 8 - a.data.regs.rsp.toNat)
      (inside : InRange a.data.regs.rsp.toBitVec n y) : Window A s y := by
    obtain ⟨i,bound,at_⟩ := inside
    rw [at_]
    exact (byteA i (by omega)).1
  have pushWindow {y : BitVec 64} (inside : InRange (a.data.regs.rsp.toBitVec - 8) 8 y) : Window A s y :=
    scratch_window (words_scratch rfacts highA lowA (words_push inside))
  have savedWindow {y : BitVec 64} (inside : InRange (a.data.regs.rsp.toBitVec+0x18) 8 y) : Window A s y :=
    scratch_window (Second.saved_scratch rfacts highA lowA inside)
  -- heap bytes through the allocation
  have heapC1 (y : BitVec 64) (hy : L.Heap y) : covered1.get? y = a.data.dmem.get? y :=
    ((storeInt_frame a.data.dmem _ 8 _ y (fun h => rfacts.heap_window hy (savedWindow h))).trans
      (frame1 y (fun h => h.elim (fun p => rfacts.heap_window hy (pushWindow p)) (rfacts.heap_writes hy)))).symm
  have heapT (y : BitVec 64)
      (cls : Fixed L y ∨ Kept (names.trie.nodes.map (·.2) ++ [base]) y) : t.data.dmem.get? y = m1.get? y := by
    have hy : L.Heap y := cls.elim Fixed.heap keptHeap
    rw [guarded1 y (cls.elim (fun f => .inr (.inl f)) (fun k => .inr (.inr (.inl k)))),heapC1 y hy,heap y hy]
  have loadT (address size : Nat)
      (cls : ∀ i < size, Fixed L (.ofNat 64 address + .ofNat 64 i) ∨
        Kept (names.trie.nodes.map (·.2) ++ [base]) (.ofNat 64 address + .ofNat 64 i)) :
      t.data.dmem.loadInt (.ofNat 64 address) size = m1.loadInt (.ofNat 64 address) size :=
    loadInt_bytes_congr _ _ (fun i bound => heapT _ (cls i bound))
  have baseCls (offset : Nat) (within : offset+8 ≤ 72) (i : Nat) (bound : i < 8) :
      Fixed L (.ofNat 64 (base+offset) + .ofNat 64 i) ∨
        Kept (names.trie.nodes.map (·.2) ++ [base]) (.ofNat 64 (base+offset) + .ofNat 64 i) :=
    .inr ⟨base,member,range_slice within ⟨i,bound,rfl⟩⟩
  have headSlot : LinkSlot names (e.data.regs.r14.toNat+1096) := .peer ring.owner
  have slotCls {link offset : Nat} (slot : LinkSlot names link) (which : offset = 0 ∨ offset = 8)
      {y : BitVec 64} (inside : InRange (.ofNat 64 (link+offset)) 8 y) :
      Fixed L y ∨ Kept (names.trie.nodes.map (·.2) ++ [base]) y :=
    (slot_class cut.peers slot which inside).imp id keptOld
  obtain ⟨hspan,hmem,hlow,hhigh⟩ := slot_allocation headSlot
  have hb := ring.bounded hspan hmem
  have headSmall : e.data.regs.r14.toNat+1096 < 2^64 := by omega
  obtain ⟨lspan,lmem,llow,lhigh⟩ := slot_allocation ring.slot
  have lb := ring.bounded lspan lmem
  have lastSmall : last < 2^64 := by omega
  have add56 : (BitVec.ofNat 64 base + 56 : BitVec 64) = BitVec.ofNat 64 (base+56) :=
    (BitVec.ofNat_add base 56).symm
  have add64 : (BitVec.ofNat 64 base + 64 : BitVec 64) = BitVec.ofNat 64 (base+56+8) := by
    rw [show base+56+8 = base+64 by omega]
    exact (BitVec.ofNat_add base 64).symm
  have headBack : (BitVec.ofNat 64 (e.data.regs.r14.toNat+1096) + 8 : BitVec 64) =
      BitVec.ofNat 64 (e.data.regs.r14.toNat+1096+8) :=
    (BitVec.ofNat_add (e.data.regs.r14.toNat+1096) 8).symm
  -- the rollback's reads at the state after the refused allocation
  have nextRead : t.data.dmem.loadInt (.ofNat 64 base + 56) 8 = some ((e.data.regs.r14.toNat+1096 : Nat) : Int) := by
    rw [add56,loadT _ 8 (baseCls 56 (by decide))]; exact ring.next
  have prevRead : t.data.dmem.loadInt (.ofNat 64 base + 64) 8 = some (last : Int) := by
    rw [add64,loadT _ 8 (fun i bound => by
      have h := baseCls 64 (by decide) i bound
      rwa [show base+64 = base+56+8 by omega] at h)]
    exact ring.prev
  have nextMapped : (t.data.dmem.loadInt (.ofNat 64 (e.data.regs.r14.toNat+1096) + 8) 8).isSome = true := by
    rw [headBack,loadT _ 8 (fun i bound => slotCls headSlot (.inr rfl) ⟨i,bound,rfl⟩),ring.headBack]; rfl
  have prevMapped : (t.data.dmem.loadInt (.ofNat 64 last) 8).isSome = true := by
    rw [loadT last 8 (fun i bound => slotCls (offset := 0) ring.slot (.inl rfl) ⟨i,bound,rfl⟩),ring.lastNext]; rfl
  have links : ∀ y, InRange (.ofNat 64 (e.data.regs.r14.toNat+1096) + 8) 8 y ∨ InRange (.ofNat 64 last) 8 y →
      L.Heap y ∧ (L.Arena y → Kept (names.trie.nodes.map (·.2) ++ [base]) y) := by
    intro y inside
    have cls : Fixed L y ∨ Kept (names.trie.nodes.map (·.2) ++ [base]) y := by
      rcases inside with back | forward
      · rw [headBack] at back
        exact slotCls headSlot (.inr rfl) back
      · exact slotCls (offset := 0) ring.slot (.inl rfl) forward
    rcases cls with fixed | kept
    · exact ⟨fixed.heap,fun inArena => absurd inArena (fixed.not_arena cut.apart)⟩
    · exact ⟨keptHeap kept,fun _ => kept⟩
  -- the stack words at the state after the refused allocation
  have stackT1 (k : Nat) (bound : k < s.data.regs.rsp.toNat + 8 - a.data.regs.rsp.toNat) :
      t.data.dmem.get? (a.data.regs.rsp.toBitVec + .ofNat 64 k) =
        (a.data.dmem.storeInt (a.data.regs.rsp.toBitVec+0x18) 8 (BitVec.ofNat 64 base).toInt).get?
          (a.data.regs.rsp.toBitVec + .ofNat 64 k) := by
    rw [guarded1 _ (.inl ⟨k,bound,rfl⟩)]
    exact (frame1 _ (fun h => h.elim (byteA k bound).2.1 (fun written =>
      rfacts.writes_window written (byteA k bound).1))).symm
  have localMapped : (t.data.dmem.loadInt t.data.regs.rsp.toBitVec 8).isSome = true := by
    rw [stackT,loadInt_bytes_congr (m' := a.data.dmem) _ 8 (fun i bound => by
      rw [stackT1 i (by omega)]
      exact (storeInt_frame a.data.dmem _ 8 _ _ ((byteA i (by omega)).2.2.2 (.inl (by omega)))).symm)]
    exact topMapped
  have baseRead : t.data.dmem.loadInt (t.data.regs.rsp.toBitVec + 24) 8 = some (base : Int) := by
    rw [stackT,loadInt_bytes_congr
      (m' := a.data.dmem.storeInt (a.data.regs.rsp.toBitVec+0x18) 8 (BitVec.ofNat 64 base).toInt) _ 8
      (fun i bound => by
        have at_ : a.data.regs.rsp.toBitVec + 24 + BitVec.ofNat 64 i =
            a.data.regs.rsp.toBitVec + BitVec.ofNat 64 (24+i) := by
          rw [BitVec.ofNat_add,←BitVec.add_assoc]; rfl
        rw [at_]
        exact stackT1 (24+i) (by omega))]
    exact load_store_nat _ _ baseSmall
  have step2 := Rollback.rollback free fetch L A premises c s t family key cidr pid ra _ rest base
    (e.data.regs.r14.toNat+1096) last ready cut.apart arena pcT raxT flightT highT lowT callsT localMapped baseRead
    member nextRead prevRead nextMapped prevMapped links idleT
  apply eventually_weaken (instructionStep fetch) _ _ _ _ step2
  rintro x ⟨pcX,stackX,ebx,flightX,callsX,idleX,covered2,frame2,guarded2⟩
  rw [erase_fresh absent] at idleX guarded2
  rw [stackT] at frame2
  have byteT (k : Nat) (bound : k < s.data.regs.rsp.toNat + 8 - a.data.regs.rsp.toNat) :
      Guarded L s t (names.trie.nodes.map (·.2)) (a.data.regs.rsp.toBitVec + .ofNat 64 k) :=
    .inl ⟨k,by rw [stackT]; exact bound,by rw [stackT]⟩
  have listHeap (y : BitVec 64) (written : ListWrites base (e.data.regs.r14.toNat+1096) last y) : L.Heap y := by
    rcases written with link | node
    · exact (links y link).1
    · exact keptHeap ⟨base,member,node.elim
        (node_bytes (offset := 56) (by decide)) (node_bytes (offset := 64) (by decide))⟩
  have heapC2 (y : BitVec 64) (hy : L.Heap y) : covered2.get? y = t.data.dmem.get? y :=
    ((storeInt_frame t.data.dmem _ 8 _ y (fun h => rfacts.heap_window hy (windowOf (n := 8) (by omega) h))).trans
      (frame2 y (fun h => h.elim (fun p => rfacts.heap_window hy (pushWindow p)) (rfacts.heap_writes hy)))).symm
  -- every byte the old interpretation reads is the cut's
  obtain ⟨related,shape0⟩ := NodeCut.related cut
  have restored : ∀ span ∈ readSpans names nodeOffsets, ∀ y, span.contains y →
      e.data.dmem.get? y = x.data.dmem.get? y := by
    intro span named y inside
    have cls := read_class cut.table cut.peers named inside
    have hy : L.Heap y := cls.elim Fixed.heap (fun k => keptHeap (keptOld k))
    rw [guarded2 y (cls.elim (fun f => .inr (.inl f)) (fun k => .inr (.inr (.inl k))))]
    have offBase : ¬InRange (.ofNat 64 base) 72 y := by
      intro inBase
      rcases cls with fixed | kept
      · exact fixed.not_arena cut.apart (kept_arena arena ⟨base,member,inBase⟩)
      · obtain ⟨object,old,within⟩ := kept
        obtain ⟨pair,isNamed,rfl⟩ := List.mem_map.mp old
        have allocation : (pair.2,72) ∈ allocations names nodeOffsets := node_allocation isNamed
        have apart : base+72 ≤ pair.2 ∨ pair.2+72 ≤ base := ring.fresh _ allocation
        have bounded : pair.2+72 ≤ 2^64 := ring.bounded _ allocation
        have extent := ring.extent
        have within : InRange (.ofNat 64 pair.2) 72 y := within
        exact range_apart (by omega) (by omega) (by omega) y inBase within
    have dropPoison : (poisoned (unlinked covered2 (e.data.regs.r14.toNat+1096) last) base).get? y =
        (unlinked covered2 (e.data.regs.r14.toNat+1096) last).get? y :=
      ((storeInt_frame _ _ 8 _ y (fun h => offBase (node_bytes (offset := 56) (by decide) h))).trans
        (storeInt_frame _ _ 8 _ y (fun h => offBase (node_bytes (offset := 64) (by decide) h)))).symm
    rw [dropPoison]
    by_cases inLast : InRange (.ofNat 64 last) 8 y
    · exact bytes_of_words ring.closed (load_store_nat _ _ headSmall) inLast
    · have dropForward : (unlinked covered2 (e.data.regs.r14.toNat+1096) last).get? y =
          (covered2.storeInt (.ofNat 64 (e.data.regs.r14.toNat+1096) + 8) 8 (BitVec.ofNat 64 last).toInt).get? y :=
        (storeInt_frame _ _ 8 _ y inLast).symm
      rw [dropForward,headBack]
      by_cases inBack : InRange (.ofNat 64 (e.data.regs.r14.toNat+1096+8)) 8 y
      · exact bytes_of_words ring.tail (load_store_nat _ _ lastSmall) inBack
      · rw [←storeInt_frame covered2 _ 8 _ y inBack,heapC2 y hy,
          heapT y (cls.imp id keptOld)]
        exact ring.frame y (fun written => by
          rcases written with fresh | stackWrite | back | forward
          · exact offBase fresh
          · exact rfacts.heap_window hy (stack_writes_window rfacts high low stackWrite)
          · exact inBack back
          · exact inLast forward)
  obtain ⟨relatedX,shapeX⟩ := rollback_relation family key cidr pid related shape0 restored
  obtain ⟨⟨final,deviceX,sameX⟩,armedX,recordsX,sitesX⟩ := facts.final inv
  rw [dropped] at recordsX sitesX
  rw [device] at sameX
  refine {
    pc := pcX
    stack := stackX.trans (stackT.trans stack)
    flight := flightX
    calls := callsX
    saved := ?_
    result := by rw [result]; exact ebx
    inv := inv_of_relation (names := recount names (names.nextNode+1)) cut.table cut.peers deviceX sameX
      relatedX shapeX armedX recordsX sitesX cut.apart cut.arena idleX
    seq := seq_kept related relatedX cut.table cut.table
      (congrArg (·.table.seq) (target_rollbackDevice family key cidr pid related)) }
  intro y inside
  obtain ⟨i,bound,at_⟩ := inside
  have here : y = a.data.regs.rsp.toBitVec + BitVec.ofNat 64 (48+i) := by
    rw [at_,stack,BitVec.ofNat_add,←BitVec.add_assoc]; rfl
  have room : 48+i < s.data.regs.rsp.toNat + 8 - a.data.regs.rsp.toNat := by rw [stack]; omega
  have facts48 := byteA (48+i) room
  rw [←saved y ⟨i,bound,at_⟩,here,guarded2 _ (byteT _ room)]
  have notList : ¬ListWrites base (e.data.regs.r14.toNat+1096) last
      (a.data.regs.rsp.toBitVec + BitVec.ofNat 64 (48+i)) :=
    fun written => rfacts.heap_window (listHeap _ written) facts48.1
  rw [←released_frame covered2 base _ last _ notList,
    ←frame2 _ (fun h => h.elim facts48.2.1 (fun written => rfacts.writes_window written facts48.1)),
    ←storeInt_frame t.data.dmem _ 8 _ _ (facts48.2.2.1 (by omega)),stackT1 _ room]
  exact (storeInt_frame a.data.dmem _ 8 _ _ (facts48.2.2.2 (.inr (by omega)))).symm

#print axioms rollback_segment
end Binary.Statements.C1.Proof.Undo
