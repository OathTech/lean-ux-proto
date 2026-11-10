import C1BelowPrefix

/-! Result C1, work package 3: what the prefix hands its continuations at
`add+0x267` beyond the machine state (`Compared`): the call still in flight,
the heap as the first initialization left it, the saved words above `add`'s
locals, the sequence word, the allocator idle, and the stack locals the
continuations read. -/
namespace Binary.Statements.C1.Proof
open Leanux Leanux.WG Binary.Pair Binary.Pair.Allowedips Binary.TrustBase
open Binary.CommonBitsCoverage Binary.Statements.C1 Binary.AllowedipsMutationImage
open Binary.Pair.Allowedips.Root
local instance : Labels := Image.linkedLabels

/-- The state at `add+0x267` relative to the entry `s`, the cut `e` and the
memory `m` the first initialization left. -/
structure AtCompare (L : Layout) (A : Allocator) (c : Context) (s e : MachineState)
    (names : Allowedips.Names) (base cidr : Nat) (stream : List HiddenRecord) (m : DataMem)
    (t : MachineState) : Prop where
  flight : InFlight L A c s t
  /-- No heap byte was written after the first initialization. -/
  heap : ∀ x, L.Heap x → t.data.dmem.get? x=m.get? x
  /-- The bytes above `add`'s locals up to the wrapper's return word are the cut's. -/
  saved : ∀ a, InRange (e.data.regs.rsp.toBitVec+48)
      (s.data.regs.rsp.toNat+8-(e.data.regs.rsp.toNat+48)) a →
    t.data.dmem.get? a=e.data.dmem.get? a
  seq : readNat t (L.table+AllowedipsMutationLayout.seq) 8=
    readNat e (L.table+AllowedipsMutationLayout.seq) 8
  idle : A.Idle t.data.dmem (names.trie.nodes.map (·.2)++[base]) (stream.drop 1)
  /-- `cmp 0x10(%rsp),%r13b` reads the requested prefix length. -/
  cidrByte : t.data.dmem.loadInt (t.data.regs.rsp.toBitVec+0x10) 1=some ((BitVec.ofNat 8 cidr).toNat : Int)
  /-- `mov 0x18(%rsp),%r8` reloads the fresh node. -/
  baseWord : t.data.dmem.loadInt (t.data.regs.rsp.toBitVec+0x18) 8=some ((BitVec.ofNat 64 base).toNat : Int)
  /-- The saved root-slot pointer is the cut's. -/
  slotWord : t.data.dmem.loadInt (t.data.regs.rsp.toBitVec+8) 8=
    e.data.dmem.loadInt (e.data.regs.rsp.toBitVec+8) 8

variable {L : Layout} {A : Allocator} {c : Context} {s : MachineState} {family : Nat} {ra : UInt64}

theorem zone_scratch_window (rfacts : ReadyFacts L A c s family ra) {e : MachineState}
    (extra : CutExtra L s e family) {a : BitVec 64} (zone : Zone e.data.regs.rsp a) :
    Scratch s (insertWindow+A.depth) a := by
  obtain ⟨fits,top⟩ := rfacts.window_bounds
  have high := extra.frameHigh
  have low := extra.frameLow
  unfold insertWindow at fits low
  obtain ⟨lo,hi⟩ := zone_nat (by omega) (by omega) zone
  exact scratch_nat (by unfold insertWindow; omega) (by omega)

theorem at_compare {fetch : Int64 → Option Decoded} (premises : Premises fetch L A)
    {w : World} {d dd : Device} {key cidr pid : Nat}
    {stream : List HiddenRecord} {placed : Option NodeId} {names : Allowedips.Names} {base child : Nat}
    {e y : MachineState} {m : DataMem}
    (rfacts : ReadyFacts L A c s family ra)
    (cut : NodeCut fetch L A c s ra w d key cidr pid stream placed names base e)
    (extra : CutExtra L s e family) (res : Res names c e.data base)
    (summary : NodeInit.effect e.data=.ok (m,base))
    (held : Held names c e.data dd key cidr pid base child m y.data)
    (flag : y.data.system.bits[10]=e.data.system.bits[10]) :
    AtCompare L A c s e names base cidr stream m y := by
  have fields := NodeInit.boundary_fields cut.boundary
  obtain ⟨actual,_,related,_⟩ := assertAt_ok fields.asserted
  have frameInit : EqualOutside (NodeInit.EntryWrites names e.data base) e.data.dmem m :=
    (NodeInit.core_of_effect fields summary).2
  have frameEY : EqualOutside (fun a => NodeInit.EntryWrites names e.data base a ∨ Late e.data.regs.rsp c a)
      e.data.dmem y.data.dmem :=
    fun a outside => (frameInit a (fun h => outside (.inl h))).trans (held.late a (fun h => outside (.inr h)))
  have scratch : ∀ a, Zone e.data.regs.rsp a → Scratch s (insertWindow+A.depth) a :=
    fun a zone => zone_scratch_window rfacts extra zone
  have window : ∀ a, Zone e.data.regs.rsp a → Window A s a := fun a zone => scratch_window (scratch a zone)
  have stackZone : ∀ a, NodeInit.StackWrites e.data.regs.rsp.toNat a → Zone e.data.regs.rsp a := by
    rintro a ⟨offset,member,inside⟩
    rw [BitVec.ofNat_add,Root.ofNat_uint64] at inside
    have small : offset+1≤48 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      omega
    exact zone_local small inside
  have lateHeap : ∀ a, L.Heap a → ¬Late e.data.regs.rsp c a := by
    intro a heap late
    rcases late_after late with zone|written
    · exact rfacts.heap_window heap (window a zone)
    · exact rfacts.heap_writes heap written
  obtain ⟨fits,top⟩ := rfacts.window_bounds
  have high := extra.frameHigh
  have low := extra.frameLow
  have rspE : e.data.regs.rsp.toBitVec.toNat=e.data.regs.rsp.toNat := rfl
  have localKept (offset size : Nat) (above : 8≤offset) (within : offset+size≤24)
      (clear : ∀ k ∈ [36,43,44], k<offset ∨ offset+size≤k) :
      y.data.dmem.loadInt (e.data.regs.rsp.toBitVec+.ofNat 64 offset) size=
        e.data.dmem.loadInt (e.data.regs.rsp.toBitVec+.ofNat 64 offset) size := by
    rw [←res.init_local frameInit offset size (by omega) clear]
    symm
    apply held.late.loadInt
    rintro i bound (⟨j,boundJ,location⟩|⟨j,boundJ,location⟩|written)
    · bv_omega
    · bv_omega
    · exact res.context _ (writes_bytes written) (zone_local (by omega) ⟨i,bound,rfl⟩)
  refine {
    flight := cut.flight.later _ (by rw [held.stack]; exact cut.flight.low)
      (by rw [held.stack]; exact cut.flight.high) frameEY ?_ held.mapped flag held.ready.state
    heap := fun x heap => (held.late x (lateHeap x heap)).symm
    saved := ?_
    seq := ?_
    idle := premises.allocator.frame _ _ _ _ cut.idle ?_
    cidrByte := ?_
    baseWord := ?_
    slotWord := by rw [held.stack]; exact localKept 8 8 (by decide) (by decide) (by decide) }
  · rintro x (written|late)
    · rcases written with fresh|list|stack
      · exact .inr (.inr (cut.init_heap (.inl fresh)))
      · exact .inr (.inr (cut.init_heap (.inr list)))
      · exact .inl (scratch x (stackZone x stack))
    · rcases late_after late with zone|written
      · exact .inl (scratch x zone)
      · exact .inr (.inl written)
  · rintro a ⟨i,bound,location⟩
    unfold insertWindow at fits low
    have position : a.toNat=e.data.regs.rsp.toNat+48+i := by
      rw [location]
      bv_omega
    have inWindow : Window A s a := window_nat rfacts (by unfold insertWindow; omega) (by omega)
    have notZone : ¬Zone e.data.regs.rsp a := by
      intro zone
      obtain ⟨lo,hi⟩ := zone_nat (by omega) (by omega) zone
      omega
    symm
    apply frameEY
    rintro (written|late)
    · rcases written with fresh|list|stack
      · exact rfacts.heap_window (cut.init_heap (.inl fresh)) inWindow
      · exact rfacts.heap_window (cut.init_heap (.inr list)) inWindow
      · exact notZone (stackZone a stack)
    · rcases late_after late with zone|written
      · exact notZone zone
      · exact rfacts.writes_window written inWindow
  · unfold readNat
    rw [frameEY.loadBytes (.ofNat 64 (L.table+AllowedipsMutationLayout.seq)) 8 (by
      rintro i bound (written|late)
      · refine fields.table_field_apart related (offset:=AllowedipsMutationLayout.seq) (size:=8) (by decide) _ ?_ written
        rw [cut.table]
        exact ⟨i,bound,rfl⟩
      · exact lateHeap _ (seq_in_heap L i bound) late)]
  · intro a arena loose
    apply frameEY
    rintro (written|late)
    · rcases written with fresh|⟨link,slot,offset,which,inside⟩|stack
      · exact loose ⟨base,List.mem_append_right _ (List.mem_singleton_self _),fresh⟩
      · cases slot with
        | node named =>
          rename_i id address
          apply loose
          have live : address ∈ names.trie.nodes.map (·.2)++[base] := by
            rcases List.mem_append.mp named with old|new
            · exact List.mem_append_left _ (List.mem_map.mpr ⟨_,old,rfl⟩)
            · cases List.mem_singleton.mp new
              exact List.mem_append_right _ (List.mem_singleton_self _)
          obtain ⟨i,bound,location⟩ := inside
          refine ⟨address,live,56+offset+i,by unfold nodeSize; rcases which with rfl|rfl <;> omega,?_⟩
          rw [location]
          bv_omega
        | peer named =>
          rename_i id address
          have same : (names.allocated base).trie.peers=L.peers := cut.peers
          rw [same] at named
          obtain ⟨span,member,within⟩ := arena
          have object : (address,Layouts.peerSize) ∈ objectsOf L :=
            List.mem_append_right _ (List.mem_map.mpr ⟨(id,address),named,rfl⟩)
          refine spansApart_sound cut.apart object member ?_ within
          obtain ⟨i,bound,location⟩ := inside
          refine ⟨1096+offset+i,by unfold Layouts.peerSize; rcases which with rfl|rfl <;> omega,?_⟩
          rw [location]
          bv_omega
      · exact rfacts.heap_window ⟨_,List.mem_append_right _ arena.choose_spec.1,arena.choose_spec.2⟩
          (window a (stackZone a stack))
    · exact lateHeap a ⟨_,List.mem_append_right _ arena.choose_spec.1,arena.choose_spec.2⟩ late
  · rw [held.stack]
    have kept := localKept 16 1 (by decide) (by decide) (by decide)
    have read := Trie.readNat_loadInt fields.cidrRead
    have part := MemoryBytes.loadInt_subword _ _ _ _ read 0 1 (by decide)
    rw [slot_address] at part
    have value : ((cidr : Int)/256^0)%(2 : Int)^(8*1)=((BitVec.ofNat 8 cidr).toNat : Int) := by
      simp [BitVec.toNat_ofNat]
    rw [value] at part
    have address : e.data.regs.rsp.toBitVec+BitVec.ofNat 64 16+BitVec.ofNat 64 0=
        e.data.regs.rsp.toBitVec+0x10 := by bv_omega
    rw [address] at part
    exact kept.trans part
  · rw [held.stack]
    have fresh := (allocated_facts fields.allocated).2.2.1
    change base+72<2^64 at fresh
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    exact held.saved

#print axioms at_compare

/-- THE PREFIX. From the cut to the comparison after `common_bits`
(`add+0x267`), for the three cases below the placement: `Compared` (machine
state, pending fresh node, `common_bits`' answer in `r13b`) and `AtCompare`
(in flight, heap frame, saved words, sequence word, allocator idle, stack
locals), for the node `downId` the mirror finds below the placement.
`extra` is what `NodeCut` lacks. -/
theorem prefix_compared {fetch : Int64 → Option Decoded} {L : Layout} {A : Allocator}
    (premises : Premises fetch L A)
    {c : Context} {s : MachineState} {w w' : World} {family key cidr pid : Nat} {ra : UInt64}
    {answer : Int} {d : Device} {stream : List HiddenRecord} {placed : Option NodeId} {exact : Bool}
    {st : Step} {names : Allowedips.Names} {base : Nat} {e : MachineState}
    (ready : insertReady L A c s family key cidr pid ra=.ok ())
    (facts : StepFacts w family key cidr pid answer w' d stream placed exact st)
    (case : st.case = .cover ∨ st.case = .split ∨ st.case = .splitNoMem)
    (cut : NodeCut fetch L A c s ra w d key cidr pid stream placed names base e)
    (extra : CutExtra L s e family) :
    ∃ downId downNode m,
      below (bump d) (rootOf d family) key placed=some downId ∧
      (bump d).nodes.get? downId=some downNode ∧
      NodeInit.effect e.data=.ok (m,base) ∧
      Eventually (instructionStep fetch) (fun t => ∃ child, child≠0 ∧ (downId,child) ∈ names.trie.nodes ∧
        Compared names c e.data (bump d) key cidr pid base child (widthOf family) downNode.bits m t ∧
        AtCompare L A c s e names base cidr stream m t) e := by
  obtain ⟨downId,downNode,m,lower,present,summary,res,run⟩ := prefix_machine premises ready facts case cut extra
  refine ⟨downId,downNode,m,lower,present,summary,?_⟩
  apply eventually_weaken (instructionStep fetch) _ _ _ _ (eventually_flight run)
  rintro y ⟨⟨child,nonzero,named,reached⟩,_,flag⟩
  exact ⟨child,nonzero,named,reached,
    at_compare premises (ready_facts ready) cut extra res summary reached.held flag⟩

#print axioms prefix_compared
end Binary.Statements.C1.Proof
