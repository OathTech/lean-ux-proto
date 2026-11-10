import C1BelowWholeMachine

/-! Result C1, work package 3, the split path: from the end of the
connections at the common exit to `AtExit`. -/
namespace Binary.Statements.C1.Proof
open Leanux Leanux.WG Binary.Pair Binary.Pair.Allowedips Binary.TrustBase
open Binary.CommonBitsCoverage Binary.Statements.C1 Binary.AllowedipsMutationImage
open Binary.Pair.Allowedips.Root AllowedipsChild Binary.AllowedipsRelation
open Binary.SplitStage3 Binary.SplitStage3.Path
local instance : Labels := Image.linkedLabels

theorem seq_setSlot (d : Device) (slot : Slot) (v : Option NodeId) :
    (setSlot d slot v).peerAllowedips.seq = d.peerAllowedips.seq := by
  cases slot with
  | root4 => rfl
  | root6 => rfl
  | child parent bit =>
    simp only [setSlot]
    cases d.nodes.get? parent <;> rfl

theorem seq_connect (d : Device) (slot : Slot) (id : NodeId) :
    (connect d slot id).peerAllowedips.seq = d.peerAllowedips.seq := by
  unfold connect
  split
  · rw [seq_setSlot]
  · rfl

theorem seq_chooseConnect (d : Device) (parent node : NodeId) :
    (chooseConnect d parent node).peerAllowedips.seq = d.peerAllowedips.seq := by
  unfold chooseConnect
  split
  · exact seq_connect _ _ _
  · rfl

theorem seq_addTail (d : Device) (pid : PeerId) (id : NodeId) :
    (addTail d pid id).peerAllowedips.seq = d.peerAllowedips.seq := by
  unfold addTail
  split <;> rfl

/-- The split leaves the sequence as the wrapper's increment left it. -/
theorem seq_splitDevice (d : Device) (family key cidr pid : Nat) (placed : Option NodeId) (downId : NodeId)
    (least : Nat) :
    (splitDevice d family key cidr pid placed downId least).peerAllowedips.seq = (bump d).peerAllowedips.seq := by
  unfold splitDevice attached
  cases placed with
  | none =>
    simp only
    rw [seq_connect,seq_chooseConnect,seq_chooseConnect]
    exact seq_addTail _ _ _
  | some p =>
    simp only
    rw [seq_chooseConnect,seq_chooseConnect,seq_chooseConnect]
    exact seq_addTail _ _ _

namespace SplitCtx
variable {fetch : Int64 → Option Decoded} {L : Layout} {A : Allocator} {c : Context}
  {s : MachineState} {ra : UInt64} {w : World} {d : Device} {family key cidr pid : Nat}
  {stream : List HiddenRecord} {placed : Option NodeId} {names : Allowedips.Names} {base : Nat}
  {e a t : MachineState} {m : DataMem} {downId child : Nat} {downNode : AipNode}
  {rest : List HiddenRecord} {base2 : Nat}
  (x : SplitCtx fetch L A c s ra w d family key cidr pid stream placed names base e a t m downId child
    downNode rest base2)
  {u : MachineState} {sel : Nat}
  (k : AtConnect c e t u base base2 child (widthOf family)
    (min cidr (AllowedipsRelation.common (widthOf family) downNode.bits key)) key sel)
include x k

/-- THE END OF THE SPLIT PATH. A state at the common exit with zero in `rbx`,
related to `step`'s device under the twice-extended names, whose writes
since `add+0x338` fall in kept nodes, fixed words, the callback's return
word or the coverage buffer, is `AtExit`. -/
theorem finish (premises : Premises fetch L A) {w' : World} {answer : Int} {exact : Bool} {st : Step}
    (inv : Inv L A w s.data.dmem)
    (facts : StepFacts w family key cidr pid answer w' d stream placed exact st)
    (dropped : stream.drop st.consumed = rest) (zero : answer = 0)
    (seq : st.device.peerAllowedips.seq = (bump d).peerAllowedips.seq)
    {v : MachineState} (P : BitVec 64 → Prop)
    (pc : v.pc = Add.entry + 0x549) (rbx : v.data.regs.rbx = 0) (rsp : v.data.regs.rsp = u.data.regs.rsp)
    (related : Allowedips.Corresponds ((names.allocated base).allocated base2) nodeOffsets v.data.dmem st.device)
    (shape : Allowedips.heap ((names.allocated base).allocated base2) (Allowedips.target st.device)
      v.data.dmem = .ok ())
    (ready : CallsReady c v.data) (frame : EqualOutside P u.data.dmem v.data.dmem)
    (inside : ∀ y, P y → (Kept (liveOf names base ++ [base2]) y ∨ ∃ span ∈ L.fixed, span.contains y) ∨
      CallWrites u.data c y)
    (mapped : MappedLe u.data.dmem v.data.dmem)
    (flag : v.data.system.bits[10] = u.data.system.bits[10]) :
    AtExit L A c s e w' answer v := by
  have position := x.frame
  have stackV : v.data.regs.rsp = e.data.regs.rsp := rsp.trans k.rsp
  have stackN : v.data.regs.rsp.toNat = e.data.regs.rsp.toNat := by rw [stackV]
  have stackT : t.data.regs.rsp.toNat = e.data.regs.rsp.toNat := by rw [x.stackT]
  have rspE : e.data.regs.rsp.toBitVec.toNat = e.data.regs.rsp.toNat := rfl
  have fixedHeap {y : BitVec 64} (fixed : ∃ span ∈ L.fixed, span.contains y) : L.Heap y := by
    obtain ⟨span,member,within⟩ := fixed
    exact ⟨span,List.mem_append_left _ member,within⟩
  have heapOf {y : BitVec 64} (solid : Kept (liveOf names base ++ [base2]) y ∨ ∃ span ∈ L.fixed, span.contains y) :
      L.Heap y := solid.elim (x.keptHeap) fixedHeap
  have frameTV : EqualOutside (fun y => C1Internal.Writes c t.data.regs.rsp base2 y ∨ P y)
      t.data.dmem v.data.dmem :=
    fun y outside => (k.frame y (fun h => outside (.inl h))).trans (frame y (fun h => outside (.inr h)))
  have savedNear {y : BitVec 64} (saved : InRange (.ofNat 64 (t.data.regs.rsp.toNat+24)) 8 y) :
      e.data.regs.rsp.toNat + 24 ≤ y.toNat ∧ y.toNat < e.data.regs.rsp.toNat + 32 := by
    have := range_nat (by omega) saved
    omega
  refine {
    pc := pc
    stack := stackV
    flight := x.grown.flight.later _ (by unfold insertWindow; omega) (by omega) frameTV ?_
      (k.mapped.trans mapped) (flag.trans k.flag) ready.state
    calls := ready
    saved := ?_
    result := ?_
    inv := ?_
    seq := seq_kept x.cut.related.1 related x.cut.table x.cut.table seq }
  · rintro y (written|written)
    · rcases written with node|saved|push|buffer
      · exact .inr (.inr (nodeHeap x.grown.arena node))
      · have near := savedNear saved
        exact .inl (x.near_scratch y (by omega) (by omega))
      · have near := x.pushNear x.stackT push
        exact .inl (x.near_scratch y near.1 near.2)
      · exact .inr (.inl buffer)
    · rcases inside y written with solid|push|buffer
      · exact .inr (.inr (heapOf solid))
      · have near := x.pushNear k.rsp push
        exact .inl (x.near_scratch y near.1 near.2)
      · exact .inr (.inl buffer)
  · rintro y ⟨i,bound,location⟩
    have value : y.toNat = e.data.regs.rsp.toNat + 48 + i := by rw [location]; bv_omega
    have window : Window A s y := by
      apply window_nat x.rfacts
      · unfold insertWindow; omega
      · omega
    have notHeap : ¬L.Heap y := fun heap => x.rfacts.heap_window heap window
    have notBuffer : ¬c.writes y := fun written => x.rfacts.writes_window written window
    have notP : ¬P y := by
      intro written
      rcases inside y written with solid|push|buffer
      · exact notHeap (heapOf solid)
      · have near := x.pushNear k.rsp push
        omega
      · exact notBuffer buffer
    have notW : ¬C1Internal.Writes c t.data.regs.rsp base2 y := by
      rintro (node|saved|push|buffer)
      · exact notHeap (nodeHeap x.grown.arena node)
      · have near := savedNear saved
        omega
      · have near := x.pushNear x.stackT push
        omega
      · exact notBuffer buffer
    rw [←frame y notP,←k.frame y notW,x.grown.kept y (.inl ⟨48+i,by rw [x.stackA]; omega,by
      rw [location,x.stackA,BitVec.add_assoc]
      congr 1
      rw [BitVec.ofNat_add]
      rfl⟩)]
    exact x.ac.saved y ⟨i,bound,location⟩
  · rw [zero]
    simp [Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,BitVec.drop,BitVec.take,rbx]
  · obtain ⟨⟨d',device,same⟩,armedAfter,records,sites⟩ := facts.final inv
    rw [dropped] at records sites
    have list : ((names.allocated base).allocated base2).trie.nodes.map (·.2) = liveOf names base ++ [base2] := by
      simp [Names.allocated,liveOf]
    refine inv_of_relation (names := (names.allocated base).allocated base2) x.cut.table x.cut.peers device same related shape armedAfter records sites
      x.cut.apart ?_ ?_
    · intro node member
      apply x.liveArena2
      rw [←list]
      exact List.mem_map.mpr ⟨node,member,rfl⟩
    · rw [list]
      apply premises.allocator.frame _ _ _ _ x.grown.idle
      intro y arena loose
      apply frameTV y
      have heap : L.Heap y := Rollback.arena_heap arena
      rintro (written|written)
      · rcases written with node|saved|push|buffer
        · exact loose ⟨base2,List.mem_append_right _ (List.mem_singleton_self _),node⟩
        · have near := savedNear saved
          exact (x.heapFar heap).1 (by omega)
        · exact (x.heapFar heap).1 (x.pushNear x.stackT push)
        · exact (x.heapFar heap).2.2 buffer
      · rcases inside y written with (kept|fixed)|call
        · exact loose kept
        · exact x.fixedOutside fixed arena
        · exact x.callFar k heap call

end SplitCtx

#print axioms SplitCtx.finish
end Binary.Statements.C1.Proof
