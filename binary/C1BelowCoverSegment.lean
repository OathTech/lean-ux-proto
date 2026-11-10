import C1BelowCoverExit
import C1BelowPrefixBytes

/-! Result C1, work package 3, covering path: from the prefix's state at the
comparison (`Compared`, `AtCompare`) through the first half of the path
(`choose_and_connect_node(newnode, down)`), with every machine-level
hypothesis of `C1Cover.first_half` derived from the cut, `CutExtra`, the
caller's conditions and the decoded nodes. -/
namespace Binary.Statements.C1.Proof
open Leanux Leanux.WG Binary.Pair Binary.Pair.Allowedips Binary.TrustBase AllowedipsChild
open Binary.CommonBitsCoverage Binary.Statements.C1 Binary.AllowedipsMutationImage
open Binary.Pair.Allowedips.Root Binary.AllowedipsRelation
local instance : Labels := Image.linkedLabels

section
variable {fetch : Int64 → Option Decoded} {L : Layout} {A : Allocator}
  {c : Context} {s : MachineState} {w w' : World} {family key cidr pid : Nat} {ra : UInt64}
  {answer : Int} {d : Device} {stream : List HiddenRecord} {placed : Option NodeId} {exact : Bool}
  {st : Step} {names : Allowedips.Names} {base : Nat} {e : MachineState}

/-- The separations of the covering path at the comparison state, for a
third heap region `other` apart from the node below and the fresh node. -/
theorem cover_apart (ready : insertReady L A c s family key cidr pid ra=.ok ())
    (cut : NodeCut fetch L A c s ra w d key cidr pid stream placed names base e)
    (extra : CutExtra L s e family) {t : MachineData} (stackT : t.regs.rsp=e.data.regs.rsp)
    {downId child : Nat} (named : (downId,child) ∈ names.trie.nodes)
    (other : BitVec 64 → Prop) (otherHeap : ∀ a, other a → L.Heap a)
    (downOther : ∀ a, InRange (.ofNat 64 child) 72 a → ¬other a)
    (baseOther : ∀ a, InRange (.ofNat 64 base) 72 a → ¬other a) :
    C1Cover.Apart c t.regs.rsp (.ofNat 64 child) (.ofNat 64 base) other := by
  have rfacts := ready_facts ready
  have fields := NodeInit.boundary_fields cut.boundary
  obtain ⟨related,_⟩ := cut.related
  have res := resources rfacts cut extra
  have g := fields.geometry related
  have zoneWindow : ∀ a, Zone e.data.regs.rsp a → Window A s a :=
    fun a zone => scratch_window (zone_scratch_window rfacts extra zone)
  have childHeap : ∀ a, InRange (.ofNat 64 child) 72 a → L.Heap a :=
    fun a h => node_heap (cut.arena _ named) h
  have baseHeap : ∀ a, InRange (.ofNat 64 base) 72 a → L.Heap a :=
    fun a h => node_heap cut.fresh h
  have threeHeap : ∀ a, (InRange (.ofNat 64 child) 72 a ∨ InRange (.ofNat 64 base) 72 a ∨ other a) →
      L.Heap a := fun a h => h.elim (childHeap a) (fun h => h.elim (baseHeap a) (otherHeap a))
  have extent := res.extent
  have rspE : e.data.regs.rsp.toBitVec.toNat=e.data.regs.rsp.toNat := rfl
  rw [stackT]
  refine ⟨?_,downOther,baseOther,?_,?_,?_⟩
  · exact nodes_apart g (List.mem_append_left _ named) (allocated_node names base)
      (fun same => fields.fresh _ named (congrArg Prod.snd same))
  · intro a locals three
    exact rfacts.heap_window (threeHeap a three) (zoneWindow a (zone_locals (by decide) locals))
  · rintro a (word|buffer) (locals|three)
    · obtain ⟨i,iBound,place⟩ := word
      obtain ⟨j,jBound,spot⟩ := locals
      rw [place] at spot
      bv_omega
    · exact rfacts.heap_window (threeHeap a three) (zoneWindow a (zone_word word))
    · exact res.context a (writes_bytes buffer) (zone_locals (by decide) locals)
    · exact rfacts.heap_writes (threeHeap a three) buffer
  · rintro a read (locals|three)
    · exact res.context a read (zone_locals (by decide) locals)
    · exact rfacts.heap_bytes (threeHeap a three) read

/-- The first half of the covering path from the prefix's comparison state:
the comparison takes the covering branch, the fresh node is saved, the node
below is linked under the fresh node on the side of its own key. -/
theorem cover_linked (premises : Premises fetch L A)
    (ready : insertReady L A c s family key cidr pid ra=.ok ())
    (cut : NodeCut fetch L A c s ra w d key cidr pid stream placed names base e)
    (extra : CutExtra L s e family)
    {downId child : Nat} {downNode : AipNode} {m : DataMem} {t : MachineState}
    (hasDown : (bump d).nodes.get? downId=some downNode)
    (summary : NodeInit.effect e.data=.ok (m,base))
    (named : (downId,child) ∈ names.trie.nodes)
    (comp : Compared names c e.data (bump d) key cidr pid base child (widthOf family) downNode.bits m t)
    (compared : AtCompare L A c s e names base cidr stream m t)
    (covers : cidr ≤ AllowedipsRelation.common (widthOf family) downNode.bits key)
    (downMeasure : cidr<downNode.cidr) (downWidth : downNode.bitlen=widthOf family)
    (other : BitVec 64 → Prop)
    (apart : C1Cover.Apart c t.data.regs.rsp (.ofNat 64 child) (.ofNat 64 base) other) :
    Eventually (instructionStep fetch) (fun x => ∃ mid,
      C1Cover.Linked c t.data (.ofNat 64 child) (.ofNat 64 base)
        (downNode.bits/2^(widthOf family-1-cidr)%2) mid x) t := by
  have rfacts := ready_facts ready
  have fields := NodeInit.boundary_fields cut.boundary
  obtain ⟨related,_⟩ := cut.related
  have res := resources rfacts cut extra
  have held := comp.held
  have width := extra.width
  have fam := fields.family
  rw [width] at fam
  have decodedDown := held.pending.old_node related named hasDown
  have downFields := Trie.decodeNode_fields decodedDown
  have bounded : downNode.cidr ≤ downNode.bitlen := downFields.bounded
  have short : cidr<widthOf family := by omega
  have position := selector_position (widthOf family) cidr fam short
  have childRange := (Trie.reconstruct_fields related.trie).nodeRange _ _ named
  have childSmall : child<2^64 := by have := childRange.2; omega
  have baseFacts := allocated_facts fields.allocated
  have baseSmall : base<2^64 := by have := baseFacts.2.2.1; omega
  have stackT := held.stack
  obtain ⟨_,ixInit,shInit⟩ := init_bytes fields res summary
  have ixRead : t.data.dmem.loadInt (t.data.regs.rsp.toBitVec+0x2b) 1=
      some ((byteSelector (widthOf family) cidr : Nat) : Int) := by
    rw [←width]
    exact (held.selector_byte res 43 (by omega) (by omega)).trans ixInit
  have shByte : t.data.dmem.loadInt (t.data.regs.rsp.toBitVec+0x2c) 1=some ((7-cidr%8 : Nat) : Int) :=
    (held.selector_byte res 44 (by omega) (by omega)).trans shInit
  have mapped4 : (t.data.dmem.loadInt (t.data.regs.rsp.toBitVec+0x2c) 4).isSome=true := by
    rw [stackT]
    exact held.mapped _ _ (res.local_mapped 44 4 (by omega))
  obtain ⟨v,vRead⟩ := Option.isSome_iff_exists.mp mapped4
  obtain ⟨vLow,vHigh⟩ := loadInt_range _ _ _ _ vRead
  have byte0 := MemoryBytes.loadInt_byte _ _ 4 v vRead 0 (by omega)
  simp only [BitVec.ofNat_eq_ofNat,BitVec.add_zero] at byte0
  have low : v%256=((7-cidr%8 : Nat) : Int) := by
    have h := Option.some.inj (byte0.symm.trans shByte)
    rw [show (256 : Int)^0=1 from rfl,Int.ediv_one] at h
    exact h
  have wordNat : ((BitVec.ofNat 32 v.toNat).toNat : Int)=v := by
    simp only [BitVec.toNat_ofNat]
    omega
  have wordMod : (BitVec.ofNat 32 v.toNat).toNat%32=7-cidr%8 := by omega
  have keyRead := queryByte_read t.data.dmem (.ofNat 64 (child+32)) (widthOf family) downNode.bits
    (byteSelector (widthOf family) cidr) fam position.2 (downWidth ▸ key_words decodedDown)
  have byteBound := queryByte_bound (widthOf family) downNode.bits (byteSelector (widthOf family) cidr)
  have selectedEq := queryByte_select (widthOf family) downNode.bits cidr fam short
  have bitEq : ((BitVec.ofNat 8 (queryByte (widthOf family) downNode.bits (byteSelector (widthOf family) cidr))).getLsbD
      ((BitVec.ofNat 32 v.toNat).toNat%32)).toNat=downNode.bits/2^(widthOf family-1-cidr)%2 := by
    rw [wordMod,bit_selected _ _ (by omega),Nat.mod_eq_of_lt byteBound]
    exact selectedEq
  have a32 : (BitVec.ofNat 64 child+32 : BitVec 64)=.ofNat 64 (child+32) := by
    rw [BitVec.ofNat_add]; rfl
  have localMapped (offset size : Nat) (within : offset+size≤48) :
      (t.data.dmem.loadInt (t.data.regs.rsp.toBitVec+.ofNat 64 offset) size).isSome=true := by
    rw [stackT]
    exact held.mapped _ _ (res.local_mapped offset size within)
  have freshMapped (offset : Nat) (within : offset+8≤72) :
      (t.data.dmem.loadInt (.ofNat 64 (base+offset)) 8).isSome=true :=
    held.mapped _ _ (Option.isSome_of_eq_some (word_loadInt _ _ _ _ _ (fields.zero_word "fresh" offset 8 within)))
  have index16 : byteSelector (widthOf family) cidr<16 := by
    rcases fam with four|four <;> rw [four] at position <;> rw [four] <;> omega
  rw [←bitEq,Placement.at_pc t _ comp.pc]
  exact C1Cover.first_half fetch premises.insertion premises.tracePc c t.data (BitVec.ofNat 8 cidr)
    (.ofNat 64 child) (.ofNat 64 base) (byteSelector (widthOf family) cidr) (BitVec.ofNat 32 v.toNat)
    (BitVec.ofNat 8 (queryByte (widthOf family) downNode.bits (byteSelector (widthOf family) cidr))) _ other
    apart held.ready compared.cidrByte
    (by rw [comp.common,BitVec.toNat_ofNat]; exact Nat.le_trans (Nat.mod_le _ _) covers)
    compared.baseWord
    (by change _=some ((BitVec.ofNat 64 child).toNat : Int)
        rw [stackT,BitVec.toNat_ofNat,Nat.mod_eq_of_lt childSmall]; exact held.down)
    index16 ixRead (by change _=some ((BitVec.ofNat 32 v.toNat).toNat : Int); rw [wordNat]; exact vRead)
    (by change _=some ((BitVec.ofNat 8 _).toNat : Int)
        rw [a32,BitVec.toNat_ofNat,Nat.mod_eq_of_lt byteBound]; exact keyRead)
    rfl (localMapped 16 8 (by omega))
    (by rw [show (BitVec.ofNat 64 child+48 : BitVec 64)=.ofNat 64 (child+48) from by rw [BitVec.ofNat_add]; rfl]
        exact old_parent_mapped held.pending related named)
    (by rw [show (BitVec.ofNat 64 base+8 : BitVec 64)=.ofNat 64 (base+8) from by rw [BitVec.ofNat_add]; rfl]
        exact freshMapped 8 (by omega))
    (by rw [show (BitVec.ofNat 64 base+16 : BitVec 64)=.ofNat 64 (base+16) from by rw [BitVec.ofNat_add]; rfl]
        exact freshMapped 16 (by omega))

end

#print axioms cover_apart
#print axioms cover_linked
end Binary.Statements.C1.Proof
