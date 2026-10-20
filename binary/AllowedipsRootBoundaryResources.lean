import AllowedipsRootBoundaryFields
import AllowedipsRootAttachTotal

namespace Binary.Pair.Allowedips.Root
open Leanux Leanux.WG

theorem BoundaryFields.peer {names o world machine key cidr pid d}
    (fields : BoundaryFields names o world machine key cidr pid)
    (related : Corresponds names o machine.data.dmem d) :
    ∃ owner, (pid,machine.data.regs.r14.toNat) ∈ names.trie.peers ∧ d.peers.get? pid=some owner := by
  have address := fields.owner
  simp only [Trie.address] at address
  cases found : names.trie.peers.find? (·.1==pid) with
  | none => rw [found] at address; cases address
  | some pair =>
    rw [found] at address
    have base : pair.2=machine.data.regs.r14.toNat := Except.ok.inj address
    have identity : pair.1=pid := by simpa using List.find?_some found
    have named : (pid,machine.data.regs.r14.toNat) ∈ names.trie.peers := by
      simpa only [←base,←identity] using List.mem_of_find?_eq_some found
    obtain ⟨⟨actual,count,entries⟩,member,decoded⟩ := (reconstruct_fields related).peers.left _ named
    have sameId : pid=actual := (decodePeer_fields decoded).1
    obtain ⟨⟨current,peer⟩,member,equal⟩ := List.mem_map.mp member
    have currentId : current=actual := congrArg Prod.fst equal
    refine ⟨peer,named,?_⟩
    have present := Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp member
    simpa only [Std.TreeMap.get?_eq_getElem?,currentId,←sameId] using present

theorem BoundaryFields.zero_word {names o world machine key cidr pid}
    (fields : BoundaryFields names o world machine key cidr pid)
    (extent : machine.data.regs.rbx.toNat+72≤2^64)
    (path : String) (offset size : Nat) (within : offset+size≤72) :
    word machine.data.dmem path (machine.data.regs.rbx.toNat+offset) size=.ok 0 := by
  have full := Trie.readNat_loadInt fields.zero
  have part := MemoryBytes.loadInt_subword _ _ _ _ full offset size within
  have part : machine.data.dmem.loadInt (.ofNat 64 (machine.data.regs.rbx.toNat+offset)) size=some 0 := by
    simpa [BitVec.ofNat_add] using part
  apply Trie.word_of_loadInt _ (by omega)
  exact part

/-- Covers the already proved store footprint. The fresh allocation cover also
supports subword initialization facts before a reconstructed record exists. -/
theorem writeSpans_cover (names : Names) (s : MachineData) :
    Covers (writeSpans names s)
      (fun a => InRange (.ofNat 64 s.regs.rbx.toNat) 72 a ∨ ListWrites names a ∨
        InRange (.ofNat 64 (names.table+(if s.regs.rbp.toNat=32 then 0 else 8))) 8 a) := by
  intro a inside
  rcases inside with fresh | list | root
  · exact ⟨(s.regs.rbx.toNat,72),List.mem_append_left _ (List.mem_append_left _ (by simp)),fresh⟩
  · rcases list with ⟨link,slot,offset,which,inside⟩
    have within : InRange (.ofNat 64 link) 16 a := by
      obtain ⟨i,bound,equal⟩ := inside
      refine ⟨offset+i,by rcases which with rfl|rfl <;> omega,?_⟩
      simpa only [BitVec.ofNat_add,BitVec.add_assoc] using equal
    cases slot with
    | node named =>
      refine ⟨_,List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨_,named,rfl⟩)),within⟩
    | peer named =>
      exact ⟨_,List.mem_append_right _ (List.mem_map.mpr ⟨_,named,rfl⟩),within⟩
  · refine ⟨(names.table+(if s.regs.rbp.toNat=32 then 0 else 8),8),
      List.mem_append_left _ (List.mem_append_left _ (by simp [beq_iff_eq])),?_⟩
    simpa only [Span.contains,beq_iff_eq] using root

def EntryWrites (names : Names) (s : MachineData) (a : BitVec 64) : Prop :=
  InRange (.ofNat 64 s.regs.rbx.toNat) 72 a ∨ ListWrites (names.allocated s.regs.rbx.toNat) a ∨
    InRange (.ofNat 64 (names.table+(if s.regs.rbp.toNat=32 then 0 else 8))) 8 a

theorem BoundaryFields.separated {names o world machine key cidr pid}
    (fields : BoundaryFields names o world machine key cidr pid) :
    ∀ (span : Span), span ∈ [(machine.data.regs.r13.toNat,machine.data.regs.rbp.toNat/8),
      (machine.data.regs.rsp.toNat+8,8),(machine.data.regs.rsp.toNat+16,4)] →
      ∀ a, span.contains a → ¬EntryWrites names machine.data a := by
  intro span member a read written
  obtain ⟨write,atWrite,inside⟩ := writeSpans_cover (names.allocated machine.data.regs.rbx.toNat) machine.data a written
  exact spansApart_sound fields.apart member atWrite read inside

#print axioms BoundaryFields.zero_word
#print axioms BoundaryFields.separated
end Binary.Pair.Allowedips.Root
