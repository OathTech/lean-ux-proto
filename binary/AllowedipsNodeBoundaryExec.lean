import AllowedipsNodeTotal
import AllowedipsNodeEffect
import AllowedipsRootBoundaryResources

namespace Binary.Pair.Allowedips.NodeInit
open Leanux Root AllowedipsMutationImage
local instance : Labels := Image.linkedLabels

private theorem ok_bind (value : α) (f : α → Except ε β) :
    ((Except.ok value : Except ε α) >>= f)=f value := rfl

/-- Every intermediate read/store in the initialization summary is derived
from current resources, without assuming a phase or its result. -/
theorem BoundaryFields.effect_total {names world machine key cidr pid base}
    (fields : BoundaryFields names nodeOffsets world machine key cidr pid base) :
    ∃ memory, effect machine.data=.ok (memory,base) ∧ MappedLe machine.data.dmem memory := by
  obtain ⟨d,_,related,_⟩ := assertAt_ok fields.asserted
  obtain ⟨owner,peerNamed,hasPeer⟩ := Root.peer_of_address fields.owner related
  have allocation (offset size : Nat) (within : offset+size≤72) :
      (machine.data.dmem.loadInt (.ofNat 64 (base+offset)) size).isSome=true := by
    have subword := MemoryBytes.loadInt_subword _ _ _ _ (Trie.readNat_loadInt fields.zero) offset size within
    have loaded : machine.data.dmem.loadInt (.ofNat 64 (base+offset)) size=some 0 := by
      simpa [BitVec.ofNat_add] using subword
    rw [loaded]; rfl
  obtain ⟨attached,attachment,attachedMapped⟩ := attach_total related peerNamed hasPeer fields.family
    fields.cidrBound fields.original fields.bits allocation
    (by simpa only [readNat] using fields.baseRead) (by simpa only [readNat] using fields.cidrRead)
  obtain ⟨initialized,headerCheck,initializedMapped⟩ := header_total (s:=machine.data) (base:=base) (cidr:=cidr)
    (fun offset member => attachedMapped _ _ (fields.stackMapped offset member))
    (attachedMapped _ _ (allocation 24 4 (by decide)))
  have mapped := attachedMapped.trans initializedMapped
  let view : MachineData := {machine.data with regs:={machine.data.regs with rbx:=.ofNat base}}
  have extent := (allocated_facts fields.allocated).2.2.1
  have baseNat : (UInt64.ofNat base).toNat=base := Nat.mod_eq_of_lt (by
    change base+72<2^64 at extent
    omega)
  have query := Placement.queryLocals_fields fields.query
  have readable : if view.regs.rbp.toNat=32 then
      (initialized.loadInt (.ofNat 64 view.regs.r13.toNat) 4).isSome=true else
      (initialized.loadInt (.ofNat 64 view.regs.r13.toNat) 8).isSome=true ∧
        (initialized.loadInt (.ofNat 64 (view.regs.r13.toNat+8)) 8).isSome=true := by
    dsimp only [view]
    by_cases four : machine.data.regs.rbp.toNat=32
    · rw [ite_eq_left four]
      have loaded : machine.data.dmem.loadInt machine.data.regs.r13.toBitVec 4=some (key : Int) := by
        simpa only [AllowedipsChild.QueryWords,four,ite_true] using query
      apply mapped
      rw [ofNat_uint64,loaded]
      rfl
    · rw [ite_eq_right four]
      have loaded : machine.data.dmem.loadInt machine.data.regs.r13.toBitVec 8=some ((key/2^64 : Nat) : Int) ∧
          machine.data.dmem.loadInt (machine.data.regs.r13.toBitVec+8) 8=some ((key%2^64 : Nat) : Int) := by
        simpa only [AllowedipsChild.QueryWords,ite_eq_right four] using query
      constructor
      · apply mapped
        rw [ofNat_uint64,loaded.1]
        rfl
      · apply mapped
        simpa [BitVec.ofNat_add,ofNat_uint64] using Option.isSome_of_eq_some loaded.2
  obtain ⟨memory,copyCheck,copyMapped⟩ := Root.copy_total readable (fun offset size within => by
    simp only [view,baseNat]
    apply mapped
    simpa only [Nat.add_assoc] using allocation (32+offset) size (by omega))
  refine ⟨memory,?_,mapped.trans copyMapped⟩
  simp only [effect,attachment,headerCheck,ok_bind]
  rw [copyCheck]
  rfl

/-- Execution from the tested internal boundary. Full-trie correspondence
awaits publication; this theorem exports the exact tested segment summary. -/
theorem initialization_executes (fetch : Int64 → Option Decoded)
    (decoder : TrustBase.AllowedipsMutationDecoderAgreement fetch)
    {names world machine key cidr pid base}
    (checked : boundary names nodeOffsets world machine key cidr pid=.ok base) :
    ∃ memory, effect machine.data=.ok (memory,base) ∧
      Eventually (instructionStep fetch) (fun t =>
        t.pc=Add.entry+0x1ff ∧ t.data.dmem=memory ∧ registers machine.data.regs t.data.regs base=true ∧
        MappedLe machine.data.dmem t.data.dmem) machine := by
  have fields := boundary_fields checked
  obtain ⟨memory,summary,mapped⟩ := fields.effect_total
  refine ⟨memory,summary,?_⟩
  rw [Placement.at_pc machine _ fields.pc]
  apply eventually_weaken (instructionStep fetch) _ _ _ _ (effect_segment fetch decoder summary)
  rintro t ⟨pc,mem,regs⟩
  exact ⟨pc,mem,regs,mem ▸ mapped⟩

#print axioms initialization_executes
end Binary.Pair.Allowedips.NodeInit
