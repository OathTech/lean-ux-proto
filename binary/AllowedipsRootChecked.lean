import AllowedipsRootPhaseInputs
import AllowedipsRootReconstruct

namespace Binary.Pair.Allowedips.Root
open Leanux Leanux.WG Binary.Pair.Allowedips.Model
local instance : Labels := Image.linkedLabels

theorem BoundaryFields.query_apart {names o world machine key cidr pid}
    (fields : BoundaryFields names o world machine key cidr pid) :
    ∀ a, InRange machine.data.regs.r13.toBitVec
      (if machine.data.regs.rbp.toNat=32 then 4 else 8) a →
      ¬InRange (.ofNat 64 (machine.data.regs.rbx.toNat+32)) 16 a := by
  intro a read written
  apply fields.separated (machine.data.regs.r13.toNat,machine.data.regs.rbp.toNat/8) (by simp) a
  · obtain ⟨i,bound,equal⟩ := read
    refine ⟨i,?_,?_⟩
    · rcases fields.family with four|six <;> simp_all <;> omega
    · simpa only [ofNat_uint64] using equal
  · obtain ⟨i,bound,equal⟩ := written
    refine .inl ⟨32+i,by omega,?_⟩
    simpa only [BitVec.ofNat_add,BitVec.add_assoc] using equal

/-- The tested post-allocation boundary implies the actual Kraken segment,
restoring full reconstruction and the heap assertion. There are no assumed
phase executions or intermediate reads in this statement. This is still an
internal segment, not a theorem from function entry to ABI return. -/
theorem initialization_checked (fetch : Int64 → Option Decoded)
    (decoder : TrustBase.AllowedipsMutationDecoderAgreement fetch)
    {names world machine key cidr pid}
    (checked : boundary names nodeOffsets world machine key cidr pid=.ok ()) :
    ∃ d owner, world.wg.dev=some d ∧ d.peers.get? pid=some owner ∧
      Eventually (instructionStep fetch) (fun t =>
        t.pc=AllowedipsMutationImage.Add.entry+0x549 ∧ OutputRegisters machine.data.regs t.data.regs ∧
        EqualOutside (Writes (names.allocated machine.data.regs.rbx.toNat) machine.data.regs.rbx.toNat
          (names.table+(if machine.data.regs.rbp.toNat==32 then 0 else 8))) machine.data.dmem t.data.dmem ∧
        Corresponds (names.allocated machine.data.regs.rbx.toNat) nodeOffsets t.data.dmem
          (emptyInstalled d (machine.data.regs.rbp.toNat==32) key cidr pid owner) ∧
        heap (names.allocated machine.data.regs.rbx.toNat)
          (target (emptyInstalled d (machine.data.regs.rbp.toNat==32) key cidr pid owner)) t.data.dmem=.ok ()) machine := by
  have fields := boundary_fields checked
  obtain ⟨d,device,related,shape⟩ := assertAt_ok fields.asserted
  obtain ⟨owner,peerNamed,hasPeer⟩ := fields.peer related
  obtain ⟨positive,aligned,extent,fresh,tableApart⟩ := allocated_facts fields.allocated
  obtain ⟨phases⟩ := phases_of_boundary fields related peerNamed hasPeer
  let v4 := machine.data.regs.rbp.toNat==32
  have width : machine.data.regs.rbp.toNat=rootWidth v4 := by
    rcases fields.family with four|six <;> simp_all [v4,rootWidth]
  have empty : (if v4 then d.peerAllowedips.root4 else d.peerAllowedips.root6)=none := by
    obtain ⟨d',device',empty⟩ := fields.device
    have same := Option.some.inj (device.symm.trans device')
    subst d'
    simpa only [v4,beq_iff_eq] using empty
  have saved : word phases.copied "root.slot" (machine.data.regs.rsp.toNat+8) 8=
      .ok (names.table+(if v4 then 0 else 8)) := by
    simpa only [v4,beq_iff_eq] using phases.saved
  have execution := initialization_segment fetch decoder related shape empty positive aligned extent fresh tableApart
    peerNamed hasPeer width fields.cidrBound
    (fields.zero_word (Nat.le_of_lt extent) _ 8 8 (by decide))
    (fields.zero_word (Nat.le_of_lt extent) _ 16 8 (by decide))
    (fields.zero_word (Nat.le_of_lt extent) _ 56 8 (by decide))
    (fields.zero_word (Nat.le_of_lt extent) _ 64 8 (by decide))
    phases.attachment phases.header phases.query fields.query_apart phases.copy saved phases.publish
  refine ⟨d,owner,device,hasPeer,?_⟩
  have entry : machine=⟨machine.data,AllowedipsMutationImage.Add.entry+0x443⟩ := by
    cases machine
    simp only [MachineState.mk.injEq,true_and]
    exact fields.pc
  exact entry.symm ▸ execution

#print axioms initialization_checked
end Binary.Pair.Allowedips.Root
