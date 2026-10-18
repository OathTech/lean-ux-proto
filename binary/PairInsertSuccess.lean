import PairInsertFinish

namespace Binary.Pair.Insert
open Leanux Leanux.WG TrustBase CommonBitsCoverage Index
local instance : Labels := Image.linkedLabels

def ReturnPost (n : Names) (o : Offsets) (c : Context) (initial : MachineState)
    (ra : UInt64) (d : Device) (index : Nat) (t : MachineState) : Prop :=
  Returned initial t ra ∧ t.data.regs.rax.toNat=index ∧
    MemoryReady c initial ra (savedWords initial.data) .enabled t.data.dmem ∧
    Corresponds n o t.data.dmem d ∧ Remove.ownership n o t.data.dmem=.ok (Remove.targetOwnership d)

/-- Successful insertion suffix, ending at the caller's return address with
the reconstructed table, ownership, return value and callback resources. -/
theorem insert_success (fetch : Int64 → Option Decoded) (decoder : IndexInsertDecoderAgreement fetch)
    (trace : TracePcContract fetch) (bh : BhEnableContract fetch)
    {n o c initial ra shadow s d} (facts : FrameFacts n o c initial ra)
    (core : Core n o c initial ra .inner shadow s) (focus : InsertFocus n o shadow)
    (ready : RetryData n o shadow d focus.fresh.owner focus.fresh.base)
    (storage : storageCheck n o=true) (table : initial.data.regs.rdi.toNat=n.table)
    (owner : initial.data.regs.rsi.toNat=focus.fresh.base) (registers : WalkRegisters true focus.index s) :
    Eventually (instructionStep fetch)
      (ReturnPost n o c initial ra {d with indexTable := ⟨focus.index,focus.fresh.owner⟩::d.indexTable} focus.index)
      ⟨s,codeEntry+0x136⟩ := by
  have validated := (reconstruct_components ready.related).1
  have layout := (validate_basic validated).1
  have body := prepend fetch decoder trace facts core layout focus ready.resident table owner registers
  apply eventually_trans (instructionStep fetch) _ _ _ body
  rintro inserted ⟨pc,core⟩
  have indexRead : word focus.after "insert.index" (focus.fresh.base+o.index) 4=.ok focus.index := by
    have slot : DataSlot n o (focus.fresh.base+o.index) 4 := by
      rw [layout.index]
      exact .entry focus.fresh.owner focus.fresh.base 28 4 focus.fresh.named (.inr (.inr rfl))
    rw [focus.read_data layout storage _ slot]
    exact focus.indexRead
  have returning := finish fetch decoder bh facts core layout focus.fresh.named owner indexRead
  apply eventually_weaken (instructionStep fetch) _ _ _ _ (at_pc pc returning)
  rintro final ⟨returned,memory,frame,result⟩
  refine ⟨returned,result,memory,frame.reconstruct (focus.reconstruct ready.related storage),?_⟩
  rw [←frame.ownership layout]
  exact focus.ownership validated storage ready.owned

#print axioms insert_success
end Binary.Pair.Insert
