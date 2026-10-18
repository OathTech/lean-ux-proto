import PairInsertWalkSites

namespace Binary.Pair.Insert
open TrustBase CommonBitsCoverage
local instance : Labels := Image.linkedLabels

def comparedIndex (locked : Bool) (s : MachineData) : Nat :=
  (s.regs.get (.low (if locked then .r15 else .r14) .W32)).toNat

def collisionPC (locked : Bool) : Int64 := codeEntry+(if locked then 0x18f else 0x6f)

theorem walk_compare (fetch : Int64 → Option Decoded) (decoder : IndexInsertDecoderAgreement fetch)
    {n o c initial ra p shadow s} (core : Core n o c initial ra p shadow s) (locked : Bool) :
    Eventually (instructionStep fetch) (fun t =>
      t.pc=(if (s.regs.get (.low .r13 .W32)).toNat==comparedIndex locked s
        then collisionPC locked else walkPC locked 0xb9) ∧
      Core n o c initial ra p shadow t.data ∧ t.data.regs=s.regs) ⟨s,walkPC locked 0xb4⟩ := by
  have region : Eventually (instructionStep fetch) (fun t =>
      t.data.regs=s.regs ∧ t.data.dmem=s.dmem ∧
      t.pc=(if (s.regs.get (.low .r13 .W32)).toNat==comparedIndex locked s
        then collisionPC locked else walkPC locked 0xb9)) ⟨s,walkPC locked 0xb4⟩ := by
    cases locked with
    | false => exact region_eventually (IndexInsertImage.Insert_rb4_layout.agreement decoder) s _ (first_compare s)
    | true => exact region_eventually (IndexInsertImage.Insert_r119_layout.agreement decoder) s _ (second_compare s)
  apply eventually_weaken (instructionStep fetch) _ _ _ _ region
  rintro t ⟨regs,heap,pc⟩
  exact ⟨pc,core.same regs heap,regs⟩

theorem walk_advance (fetch : Int64 → Option Decoded) (decoder : IndexInsertDecoderAgreement fetch)
    {n o c initial ra p shadow s} (core : Core n o c initial ra p shadow s) (locked : Bool)
    (next : BitVec 64) (read : s.dmem.loadInt (s.regs.rbx.toBitVec+8) 8=some next.toNat) :
    Eventually (instructionStep fetch) (fun t =>
      t.pc=(if next=0 then walkPC locked 0xc7 else walkPC locked 0x8d) ∧
      Core n o c initial ra p shadow t.data ∧
      t.data.regs={s.regs with rbx := .ofBitVec next}) ⟨s,walkPC locked 0xbe⟩ := by
  have region : Eventually (instructionStep fetch) (fun t =>
      t.data.regs={s.regs with rbx := .ofBitVec next} ∧ t.data.dmem=s.dmem ∧
      t.pc=(if next=0 then walkPC locked 0xc7 else walkPC locked 0x8d)) ⟨s,walkPC locked 0xbe⟩ := by
    cases locked with
    | false => exact region_eventually (IndexInsertImage.Insert_rbe_layout.agreement decoder) s _ (first_advance s next read)
    | true => exact region_eventually (IndexInsertImage.Insert_r123_layout.agreement decoder) s _ (second_advance s next read)
  apply eventually_weaken (instructionStep fetch) _ _ _ _ region
  rintro t ⟨regs,heap,pc⟩
  have template : Core n o c initial ra p shadow {s with regs := {s.regs with rbx := .ofBitVec next}} :=
    ⟨core.stack,core.table,core.owner,core.memory,core.frame,core.outside⟩
  exact ⟨pc,template.same regs heap,regs⟩

#print axioms walk_compare
#print axioms walk_advance
end Binary.Pair.Insert
