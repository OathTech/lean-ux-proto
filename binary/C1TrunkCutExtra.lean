import C1TrunkRoot
import C1Cut
/-! Result C1, package 2: the six facts package 3 needs of the cut state
beside `NodeCut` (coordinator's decision of 2026-11-10 on the internal
interface). `CutExtra` is in `C1Cut` since the integration (the package
carried a verbatim copy of package 3's definition on its branch).

`cutExtra_of_frame` proves all six for any state of `add`'s frame at which
`r13` and `rbp` are what the prologue left and the stack word at `rsp+8` is
the prologue's: none is false of the image, and none needs a premise beyond
`Inv` and `insertReady`. The walk from `add`'s entry to `add+0x156` (which
must supply those three facts at the cut, from the landed loop's frame) is
not in the package, so `TrunkToNodePlus` is not proved here. -/
namespace C1Trunk
open Binary Binary.Pair Binary.Pair.Allowedips Binary.AllowedipsMutationImage
open Binary.TrustBase Binary.CommonBitsCoverage Binary.Instrumentation
open Binary.Statements.C1 Binary.Statements.C1.Proof Leanux Leanux.WG
local instance : Labels := Image.linkedLabels

section
variable {L : Statements.C1.Layout} {A : Allocator} {c : Context}
  {s : MachineState} {w : World} {v4 : Bool} {key cidr pid : Nat} {ra : UInt64}
  {names : Allowedips.Names} {stream : List HiddenRecord} {d : Device} {seq : BitVec 64}
  {a : MachineData}

theorem cutExtra_of_frame (trunk : Trunk L A c s w v4 key cidr pid ra names stream d seq a)
    (family : Nat) (families : family = if v4 then 4 else 6) (e : MachineState)
    (stackE : e.data.regs.rsp = a.regs.rsp - 96)
    (r13 : e.data.regs.r13 = a.regs.rdx)
    (bits : e.data.regs.rbp.toNat = if v4 then 32 else 128)
    (slotWord : e.data.dmem.loadInt (a.regs.rsp.toBitVec-104+.ofNat 64 (8+8)) 8 =
      (memory a 8).loadInt (a.regs.rsp.toBitVec-104+.ofNat 64 (8+8)) 8) :
    CutExtra L s e family := by
  have fs := frameSize_range v4
  have wide := window_wide A
  have room' : insertWindow + A.depth ≤ s.data.regs.rsp.toBitVec.toNat := trunk.sep.room
  have window : insertWindow = 200 := rfl
  have stackAt := trunk.atAdd.stackAt
  have espBV : e.data.regs.rsp.toBitVec = s.data.regs.rsp.toBitVec - .ofNat 64 (frameSize v4 + 96) := by
    rw [stackE]
    show a.regs.rsp.toBitVec - BitVec.ofNat 64 96 = _
    rw [stackAt, sub_sub_ofNat]
  have espNat : e.data.regs.rsp.toNat = s.data.regs.rsp.toBitVec.toNat - (frameSize v4 + 96) := by
    show e.data.regs.rsp.toBitVec.toNat = _
    rw [espBV, toNat_sub_ofNat _ _ (by omega)]
  have r13Nat : e.data.regs.r13.toNat = s.data.regs.rsp.toBitVec.toNat - (if v4 then 36 else 48) := by
    show e.data.regs.r13.toBitVec.toNat = _
    have at' : e.data.regs.r13.toBitVec = s.data.regs.rsp.toBitVec - .ofNat 64 (if v4 then 36 else 48) := by
      rw [r13, trunk.atAdd.query]
      cases v4 <;> rfl
    rw [at', toNat_sub_ofNat _ _ (by split <;> omega)]
  have tableTop := (Root.table_valid_geometry (related_valid trunk.relatedA)).1
  have small : (if (if v4 then 32 else 128) = 32 then 0 else 8) ≤ 8 := by
    repeat' split
    all_goals omega
  have argSlot : a.regs.rdi.toNat = names.table+(if (if v4 then 32 else 128) = 32 then 0 else 8) := by
    have h := congrArg BitVec.toNat trunk.slotAt
    have lt : names.table+(if (if v4 then 32 else 128) = 32 then 0 else 8) < 2^64 := by omega
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt lt] at h
    exact h
  have sizes : frameSize v4 = (if v4 then 48 else 56) := rfl
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · show e.data.regs.rsp.toNat + 48 ≤ s.data.regs.rsp.toBitVec.toNat
    rw [espNat]
    omega
  · show s.data.regs.rsp.toBitVec.toNat + 48 ≤ e.data.regs.rsp.toNat + insertWindow
    rw [espNat, window]
    omega
  · rw [bits, families]
    cases v4 <;> rfl
  · rw [espNat, r13Nat, sizes]
    cases v4
    · simp only [Bool.false_eq_true, ↓reduceIte]
      omega
    · simp only [↓reduceIte]
      omega
  · show e.data.regs.r13.toNat + e.data.regs.rbp.toNat/8 ≤ s.data.regs.rsp.toBitVec.toNat
    rw [r13Nat, bits]
    cases v4
    · simp only [Bool.false_eq_true, ↓reduceIte]
      omega
    · simp only [↓reduceIte]
      omega
  · have address : e.data.regs.rsp.toBitVec + 8 = a.regs.rsp.toBitVec-104+.ofNat 64 (8+8) := by
      rw [stackE]
      show a.regs.rsp.toBitVec - 96#64 + 8#64 = a.regs.rsp.toBitVec - 104#64 + 16#64
      bv_omega
    rw [address, slotWord]
    have read : (memory a 8).loadInt (a.regs.rsp.toBitVec-104+.ofNat 64 (8+8)) 8 =
        some (((words a)[6]?.getD 0).toNat : Int) := by
      have r := memory_read a 8 6 (by decide) (by decide) (by decide)
      rw [slot_base a 6 (by decide)] at r
      exact r
    rw [read]
    show some ((a.regs.rdi.toNat : Nat) : Int) = _
    rw [argSlot, trunk.table, families]
    cases v4 <;> rfl
end

#print axioms cutExtra_of_frame
end C1Trunk
