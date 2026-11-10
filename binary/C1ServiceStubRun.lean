import C1ServiceStub

/-! Result C1, work package 4: the stub's instructions, executed. -/
namespace Binary.Statements.C1.Stub
open Leanux Leanux.WG Binary.Pair Binary.Pair.Allowedips Binary.TrustBase
open Binary.CommonBitsCoverage Binary.Statements.C1 Binary.Statements.C1.Proof
local instance : Labels := Image.linkedLabels

theorem step_instr {fetch : Int64 → Option Decoded} {P : MachineState → Prop}
    {s : MachineData} {pc : Int64} {i : Instr} {n : Nat}
    (here : fetch pc = some ⟨i,n⟩) (positive : 0<n)
    (run : (i.interp s ⟨pc,pc+.ofNat n⟩
      (fun d => .done ⟨d,pc+.ofNat n⟩) (fun p d => .done ⟨d,p⟩)).All
        (Eventually (instructionStep fetch) P)) :
    Eventually (instructionStep fetch) P ⟨s,pc⟩ := by
  apply step_cps
  simpa only [instructionStep,here] using And.intro positive run

local macro "stub_instr" agree:ident : tactic => `(tactic|
  (apply step_instr ($agree _ _ (by rfl)) (by decide)
   simp only [Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
     MachineData.load, MachineData.store, MachineData.set, MachineData.setReg,
     AddrExpr.interp, ConstExpr.interp, Reg64s.get, Reg64s.get64, Reg64s.set,
     Reg64s.set64, Reg.base, Reg.offset, BitVec.drop, BitVec.take,
     BitVec.toAddressSize, Effects.All]))

theorem branch_taken.{u} {α : Sort u} {condition : Prop} [Decidable condition] {first second : α}
    (holds : condition) : (if condition then first else second) = first := by
  simp [holds]

theorem branch_skipped.{u} {α : Sort u} {condition : Prop} [Decidable condition] {first second : α}
    (fails : ¬condition) : (if condition then first else second) = second := by
  simp [fails]

theorem return_pc (ra : UInt64) : Int64.ofInt (ra.toNat : Int) = .ofBitVec ra.toBitVec := by
  apply Int64.toBitVec_inj.mp
  simp [Int64.toBitVec_ofInt]

/-- A load whose result is known, then the continuation. -/
local macro "stub_load" read:ident : tactic => `(tactic|
  (simp [BitVec.signed]
   rw [$read:ident]
   simp only [Effects.All]))

/-- The six instructions both paths share, up to the branch. -/
local macro "stub_prefix" agree:ident cache:ident stateRead:ident tableRead:ident : tactic => `(tactic|
  (stub_instr $agree
   simp [$cache:ident, state, BitVec.signed]
   rw [$stateRead:ident]
   simp only [Effects.All]
   stub_instr $agree
   simp [BitVec.signed]
   stub_instr $agree
   stub_load $stateRead
   stub_instr $agree
   stub_load $tableRead
   stub_instr $agree
   simp [BitVec.signed]
   stub_instr $agree
   simp))

set_option maxRecDepth 4096 in -- the interpreter's terms, as in the landed callback proofs
set_option maxHeartbeats 4000000 in -- sixteen concrete executions of the twelve instructions
/-- The allocation stub, executed: with `count` answers given and the pending
outcome byte `code`, it stores `count+1` in the state byte and returns object
`count` (outcome 1) or NULL (outcome 0), changing nothing else in memory. -/
theorem alloc_run (fetch : Int64 → Option Decoded)
    (agree : ∀ pc i, Stub.fetch pc = some i → fetch pc = some i)
    (d : MachineData) (ra : UInt64) (count : Nat) (small : count < slots) (code : Int)
    (binary : code = 0 ∨ code = 1)
    (cache : d.regs.rdi = UInt64.ofNat state)
    (stateRead : d.dmem.loadInt (.ofNat 64 state) 1 = some (count : Int))
    (tableRead : (d.dmem.storeInt (.ofNat 64 state) 1 ((count : Int)+1)).loadInt
      (.ofNat 64 (table+count)) 1 = some code)
    (retRead : (d.dmem.storeInt (.ofNat 64 state) 1 ((count : Int)+1)).loadInt d.regs.rsp.toBitVec 8 =
      some (ra.toNat : Int))
    (P : MachineState → Prop)
    (finish : ∀ t, Returned ⟨d,allocEntry⟩ t ra →
      t.data.dmem = d.dmem.storeInt (.ofNat 64 state) 1 ((count : Int)+1) →
      t.data.regs.rax.toNat = (if code = 1 then slot count else 0) →
      t.data.system = d.system → P t) :
    Eventually (instructionStep fetch) P ⟨d,allocEntry⟩ := by
  have target : label "L_ffffffff81196d4d" = allocEntry + 3 + 3 + 2 + 7 + 3 + 2 + 8 + 8 + 8 + 1 := by
    decide +kernel
  simp only [slots] at small
  have cases : count = 0 ∨ count = 1 ∨ count = 2 ∨ count = 3 ∨ count = 4 ∨ count = 5 ∨ count = 6 ∨
      count = 7 := by omega
  rcases binary with rfl | rfl
  · rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp [state, table] at stateRead tableRead retRead
      stub_prefix agree cache stateRead tableRead
      rw [branch_taken (by decide), target]
      simp only [Effects.All]
      stub_instr agree
      intro undefined
      stub_instr agree
      stub_load retRead
      apply Eventually.done
      apply finish
      · simp [Returned, return_pc]
      · rfl
      · simp
      · rfl
  · rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp [state, table] at stateRead tableRead retRead
      stub_prefix agree cache stateRead tableRead
      rw [branch_skipped (by decide)]
      simp only [Effects.All]
      stub_instr agree
      simp [BitVec.signed]
      stub_instr agree
      simp [BitVec.signed]
      stub_instr agree
      simp [BitVec.signed]
      stub_instr agree
      stub_load retRead
      apply Eventually.done
      apply finish
      · simp [Returned, return_pc]
      · rfl
      · simp [slot, objects]
        rfl
      · rfl

/-- The release stub, executed: it returns and changes nothing. -/
theorem free_run (fetch : Int64 → Option Decoded)
    (agree : ∀ pc i, Stub.fetch pc = some i → fetch pc = some i)
    (d : MachineData) (ra : UInt64)
    (retRead : d.dmem.loadInt d.regs.rsp.toBitVec 8 = some (ra.toNat : Int))
    (P : MachineState → Prop)
    (finish : ∀ t, Returned ⟨d,freeEntry⟩ t ra → t.data.dmem = d.dmem → P t) :
    Eventually (instructionStep fetch) P ⟨d,freeEntry⟩ := by
  stub_instr agree
  stub_load retRead
  apply Eventually.done
  apply finish
  · simp [Returned, return_pc]
  · rfl

#print axioms alloc_run
#print axioms free_run

end Binary.Statements.C1.Stub
