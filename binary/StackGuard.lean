import CallbackContracts
import RegionExecution

namespace Binary.Callback
local instance : Labels := Image.linkedLabels

/-- Interior stack exclusion is stronger than merely avoiding the return PC.
It still applies when a supplied return PC aliases a code address. -/
def StackGuard (outer : UInt64) (s : MachineState) : Prop := s.data.regs.rsp≠outer+8

/-- Instruction framing in CPS, retaining the stack effect while changing
continuations. This is a semantic lemma, not a certificate validation step. -/
def StackCps (i : Instr) (delta : UInt64 → UInt64) : Prop :=
  ∀ (s : MachineData) (p : Std.Rco Int64)
    (next₁ next₂ : MachineData → Effects)
    (jump₁ jump₂ : Int64 → MachineData → Effects) (P Q : MachineState → Prop),
    (∀ d, d.regs.rsp=delta s.regs.rsp → (next₁ d).All P → (next₂ d).All Q) →
    (∀ pc d, d.regs.rsp=delta s.regs.rsp → (jump₁ pc d).All P → (jump₂ pc d).All Q) →
    (i.interp s p next₁ jump₁).All P → (i.interp s p next₂ jump₂).All Q

/-- Only interior points require the guard. The endpoint may be the return. -/
inductive StackPath (outer : UInt64) : List (Kraken.Sized Directive) → UInt64 → Prop
  | nil (sp) : StackPath outer [] sp
  | cons (i : Instr) (n : Nat) (tail : List (Kraken.Sized Directive)) (sp : UInt64)
      (delta : UInt64 → UInt64) (guard : sp≠outer+8) (effect : StackCps i delta)
      (rest : StackPath outer tail (delta sp)) :
      StackPath outer (⟨.instr i,n⟩::tail) sp

theorem region_guarded {fetch pc code outer}
    (layout : LaidOut fetch pc code) (s : MachineData) (P : MachineState → Prop)
    (path : StackPath outer code s.regs.rsp)
    (run : (Directives.interp code s pc (fun p d => .done ⟨d,p⟩)).All P) :
    Eventually (guardedStep fetch (StackGuard outer)) P ⟨s,pc⟩ := by
  induction layout generalizing s with
  | nil pc => exact .done _ run
  | cons pc i n tail positive here mono rest ih =>
    cases path with
    | cons _ _ _ _ delta guard effect path =>
      apply step_cps
      refine ⟨guard,?_⟩
      simp only [instructionStep,here]
      refine ⟨positive,?_⟩
      apply effect s ⟨pc,pc+.ofNat n⟩
        (fun d => Directives.interp tail d (pc+.ofNat n) (fun p d => .done ⟨d,p⟩))
        _ (fun p d => .done ⟨d,p⟩) _ P _
      · intro d stack h
        apply ih d
        · rw [stack]; exact path
        · exact h
      · exact fun p d _ h => .done _ h
      · exact run

macro "stack_effect" : tactic => `(tactic|
  (try simp only [Option.getD]
   intro s p n₁ n₂ j₁ j₂ P Q hn hj
   simp only [Instr.interp,Operation.interp,RegOrMem.interp,Operand.interp,
     MachineData.load,MachineData.store,MachineData.set,MachineData.setReg,
     AddrExpr.interp,ConstExpr.interp,Reg64s.get,Reg64s.get64,Reg64s.set,Reg64s.set64,
     Reg.base,Reg.offset,BitVec.take,BitVec.drop,RelRegOrMem.interp,Effects.All,
     Width.bits,Width.bytes,Width.bytesv,Nat.sub_zero,BitVec.extractLsb'_eq_self]
   iterate 30 (all_goals first
     | exact hn _ (by rfl)
     | exact hj _ _ (by rfl)
     | exact False.elim
     | (change (∀ _,_) → (∀ _,_); intro h v; specialize h v; revert h)
     | (split <;> simp_all only [Effects.All])
     | skip)))

macro "stack_not_return" : tactic => `(tactic|
  (intro equal
   have values := congrArg UInt64.toBitVec equal
   simp [UInt64.toBitVec_sub,UInt64.toBitVec_add,BitVec.sub_eq_add_neg,BitVec.add_assoc] at values))

syntax "stack_path" : tactic
open Lean Elab Tactic Meta in
elab_rules : tactic
 | `(tactic| stack_path) => withMainContext do
  let target ← getMainTarget
  let code ← whnf target.getAppArgs[1]!
  if code.isAppOf ``List.nil then
    evalTactic (← `(tactic| exact StackPath.nil _))
  else
    let sized ← whnf code.getAppArgs[1]!
    let directive ← whnf sized.getAppArgs[1]!
    let instruction ← whnf directive.getAppArgs[0]!
    let operation ← whnf instruction.getAppArgs[2]!
    let name := operation.getAppFn.constName!
    let delta ← if name == ``Operation.push || name == ``Operation.call then
        `(term| fun sp : UInt64 => sp-8)
      else if name == ``Operation.pop || name == ``Operation.ret then
        `(term| fun sp : UInt64 => sp+8)
      else `(term| id)
    evalTactic (← `(tactic|
      (refine StackPath.cons _ _ _ _ $delta ?_ ?_ ?_
       · stack_not_return
       · stack_effect; done
       · stack_path)))

#print axioms region_guarded
end Binary.Callback
