import TrustBase

namespace Binary.Callback
local instance : Labels := Image.linkedLabels

/-- A proof-side restriction on the states at which actual instructions
execute. It preserves the same instruction semantics and all undefined choices. -/
def guardedStep (fetch : Int64 → Option Decoded) (guard : MachineState → Prop)
    (s : MachineState) (post : MachineState → Prop) : Prop :=
  guard s ∧ instructionStep fetch s post

/-- Retain the interior invariant while lifting an endpoint derivation to
its actual history. The endpoint itself need not satisfy the interior guard. -/
theorem guarded_history (fetch : Int64 → Option Decoded) (guard P : MachineState → Prop)
    (s : MachineState) (run : Eventually (guardedStep fetch guard) P s) :
    ∀ front, (∀ q ∈ front, guard q) →
      Eventually (historyStep fetch)
        (fun t => P t.machine ∧ ∀ q ∈ t.history.dropLast, guard q) ⟨s,front++[s]⟩ := by
  induction run with
  | done s hp =>
    intro front hfront
    apply Eventually.done
    simpa using And.intro hp hfront
  | step s mid step _ ih =>
    intro front hfront
    apply step_cps
    apply instruction_mono fetch s _ _ _ step.2
    intro next hn
    have more : ∀ q ∈ front++[s], guard q := by
      intro q hq
      rcases List.mem_append.mp hq with prior | now
      · exact hfront q prior
      · simpa only [List.mem_singleton.mp now] using step.1
    simpa only [historyStep, List.append_assoc] using ih next hn (front++[s]) more

/-- Fixed leaf-service stack depth is useful to callers' first-return proofs;
no anchored function instruction executes inside the service. -/
def leafGuard (rsp : UInt64) (s : MachineState) : Prop :=
  s.data.regs.rsp=rsp ∧ Image.fetch s.pc=none

theorem leaf_step {rsp : UInt64} {P : MachineState → Prop}
    {s : MachineData} {pc : Int64} {i : Instr} {n : Nat}
    (here : ServiceImage.fetch pc=some ⟨i,n⟩) (positive : 0<n)
    (stack : s.regs.rsp=rsp) (outside : Image.fetch pc=none)
    (run : (i.interp s ⟨pc,pc+.ofNat n⟩
      (fun d => .done ⟨d,pc+.ofNat n⟩) (fun p d => .done ⟨d,p⟩)).All
        (Eventually (guardedStep ServiceImage.fetch (leafGuard rsp)) P)) :
    Eventually (guardedStep ServiceImage.fetch (leafGuard rsp)) P ⟨s,pc⟩ := by
  apply step_cps
  exact ⟨⟨stack,outside⟩,by simpa only [instructionStep,here] using And.intro positive run⟩

theorem leaf_return {rsp : UInt64} (pc : Int64) (size : Nat) (s : MachineData) (ra : UInt64)
    (here : ServiceImage.fetch pc=some ⟨.regular .W64 .W64 .ret,size⟩)
    (positive : 0<size) (outside : Image.fetch pc=none)
    (stack : s.regs.rsp=rsp)
    (read : s.dmem.loadInt s.regs.rsp.toBitVec 8=some (ra.toNat : Int))
    (P : MachineState → Prop)
    (post : P ⟨{s with regs := {s.regs with rsp := s.regs.rsp+8}},ra.toInt64⟩) :
    Eventually (guardedStep ServiceImage.fetch (leafGuard rsp)) P ⟨s,pc⟩ := by
  apply leaf_step here positive stack outside
  simp [Instr.interp,Operation.interp,MachineData.load,Reg64s.get64,
    Reg64s.set64,read,Effects.All]
  exact .done _ post

theorem leaf_contract {fetch address ready writes effect}
    (run : ∀ s ra, s.pc=address → ready s → TrustBase.EntryFrame s ra →
      Eventually (guardedStep fetch (leafGuard s.data.regs.rsp))
        (fun t => TrustBase.Returned s t ra ∧ EqualOutside (writes s) s.data.dmem t.data.dmem ∧ effect s t) s) :
    TrustBase.ServiceReturns fetch address ready writes effect := by
  intro s ra pc ready frame
  have history := guarded_history fetch _ _ s (run s ra pc ready frame) [] (by simp)
  apply eventually_weaken (historyStep fetch) _ _ _ _ history
  rintro t ⟨⟨returned,outside,effect⟩,interior⟩
  exact ⟨returned,outside,effect,fun q hq => (interior q hq).2⟩

#print axioms guarded_history
#print axioms leaf_contract
end Binary.Callback
