import Execution

namespace Binary.Sequential

/-- Relational composition for the actual nested-state source loop. Every
iteration executes from the previous machine endpoint. A successful source
run supplies finite iteration, but no binary execution or final relation.
The iteration premise is discharged by the client's physical region proof. -/
theorem forIn_execution [Labels] (fetch : Int64 → Option Decoded)
    {Item Acc Store Ambient Error : Type}
    (body : Item → Acc → StateT Store (StateT Ambient (Except Error)) (ForInStep Acc))
    (R : Acc → Store → Ambient → MachineState → Prop)
    (Open : Acc → Prop)
    (continues : ∀ item acc store ambient next nextStore nextAmbient,
      ((body item acc).run store).run ambient = .ok ((.yield next,nextStore),nextAmbient) → Open next)
    (iteration : ∀ item acc store ambient next nextStore nextAmbient machine,
      ((body item acc).run store).run ambient = .ok ((next,nextStore),nextAmbient) →
      Open acc → R acc store ambient machine →
      Eventually (instructionStep fetch)
        (R (match next with | .done a => a | .yield a => a) nextStore nextAmbient) machine)
    (items : List Item) (acc final : Acc) (store finalStore : Store)
    (ambient finalAmbient : Ambient) (machine : MachineState)
    (accepted : ((forIn items acc body).run store).run ambient = .ok ((final,finalStore),finalAmbient))
    (openLoop : Open acc) (initial : R acc store ambient machine) :
    Eventually (instructionStep fetch) (R final finalStore finalAmbient) machine := by
  induction items generalizing acc store ambient machine with
  | nil =>
    change Except.ok ((acc,store),ambient) = .ok ((final,finalStore),finalAmbient) at accepted
    cases accepted
    exact .done _ initial
  | cons item items ih =>
    simp only [List.forIn_cons,StateT.run_bind] at accepted
    cases first : ((body item acc).run store).run ambient with
    | error error =>
      simp only [first] at accepted
      cases accepted
    | ok out =>
      rcases out with ⟨⟨next,nextStore⟩,nextAmbient⟩
      simp only [first] at accepted
      have one := iteration item acc store ambient next nextStore nextAmbient machine first openLoop initial
      cases next with
      | done result =>
        change Except.ok ((result,nextStore),nextAmbient) = .ok ((final,finalStore),finalAmbient) at accepted
        cases accepted
        exact one
      | yield result =>
        apply eventually_trans (instructionStep fetch) _ _ _ one
        intro nextMachine related
        exact ih result nextStore nextAmbient nextMachine accepted (continues item acc store ambient result nextStore nextAmbient first) related

#print axioms forIn_execution
end Binary.Sequential
