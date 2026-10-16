import History

namespace Binary.Sequential

/-- Reuse a proved physical execution while exposing only its endpoint.
This forgets observations, not instructions or undefined outcomes. -/
theorem forget [Labels] {fetch : Int64 → Option Decoded} {s : Executed}
    {P : Executed → Prop} {Q : MachineState → Prop}
    (run : Eventually (historyStep fetch) P s)
    (post : ∀ t, P t → Q t.machine) :
    Eventually (instructionStep fetch) Q s.machine := by
  apply eventually_weaken (instructionStep fetch) _ _ _ _ (history_project fetch P s run)
  rintro t ⟨history, facts⟩
  exact post ⟨t, history⟩ facts

end Binary.Sequential
