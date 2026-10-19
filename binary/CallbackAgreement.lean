import CallbackExecution

namespace Binary.Callback
open TrustBase
local instance : Labels := Image.linkedLabels

theorem instruction_agreement {partialFetch fetch : Int64 → Option Decoded}
    (agree : ∀ p i, partialFetch p=some i → fetch p=some i)
    {s P} (run : instructionStep partialFetch s P) : instructionStep fetch s P := by
  unfold instructionStep at run ⊢
  cases read : partialFetch s.pc with
  | none => simp [read] at run
  | some i =>
    rw [read] at run
    simpa only [agree _ _ read] using run

theorem guarded_agreement {partialFetch fetch : Int64 → Option Decoded}
    (agree : ∀ p i, partialFetch p=some i → fetch p=some i)
    {guard P s} (run : Eventually (guardedStep partialFetch guard) P s) :
    Eventually (guardedStep fetch guard) P s := by
  induction run with
  | done s hp => exact .done s hp
  | step s mid step _ ih =>
    apply step_cps
    exact ⟨step.1,instruction_mono fetch s _ _ ih (instruction_agreement agree step.2)⟩

theorem history_agreement {partialFetch fetch : Int64 → Option Decoded}
    (agree : ∀ p i, partialFetch p=some i → fetch p=some i)
    {P s} (run : Eventually (historyStep partialFetch) P s) :
    Eventually (historyStep fetch) P s := by
  induction run with
  | done s hp => exact .done s hp
  | step s mid step _ ih =>
    apply step_cps
    exact instruction_mono fetch s.machine _ _
      (fun next hn => ih ⟨next,s.history++[next]⟩ hn) (instruction_agreement agree step)

theorem service_agreement {partialFetch fetch : Int64 → Option Decoded}
    (agree : ∀ p i, partialFetch p=some i → fetch p=some i)
    {address ready writes effect}
    (contract : ServiceReturns partialFetch address ready writes effect) :
    ServiceReturns fetch address ready writes effect := by
  intro s ra pc ready frame
  exact history_agreement agree (contract s ra pc ready frame)

#print axioms service_agreement
end Binary.Callback
