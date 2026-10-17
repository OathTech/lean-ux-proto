import Leanux.Proofs.WG.TimerDiscipline.OuterFirstReceiptSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Env

/-- A normal actual outer call supplies the first retransmit receipt. The
retry effect is at the immediate post-unit snapshot, before arbitrary later
turns; the receipt also retains the exact original suffix outcome. -/
theorem runTimers_first_retransmit_receipt (jPass : UInt64) (pid : PeerId) (we : WheelEntry)
    (identity attempts : Nat) (expiry : Option UInt64) :
    Campaign2.Product.Ensures
      (observed (Env.runTimers jPass)
        (firstTimerReceiptPath jPass .timerRetransmit pid .retransmitHandshake we))
      (fun entry => FirstTimerSelected jPass .timerRetransmit pid .retransmitHandshake we entry ∧
        retryObservation entry.toSnapshot pid = some (identity, attempts, expiry))
      (fun result final => ∃ remaining selected afterUnit,
        result.1 = .ok ((remaining, (pid, .retransmitHandshake, selected),
          .ok (result.2, final)), afterUnit) ∧
        retryObservation selected.toSnapshot pid = some (identity, attempts, expiry) ∧
        retryObservation afterUnit.toSnapshot pid = some (identity, nextAttempts attempts, none)) := by
  apply observed_effect
  intro initial result final pre run
  obtain ⟨remaining, selected, afterUnit, budget, prefixRun, unitRun, callback, suffix,
      kind, sameDevice, receipt⟩ :=
    runTimers_first_receipt_run jPass .timerRetransmit pid .retransmitHandshake we
      initial final result pre.1 run
  let start : World := {initial with wg := {initial.wg with queuedThisCall := []}}
  have before : retryAt start.wg pid = some (identity, attempts, expiry) := pre.2
  have selectedView := (Noise.Product.ensures_iff _ _ _).mpr
    (timerSelection_kernel_spec (fun g _ _ _ => retryAt g pid = some (identity, attempts, expiry))
      .timerRetransmit pid .retransmitHandshake we none)
    start () selected before prefixRun
  have afterView := fireSelected_retransmit pid we identity attempts expiry
    selected () afterUnit selectedView callback
  exact ⟨remaining, Campaign2.Product.snapshot selected, Campaign2.Product.snapshot afterUnit,
    observe_ok receipt, selectedView, afterView⟩

end Leanux.Proofs.WG.TimerDiscipline
