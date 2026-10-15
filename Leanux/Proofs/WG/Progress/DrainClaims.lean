import Leanux.Proofs.WG.Progress.DrainEffects

set_option autoImplicit false

namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Campaign2 TimerDiscipline

theorem source_drain_bounded (upTo : Option PeerId) (d : Device)
    (enough : flushQueueCount (workQueues d) < 4096) :
    Campaign2.Returns (observedDrain upTo) (fun entry => entry.wg.device = some d)
      (fun outcome _ => DrainBounded upTo (flushQueueCount (workQueues d)) outcome) := by
  intro entry resident
  exact ⟨_, entry, rfl, drainAuditRun_bounded upTo 4096 entry d resident enough⟩

theorem drainBounded_none (count : Nat) (success : DrainSuccess) (final : Snapshot)
    (bounded : DrainBounded none count (.ok (success, final))) :
    flushQueues final = some ([], []) := by
  have reason := bounded.2
  cases chosen : success.reason with
  | empty => simpa [chosen] using reason
  | requestedClear pid => simp [chosen] at reason

theorem source_drain_to_empty (d : Device)
    (enough : flushQueueCount (workQueues d) < 4096) :
    Campaign2.Ensures (drainHandshakeSendWq none)
      (fun entry => entry.wg.device = some d)
      (fun _ final => flushQueues final = some ([], [])) := by
  intro entry returned final resident run
  cases returned
  have exactRun := drainAuditRun_original none entry
  rw [run] at exactRun
  have bound := drainAuditRun_bounded none 4096 entry d resident enough
  cases audit : drainAuditRun none 4096 entry with
  | error failure => simp [audit, drainEraseRaw] at exactRun
  | ok found =>
    rcases found with ⟨success, after⟩
    simp only [audit, drainEraseRaw, Except.ok.injEq, Prod.mk.injEq, true_and] at exactRun
    subst after
    rw [audit] at bound
    exact drainBounded_none _ success (snapshot final) bound

end Leanux.Proofs.WG.Progress
