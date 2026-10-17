import Leanux.Proofs.WG.Index.OwnerCoherenceQueuedFrames
import Leanux.Proofs.WG.TimerDiscipline.RetryBaseSource

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise

/-- Every normal original queue call preserves local hashed-owner coherence,
for both retry modes. Actual clock/queue observations choose the effect; no
publisher, reference budget, queue state or recorded-input readiness is assumed. -/
theorem sendQueuedHandshakeInitiation_owner_coherent (pid : PeerId) (retry : Bool) :
    Campaign2.Ensures (sendQueuedHandshakeInitiation pid retry) View.OwnerCoherentSafe
      (fun _ => View.OwnerCoherentSafe) := by
  intro g ambient result final after pre run
  cases device : g.dev with
  | none =>
    cases retry <;>
      simp [sendQueuedHandshakeInitiation,branch,AmbientM.branch,getPeer,getDev,
        device,invariant,AmbientM.invariant] at run <;> cases run
  | some d =>
    cases resident : d.peers[pid]? with
    | none =>
      cases retry <;>
        simp [sendQueuedHandshakeInitiation,branch,AmbientM.branch,getPeer,getDev,
          device,resident,invariant,AmbientM.invariant] at run <;> cases run
    | some p =>
      have coherent : HashedOwnersCoherent d := pre d device
      cases retry with
      | false =>
        rw [← Config.observedSendQueued_erase] at run
        change (((Config.observedSendQueued pid).run g).run ambient >>= fun ((_,current),inputs) =>
          .ok (((),current),inputs)) = _ at run
        cases observed : ((Config.observedSendQueued pid).run g).run ambient with
        | error stop => rw [observed] at run; cases run
        | ok pair =>
          obtain ⟨⟨seen,current⟩,inputs⟩ := pair
          rw [observed] at run
          cases run
          have facts := Config.sendQueued_exact pid d p resident
            g ambient seen final after device observed
          have resetCoherent := peerWrite_owner_coherent d pid p
            {p with timerHandshakeAttempts := 0} resident rfl rfl coherent
          intro actual present
          change final.dev = some actual at present
          cases inspected : seen.2 with
          | none =>
            simp only [inspected] at facts
            have nextDevice : final.dev = _ := facts.1
            rw [nextDevice] at present
            cases present
            exact resetCoherent
          | some queued =>
            simp only [inspected] at facts
            have nextDevice : final.dev = _ := facts.2.2
            rw [nextDevice] at present
            cases present
            exact queuedDeviceAfterInspection_owner_coherent
              (Config.withPeer d pid {p with timerHandshakeAttempts := 0}) pid
              {p with timerHandshakeAttempts := 0} seen.1 queued
              (by simp [Config.withPeer]) resetCoherent
      | true =>
        rw [← TimerDiscipline.observedSendQueuedRetry_erase] at run
        change (((TimerDiscipline.observedSendQueuedRetry pid).run g).run ambient >>= fun ((_,current),inputs) =>
          .ok (((),current),inputs)) = _ at run
        cases observed : ((TimerDiscipline.observedSendQueuedRetry pid).run g).run ambient with
        | error stop => rw [observed] at run; cases run
        | ok pair =>
          obtain ⟨⟨seen,current⟩,inputs⟩ := pair
          rw [observed] at run
          cases run
          have facts := TimerDiscipline.sendQueuedRetry_exact pid d p resident
            g ambient seen final after device observed
          intro actual present
          change final.dev = some actual at present
          cases inspected : seen.2 with
          | none =>
            simp only [inspected] at facts
            have nextDevice : final.dev = some d := facts.1
            rw [nextDevice] at present
            cases present
            exact coherent
          | some queued =>
            simp only [inspected] at facts
            have nextDevice : final.dev = _ := facts.2.2
            rw [nextDevice] at present
            cases present
            exact queuedDeviceAfterInspection_owner_coherent d pid p seen.1 queued resident coherent

end Leanux.Proofs.WG.Index
