import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingPhaseModel

/-! Native run equations used by the canonical queue-mutation certificates.
These retain actual values and worlds rather than an error post-state. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingPhase
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes TransmitSecurity CausalJournal
open Staged.Obligations Staging.Points CompleteCarrier
set_option maxHeartbeats 600000

theorem lift_success {body : WG.M α}
    (performed : runWGPrefix (liftWGPrefix body) w a h=(.ok ((value,v),b),last)) :
    (body.run w).run a=.ok ((value,v),b) ∧ last=h := by
  rw [runWGPrefix_lift] at performed
  cases native : (body.run w).run a with
  | error stop=>rw [native] at performed; cases performed
  | ok out=>rw [native] at performed; cases performed; exact ⟨rfl,rfl⟩

theorem branch_success
    (performed : runWGPrefix (liftWGPrefix (branch site flag)) w a h=(.ok ((value,v),b),last)) :
    value=flag ∧ v=w ∧ b=StagingInterior.clock a site flag ∧ last=h := by
  obtain ⟨native,rfl⟩:=lift_success performed
  simp only [branch,AmbientM.branch] at native
  cases native
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem peer_success
    (performed : runWGPrefix (liftWGPrefix (getPeer pid)) w a h=(.ok ((peer,v),b),last)) :
    v=w ∧ b=a ∧ last=h ∧ ∃ d,w.dev=some d ∧ d.peers[pid]?=some peer := by
  obtain ⟨native,rfl⟩:=lift_success performed
  obtain ⟨rfl,rfl,d,device,resident⟩:=Origins.getPeer_return pid w v peer a b native
  exact ⟨rfl,rfl,rfl,d,device,resident⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingPhase
