import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingPhaseSelected

/-! Actual native preparation reads and hidden allocation choices retain
the original world. Their returned values and clocks identify the later
insertion; they do not supply a post-world for a stopped choice. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingPhase
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing TransmitSecurity CausalJournal
open Staged.Obligations CompleteCarrier Staging.Points
set_option maxHeartbeats 600000

theorem ambient_success {action : AmbientM α}
    (run : runWGPrefix (liftWGPrefix (monadLift action : WG.M α)) w a h=(.ok ((value,v),b),last)) :
    v=w ∧ last=h ∧ action.run a=.ok (value,b) := by
  rw [runWGPrefix_lift] at run
  change (((StateT.lift action : WG.M α).run w).run a,h)=_ at run
  rw [stateLiftAmbient_run] at run
  cases actual : action.run a with
  | error stop=>rw [actual] at run; cases run
  | ok pair=>obtain ⟨returned,c⟩:=pair; rw [actual] at run; cases run; exact ⟨rfl,rfl,rfl⟩

theorem device_success
    (run : runWGPrefix (liftWGPrefix getDev) w a h=(.ok ((device,v),b),last)) :
    v=w ∧ b=a ∧ last=h ∧ w.dev=some device := by
  obtain ⟨native,rfl⟩:=lift_success run
  cases found : w.dev with
  | none=>simp [getDev,found,invariant,AmbientM.invariant] at native; cases native
  | some d=>
    simp [getDev,found] at native
    obtain ⟨⟨rfl,rfl⟩,rfl⟩:=native
    exact ⟨rfl,rfl,rfl,rfl⟩

theorem allocation_choice
    (allocated : (AmbientM.hiddenAlloc .keepaliveSkb).run a=.ok (value,b))
    (refused : (AmbientM.branch .keepaliveNoMem (!value)).run b=.ok (false,c)) :
    StagingInterior.keepaliveAllocation.run a=.ok (false,c) := by
  unfold StagingInterior.keepaliveAllocation
  simp only [StateT.run_bind,allocated]
  exact refused

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingPhase
