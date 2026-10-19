import Leanux.Proofs.WG.AuthenticatedEffects.CausalEffectsFrames
import Leanux.Proofs.WG.TransmitSecurity.DriverEffectsHistory
import Leanux.Proofs.WG.AuthenticatedEffects.CausalCallbackQuietActors
import Leanux.Proofs.WG.HandshakeSecurity.StagedDisposalEffectsProjection
import Leanux.Proofs.WG.AuthenticatedEffects.TimerEffectsNeutral

/-! Quiet projections of actual handshake queueing, including its conditional
peer release. Each excluded event constructor is an explicit premise. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.CallbackQuiet
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity
open HandshakeSecurity.StagedDisposal
set_option maxHeartbeats 600000

variable {F : Type}

theorem effects_history (ρ : Event → Option F)
    (armed : ∀ r, ρ (.armed r) = none) (queued : ∀ r, ρ (.queued r) = none)
    (before : List F) : Driver.EffectsHistory (fun h => h.filterMap ρ = before) effects where
  step := Driver.History.state_lift
  arm := fun pid timer delay caller => state_history
    ⟨(fun w a h => (StateAppends.lift (armTimer pid timer delay caller)).receiptWGObserved
        (fun r => Event.armed ⟨CausalScope.current scope? h,pid,timer,delay,caller,r⟩) w a h),
      (CausalEffects.ops_frames scope? Event.armed Event.queued ρ armed queued).arm pid timer delay caller⟩ before
  append := fun pid => state_history
    ⟨(fun w a h => (StateAppends.lift
        (modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]})).receiptWGObserved
        (fun r => Event.queued ⟨CausalScope.current scope? h,pid,r⟩) w a h),
      (CausalEffects.ops_frames scope? Event.armed Event.queued ρ armed queued).append pid⟩ before

theorem queued (ρ : Event → Option F)
    (armed : ∀ r, ρ (.armed r) = none) (queued : ∀ r, ρ (.queued r) = none)
    (disposal : ∀ r, ρ (.stagedDisposal r) = none) (pid : PeerId) (retry : Bool) :
    StateQuiet ρ (Effects.queuedWith effects peerRelease pid retry) := by
  apply state_of_history
  intro before
  exact Driver.disposal_queued_history (effects_history ρ armed queued before) peerRelease
    (fun _ => state_history (state_focus ρ Event.stagedDisposal stagedDisposal? disposal _) before) pid retry

theorem queued_projects (ρ : Event → Option F)
    (armed : ∀ r, ρ (.armed r) = none) (queued : ∀ r, ρ (.queued r) = none)
    (disposal : ∀ r, ρ (.stagedDisposal r) = none) (pid : PeerId) (retry : Bool) :
    StateProjectsPrefix ρ id (Effects.queuedWith effects peerRelease pid retry)
      (liftWGPrefix (sendQueuedHandshakeInitiation pid retry)) := by
  have project := Effects.queued_projects ρ
    (CausalEffects.ops_projects scope? Event.armed Event.queued ρ armed queued)
    peerRelease (fun peer => liftWGPrefix (peerPut peer))
    (Decoration.release_projects Event.stagedDisposal stagedDisposal? ρ disposal) pid retry
  change StateProjectsPrefix ρ id (Effects.queuedWith effects peerRelease pid retry)
    (Effects.queuedWith TimerEffects.lifted
      (fun peer => (TimerEffects.lifted : TimerEffects.Ops (WGPrefix F)).step (peerPut peer)) pid retry) at project
  rw [Effects.queued_neutral,TimerEffects.queued_lifted] at project
  exact project

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.CallbackQuiet
