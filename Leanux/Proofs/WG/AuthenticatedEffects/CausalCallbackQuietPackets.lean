import Leanux.Proofs.WG.AuthenticatedEffects.CausalCallbackQuietEffects
import Leanux.Proofs.WG.HandshakeSecurity.StagedDisposalPacketProjection
import Leanux.Proofs.WG.AuthenticatedEffects.PacketEffectsFrames

/-! Receive maintenance retains its native action and only appends receipts
excluded by the supplied history projection. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.CallbackQuiet
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity
open HandshakeSecurity.StagedDisposal
variable {F : Type}

theorem prepare (ρ : Event → Option F)
    (armed : ∀ r, ρ (.armed r) = none) (queued : ∀ r, ρ (.queued r) = none)
    (disposal : ∀ r, ρ (.stagedDisposal r) = none) (pid : PeerId) (packet : RxPacket) :
    StateQuiet ρ (PacketSource.prepareWith effects peerRelease pid packet) := by
  apply state_of_history
  intro before
  exact Driver.disposal_prepare_history (effects_history ρ armed queued before) peerRelease
    (fun _ => state_history (state_focus ρ Event.stagedDisposal stagedDisposal? disposal _) before) pid packet

theorem prepare_projects (ρ : Event → Option F)
    (armed : ∀ r, ρ (.armed r) = none) (queued : ∀ r, ρ (.queued r) = none)
    (disposal : ∀ r, ρ (.stagedDisposal r) = none) (pid : PeerId) (packet : RxPacket) :
    StateProjectsPrefix ρ id (PacketSource.prepareWith effects peerRelease pid packet)
      (liftWGPrefix (Queues.RxCredits.prepareRest pid packet)) := by
  have project := PacketSource.prepare_projects ρ
    (CausalEffects.ops_projects scope? Event.armed Event.queued ρ armed queued)
    peerRelease (fun peer => liftWGPrefix (peerPut peer))
    (Decoration.release_projects Event.stagedDisposal stagedDisposal? ρ disposal) pid packet
  change StateProjectsPrefix ρ id (PacketSource.prepareWith effects peerRelease pid packet)
    (PacketSource.prepareWith TimerEffects.lifted
      (fun peer => (TimerEffects.lifted : TimerEffects.Ops (WGPrefix F)).step (peerPut peer)) pid packet) at project
  rw [PacketSource.prepare_neutral,PacketEffects.prepare_lifted] at project
  exact project

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.CallbackQuiet
