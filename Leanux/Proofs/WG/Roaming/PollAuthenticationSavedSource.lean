import Leanux.Proofs.WG.Roaming.PollAuthenticationQuietSource
import Leanux.Proofs.WG.Packets.PublicationDeferred

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.PollAuthentication
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Queues Lifetimes
variable {α : Type}

/-- The wheel is authorized by this actual saved getter, not an arbitrary device. -/
theorem saved_spec :
    PrefixEnsures Reached PublicSafe (RxHistory.audit getDevSavedAudit)
      (fun d h w => Reached h w ∧ SavedPeers d.peers.toList (identityView w.wg)) :=
  (audit_ensures _
    (pinned_const _private.Leanux.Proofs.WG.Packets.PublicationDeferred.«0».Leanux.Proofs.WG.PublicationDeferred.saved_spec)).consequence
      (fun _ _ hi => hi)
      (fun _ _ _ hi => ⟨⟨hi.1.1,hi.2⟩,hi.1.2⟩)

theorem wheel_spec (d : Device) (j : UInt64) :
    PrefixEnsures
      (fun h w => Reached h w ∧ SavedPeers d.peers.toList (identityView w.wg))
      PublicSafe (RxHistory.audit (wheelNextDueAudit d j)) (fun _ => Reached) :=
  (audit_ensures _
    ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationDeferred.«0».Leanux.Proofs.WG.PublicationDeferred.wheel_spec) d j)).consequence
      (fun _ _ hi => ⟨⟨hi.1.1,hi.2⟩,hi.1.2⟩)
      (fun _ _ _ hi => hi)

end Leanux.Proofs.WG.Roaming.PollAuthentication
