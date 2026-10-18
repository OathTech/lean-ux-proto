import Leanux.Proofs.WG.Roaming.RemoteControlFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteControl
open Leanux Leanux.WG Noise Lifetimes Queues Queues.RxCredits Leanux.Proofs.Framing Std.Do

theorem setPeerEndpoint_all_remotes (pid : PeerId) (endpoint : Endpoint) (entry : RemoteMap) :
    Ensures (setPeerEndpoint pid endpoint) (fun g => destinationAt g = entry)
      (fun _ g => destinationAt g = setterRemotes entry pid endpoint) := by
  by_cases valid : endpoint.family = AF_INET ∨ endpoint.family = AF_INET6
  · simpa only [setterRemotes,ite_eq_left valid] using setPeerEndpoint_remotes pid endpoint valid entry
  · intro g a result final b pre run
    have eq := (ProjectedAction.iff_run_ambient _ _ _).mp
      (setPeerEndpoint_invalid pid endpoint (fun h => valid (Or.inl h)) (fun h => valid (Or.inr h)))
      g a result final b run
    simpa only [setterRemotes,ite_eq_right valid,eq] using pre

theorem consumeDataDone_all_remotes (entry : RemoteMap) (pid : PeerId)
    (pkt : RxPacket) (endpoint : Endpoint) :
    Ensures (consumeDataDone pid pkt endpoint) (fun g => destinationAt g = entry)
      (fun _ g => RemoteRetained (setterRemotes entry pid endpoint) (destinationAt g)) := by
  rw [ConsumeConfirmation.source]
  refine ensures_bind _ _ (setPeerEndpoint_all_remotes pid endpoint entry) ?_
  intro _ g a result final b pre run
  exact (hoare_iff_run_ambient _ _ _).mp
    (preserves_bind ((RemoteCompletion.receivedWithKeypair_remotes pid pkt.keypair).wp
      (RemoteRetained (setterRemotes entry pid endpoint)))
      (fun confirmed => RemoteCompletion.afterConfirmation_retained _ pid pkt confirmed))
    g a result final b (RemoteRetained.of_eq pre) run

end Leanux.Proofs.WG.Roaming.RemoteControl
