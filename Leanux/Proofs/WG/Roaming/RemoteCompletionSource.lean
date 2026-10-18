import Leanux.Proofs.WG.Roaming.RemoteCompletionFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteCompletion
open Leanux Leanux.WG Noise Std.Do Leanux.Proofs.Framing
open Lifetimes Queues TimerDiscipline

theorem consumeDataDone_remotes (entry : RemoteMap) (pid : PeerId)
    (pkt : RxPacket) (endpoint : Endpoint)
    (valid : endpoint.family = AF_INET ∨ endpoint.family = AF_INET6) :
    Ensures (consumeDataDone pid pkt endpoint) (fun g => destinationAt g = entry)
      (fun _ g => RemoteRetained (updateRemote entry pid (destination endpoint)) (destinationAt g)) := by
  rw [ConsumeConfirmation.source]
  refine ensures_bind _ _ (setPeerEndpoint_remotes pid endpoint valid entry) ?_
  intro _ g a result final b pre run
  exact (hoare_iff_run_ambient _ _ _).mp
    (preserves_bind ((receivedWithKeypair_remotes pid pkt.keypair).wp
      (RemoteRetained (updateRemote entry pid (destination endpoint))))
      (fun confirmed => afterConfirmation_retained _ pid pkt confirmed))
    g a result final b (RemoteRetained.of_eq pre) run

end Leanux.Proofs.WG.Roaming.RemoteCompletion
