import Leanux.Proofs.WG.Config.ScalarAllowedFrames
import Leanux.Proofs.WG.Config.ScalarTailEffects
import Leanux.Proofs.WG.Queues.BaseCoherenceConfiguration

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.ScalarTail
open Leanux Leanux.WG Noise Std.Do
open Queues Queues.RxCredits Leanux.Proofs.Framing Lifetimes
open PeerScalarRetention ScalarFinish

theorem replacement_frame (pid : PeerId) (flags : UInt32) :
    SameView (fun g=>(view g,BaseCoherence.view g))
      (do if ←branch .peerReplaceAips (flags &&& WGPEER_F_REPLACE_ALLOWEDIPS !=0) then
            removeByPeer pid : WG.M Unit) := by
  apply SameView.bind (fun initial=>
    hoare_liftAmbient (AmbientM.branch .peerReplaceAips
      (flags &&& WGPEER_F_REPLACE_ALLOWEDIPS !=0)) _)
  intro replace
  cases replace with
  | false=>exact SameView.pure _ ()
  | true=>exact (ScalarAllowed.remove_frame pid).product (BaseCoherence.removeByPeer_view pid)

end Leanux.Proofs.WG.Config.ScalarTail
