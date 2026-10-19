import Leanux.Proofs.WG.Config.PeerDead
import Leanux.Proofs.WG.AllowedIps.RoutingFlushFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise AllowedIps
open Leanux.Proofs.Framing Lifetimes Std.Do

theorem makeDeadAfterRemoval_routing (pid : PeerId) :
    SameView routingView (makeDeadAfterRemoval pid) := by
  unfold makeDeadAfterRemoval
  refine (routing_kernel _ getDev_sameWGStore).bind (fun d => ?_)
  have branchFrame : SameView routingView
      (branch .pubkeyRemoveHashed (d.peerHashtable.any (·.2 == pid))) :=
    fun initial => hoare_liftAmbient (AmbientM.branch .pubkeyRemoveHashed
      (d.peerHashtable.any (·.2 == pid))) (fun w=>routingView w=initial)
  refine branchFrame.bind (fun _ => ?_)
  refine (modifyDev_routing
    (fun d=>{d with peerHashtable:=d.peerHashtable.filter (·.2 != pid)})
    (fun _=>rfl)).bind (fun _=>?_)
  exact modifyPeer_routing pid (fun p=>{p with isDead:=true}) (fun _=>rfl)


end Leanux.Proofs.WG.Config
