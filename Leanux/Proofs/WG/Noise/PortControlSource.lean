import Leanux.Proofs.Framing.WGDump
import Leanux.Proofs.Framing.WGSocketLifecycle
import Leanux.WG.Netlink

/-! Projection-parametric composition for the original port setter, including its saved-peer source-cache clearing and socket branch. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG Leanux.Proofs.Framing Std.Do

theorem setPort_frame_source {V : Type} (view : WGWorld → V) (port : Nat)
    (read : SameView view getDev)
    (clear : ∀pid,SameView view (clearPeerEndpointSrc pid))
    (write : SameView view (modifyDev fun d=>{d with incomingPort:=port}))
    (socket : SameView view (socketInit port)) :
    SameView view (setPort port) := by
  have ambient (site : Decision) (value : Bool) : SameView view (branch site value) :=
    fun entry=>hoare_liftAmbient (AmbientM.branch site value) (fun g=>view g=entry)
  unfold setPort
  apply read.bind
  intro d
  apply (ambient .setPortSame (d.incomingPort==port)).bind
  intro same
  cases same with
  | true=>exact SameView.pure view 0
  | false=>
    apply (DumpComposition.forIn_sameView d.peerList ()
      (fun pid _=>do
        _ ←branch .setPortPeerIter true
        clearPeerEndpointSrc pid
        pure (.yield ()))
      (fun pid _=>(ambient .setPortPeerIter true).bind (fun _=>
        (clear pid).bind (fun _=>SameView.pure view (ForInStep.yield ()))))).bind
    intro _
    apply (ambient .setPortPeerIter false).bind
    intro _
    apply (ambient .setPortNotRunning (!d.running)).bind
    intro down
    cases down with
    | true=>exact write.bind (fun _=>SameView.pure view 0)
    | false=>exact socket
end Leanux.Proofs.WG.Noise
