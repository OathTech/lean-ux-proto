import Leanux.Proofs.WG.Roaming.ReceiveIngressSource
import Leanux.Proofs.WG.Roaming.View

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Noise Std.Do

/-- The actual UDP ingress call preserves endpoint presence and destination on
normal return. Handshake work is only queued here; this does not assert anything
about later worker/NAPI execution or historical packet authentication. -/
theorem wgReceive_preserves_endpoints (msg : List UInt8) (src : SkbSource)
    (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (wgReceive msg src) (fun s => s = entry)
      (fun _ final => responseEndpointMap final.wg.device = responseEndpointMap entry.wg.device ∧
        ∀ pid, remoteAt final pid = remoteAt entry pid) := by
  intro g ambient result final after pre run
  subst entry
  let safe : WGWorld → Prop := fun w => responseEndpointMap w.dev = responseEndpointMap g.dev
  have hbranch (site : Decision) (value : Bool) :
      Ensures (branch site value : WG.M Bool) safe (fun _ => safe) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branch site value) safe)
  have hstop {α : Type} (message : String) : Ensures (unsupported message : WG.M α)
      safe (fun _ => safe) := by
    intro w a r finish tail before actual; cases actual
  have ingress : Ensures (wgReceive msg src) safe (fun _ => safe) := by
    unfold wgReceive
    repeat' first
      | with_reducible exact hbranch _ _
      | with_reducible exact hstop _
      | with_reducible exact packetReceive_endpoints msg src g.dev
      | (with_reducible refine ensures_bind (Q := fun _ => safe) _ _ ?_ (fun _ => ?_))
      | split
  have same := ingress g ambient result final after rfl run
  refine ⟨same,?_⟩
  intro pid
  have point := congrFun same pid
  have remote := congrArg (fun endpoint : Option (Option Endpoint) => endpoint.join.map destination) point
  have joinMap (p : Option Peer) : (p.map Peer.endpoint).join = p.bind Peer.endpoint := by
    cases p <;> rfl
  simpa only [responseEndpointMap,joinMap,remoteAt,Campaign2.Snapshot.peerAt,
    Campaign2.snapshot,Campaign2.core] using remote

end Leanux.Proofs.WG.Roaming
