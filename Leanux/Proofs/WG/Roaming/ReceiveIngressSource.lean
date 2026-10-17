import Leanux.Proofs.WG.Roaming.ReceiveIngressFrames
import Leanux.Proofs.WG.Roaming.ConsumeEndpointSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Noise Std.Do

/-- Original packet admission preserves all optional peer endpoints. This
includes malformed headers, full handshake queues, CPU selection and all actual
data admission/cleanup paths, with no queue or reference readiness premise. -/
theorem packetReceive_endpoints (msg : List UInt8) (src : SkbSource) (entry : Option Device) :
    Ensures (packetReceive msg src)
      (fun g => responseEndpointMap g.dev = responseEndpointMap entry)
      (fun _ g => responseEndpointMap g.dev = responseEndpointMap entry) := by
  let safe : WGWorld → Prop := fun g => responseEndpointMap g.dev = responseEndpointMap entry
  change Ensures _ safe (fun _ => safe)
  have hpure {α : Type} (x : α) : Ensures (pure x : WG.M α) safe (fun _ => safe) := by
    intro g a r final after pre run; cases run; exact pre
  have hbranch (site : Decision) (value : Bool) :
      Ensures (branch site value : WG.M Bool) safe (fun _ => safe) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branch site value) safe)
  have hstop {α : Type} (message : String) : Ensures (invariant message : WG.M α)
      safe (fun _ => safe) := by
    intro g a r final after pre run; cases run
  have hunsupported {α : Type} (message : String) : Ensures (unsupported message : WG.M α)
      safe (fun _ => safe) := by
    intro g a r final after pre run; cases run
  have hdev : Ensures getDev safe (fun _ => safe) := by
    intro g a r final after pre run
    cases hd : g.dev with
    | none => simp [getDev,hd,invariant,AmbientM.invariant] at run; cases run
    | some old => simp [getDev,hd] at run; rcases run with ⟨⟨rfl,rfl⟩,rfl⟩; exact pre
  have hmodify (f : Device → Device) (same : ∀ d, (f d).peers = d.peers) :
      Ensures (modifyDev f) safe (fun _ => safe) := by
    intro g a r final after pre run
    cases run
    have unchanged : responseEndpointMap (g.dev.map f) = responseEndpointMap g.dev := by
      funext pid
      cases device : g.dev <;> simp [responseEndpointMap,same]
    exact unchanged.trans pre
  have hqueue : Ensures (queueDeviceWork .receiveWorker : WG.M Unit) safe (fun _ => safe) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.queueDeviceWork .receiveWorker) safe)
  unfold packetReceive
  repeat' first
    | with_reducible exact hpure _
    | with_reducible exact hbranch _ _
    | with_reducible exact hstop _
    | with_reducible exact hunsupported _
    | with_reducible exact hdev
    | with_reducible exact hqueue
    | with_reducible exact hmodify _ (fun _ => rfl)
    | with_reducible exact prepareSkbHeader_spec_endpoints_variant _ entry
    | with_reducible exact cpumaskNextOnline_spec_endpoints_variant entry
    | with_reducible exact ipTunnelGetDsfield_spec_endpoints_variant _ _ entry
    | with_reducible exact consumeData_endpoints _ _ _ entry
    | (with_reducible refine ensures_bind (Q := fun _ => safe) _ _ ?_ (fun _ => ?_))
    | split

end Leanux.Proofs.WG.Roaming
