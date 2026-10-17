import Leanux.Proofs.WG.Roaming.ResponseRejectionFrames
import Leanux.Proofs.WG.Noise.ComponentFrames

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Noise Std.Do

/-- Endpoint-map variant of C1 Keypairs/Frames/WGMore.prepareSkbHeader_spec,
including its validateHeaderLen call. Every original header branch is retained. -/
theorem prepareSkbHeader_spec_endpoints_variant (msg : List UInt8) (entry : Option Device) :
    Ensures (prepareSkbHeader msg)
      (fun g => responseEndpointMap g.dev = responseEndpointMap entry)
      (fun _ g => responseEndpointMap g.dev = responseEndpointMap entry) := by
  let safe : WGWorld → Prop := fun g => responseEndpointMap g.dev = responseEndpointMap entry
  change Ensures _ safe (fun _ => safe)
  have hpure {α : Type} (x : α) : Ensures (pure x : WG.M α) safe (fun _ => safe) := by
    intro g a r final after pre run; cases run; exact pre
  have hbranch (site : Decision) (value : Bool) :
      Ensures (branch site value : WG.M Bool) safe (fun _ => safe) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branch site value) safe)
  have hand (a b : WG.M Bool) (ha : Ensures a safe (fun _ => safe))
      (hb : Ensures b safe (fun _ => safe)) : Ensures (WG.andM a b) safe (fun _ => safe) := by
    unfold WG.andM
    refine ensures_bind _ _ ha ?_
    intro result; cases result <;> first | exact hpure _ | exact hb
  have hor (a b : WG.M Bool) (ha : Ensures a safe (fun _ => safe))
      (hb : Ensures b safe (fun _ => safe)) : Ensures (WG.orM a b) safe (fun _ => safe) := by
    unfold WG.orM
    refine ensures_bind _ _ ha ?_
    intro result; cases result <;> first | exact hpure _ | exact hb
  have hlength : Ensures (validateHeaderLen msg) safe (fun _ => safe) := by
    unfold validateHeaderLen
    repeat' first
      | with_reducible exact hpure _
      | with_reducible exact hbranch _ _
      | (with_reducible apply hand)
      | (with_reducible apply hor)
      | (with_reducible refine ensures_bind (Q := fun _ => safe) _ _ ?_ (fun _ => ?_))
      | split
  unfold prepareSkbHeader
  repeat' first
    | with_reducible exact hpure _
    | with_reducible exact hbranch _ _
    | with_reducible exact hlength
    | (with_reducible apply hand)
    | (with_reducible apply hor)
    | (with_reducible refine ensures_bind (Q := fun _ => safe) _ _ ?_ (fun _ => ?_))
    | split

/-- Endpoint-map variant of C1 Keypairs/Frames/WGMore.cpumaskNextOnline_spec.
The native read retains absent-device refusal and only the CPU field changes. -/
theorem cpumaskNextOnline_spec_endpoints_variant (entry : Option Device) :
    Ensures cpumaskNextOnline
      (fun g => responseEndpointMap g.dev = responseEndpointMap entry)
      (fun _ g => responseEndpointMap g.dev = responseEndpointMap entry) := by
  let safe : WGWorld → Prop := fun g => responseEndpointMap g.dev = responseEndpointMap entry
  change Ensures _ safe (fun _ => safe)
  have hpure {α : Type} (x : α) : Ensures (pure x : WG.M α) safe (fun _ => safe) := by
    intro g a r final after pre run; cases run; exact pre
  have hbranch (site : Decision) (value : Bool) :
      Ensures (branch site value : WG.M Bool) safe (fun _ => safe) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branch site value) safe)
  have hdev : Ensures getDev safe (fun _ => safe) := by
    intro g a r final after pre run
    cases hd : g.dev with
    | none => simp [getDev,hd,invariant,AmbientM.invariant] at run; cases run
    | some old => simp [getDev,hd] at run; rcases run with ⟨⟨rfl,rfl⟩,rfl⟩; exact pre
  have hwrite (cpu : Int) : Ensures (modifyDev fun d => {d with handshakeLastCpu := cpu})
      safe (fun _ => safe) := by
    intro g a r final after pre run
    cases run
    have unchanged : responseEndpointMap (g.dev.map fun d => {d with handshakeLastCpu := cpu}) =
        responseEndpointMap g.dev := by
      funext pid
      cases g.dev <;> rfl
    exact unchanged.trans pre
  unfold cpumaskNextOnline
  repeat' first
    | with_reducible exact hpure _
    | with_reducible exact hbranch _ _
    | with_reducible exact hdev
    | with_reducible exact hwrite _
    | (with_reducible refine ensures_bind (Q := fun _ => safe) _ _ ?_ (fun _ => ?_))
    | split

/-- Endpoint-map variant of C1 Keypairs/Frames/WGTransitions.ipTunnelGetDsfield_spec.
The actual VLAN refusal and both address-family decisions are unchanged. -/
theorem ipTunnelGetDsfield_spec_endpoints_variant (protocol : Nat) (hdr : List UInt8)
    (entry : Option Device) :
    Ensures (ipTunnelGetDsfield protocol hdr)
      (fun g => responseEndpointMap g.dev = responseEndpointMap entry)
      (fun _ g => responseEndpointMap g.dev = responseEndpointMap entry) := by
  let safe : WGWorld → Prop := fun g => responseEndpointMap g.dev = responseEndpointMap entry
  change Ensures _ safe (fun _ => safe)
  have hpure {α : Type} (x : α) : Ensures (pure x : WG.M α) safe (fun _ => safe) := by
    intro g a r final after pre run; cases run; exact pre
  have hbranch (site : Decision) (value : Bool) :
      Ensures (branch site value : WG.M Bool) safe (fun _ => safe) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branch site value) safe)
  have hstop {α : Type} (message : String) : Ensures (unsupported message : WG.M α)
      safe (fun _ => safe) := by
    intro g a r final after pre run; cases run
  unfold ipTunnelGetDsfield
  repeat' first
    | with_reducible exact hpure _
    | with_reducible exact hbranch _ _
    | with_reducible exact hstop _
    | (with_reducible refine ensures_bind (Q := fun _ => safe) _ _ ?_ (fun _ => ?_))
    | split

end Leanux.Proofs.WG.Roaming
