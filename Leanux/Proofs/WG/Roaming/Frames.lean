import Leanux.Proofs.WG.Roaming.EndpointSource
import Leanux.Proofs.WG.Noise.AccessSource

set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

def destinationAt (g : WGWorld) (pid : PeerId) : Option (Nat × Nat × Nat × Nat) :=
  ((peerAt g pid).bind Peer.endpoint).map destination

theorem dstCacheReset_destination (pid : PeerId) (remote : Option (Nat × Nat × Nat × Nat)) :
    ⦃fun w => ⌜destinationAt w pid = remote⌝⦄ dstCacheReset pid
    ⦃⇓? _ w => ⌜destinationAt w pid = remote⌝⦄ := by
  let P : WGWorld → Prop := fun g => destinationAt g pid = remote
  have tail (ts : UInt64) : Ensures (do
      let p ← getPeer pid
      setPeer pid {p with dstCache := {p.dstCache with resetTs := ts}}) P (fun _ => P) := by
    refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (getPeer_spec pid P)) ?_
    intro p g ambient result final after pre run
    change Except.ok (((), {g with dev := g.dev.map (fun d : Device =>
      {d with peers := d.peers.insert pid {p with dstCache := {p.dstCache with resetTs := ts}}})}), ambient) = _ at run
    cases run
    have endpoint : destinationAt g pid = p.endpoint.map destination := by
      simp [destinationAt, pre.2]
    cases hd : g.dev with
    | none => simp [peerAt, hd] at pre
    | some d =>
      simpa [P, destinationAt, peerAt, hd] using endpoint.symm.trans pre.1
  apply (ensures_iff _ _ _).mp
  unfold dstCacheReset
  refine ensures_bind (Q := fun _ => P) _ _ ?_ ?_
  · exact (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (get : AmbientM Ambient) P)
  · intro ambient
    refine ensures_bind (Q := fun _ => P) _ _ ?_ ?_
    · intro g a result final after pre run
      cases run
      exact pre
    · intro g
      split
      · intro s a result final after pre run
        cases run
        exact pre
      · refine ensures_bind (Q := fun _ => P) _ _ ?_ tail
        exact (ensures_iff _ _ _).mpr
          (hoare_liftAmbient_variant (AmbientM.hiddenJiffies .dstCacheResetTs) P)

end Leanux.Proofs.WG.Roaming
