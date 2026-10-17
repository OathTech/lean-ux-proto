import Leanux.Proofs.WG.Config.MixedAttributeFrames
import Leanux.Proofs.WG.Config.OperationFrames
import Leanux.Proofs.WG.Config.RunningPort

/-! Substantive WireGuard state frames for the actual source-clearing loops. -/

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Std.Do

/-- Both real source-clearing loops preserve the selector/socket and bind lookup.
The source and cache changes inside each peer remain substantive effects. -/
theorem endpointClearLoop_configurationFrame (site : Decision) (pids : List PeerId)
    (bound : Nat → Bool) (sock : NlSock) (fixtures : FixtureDevices) :
    Ensures (do for pid in pids do
      _ ← branch site true
      clearPeerEndpointSrc pid)
      (fun g => g.portBound = bound ∧ readbackFrame g sock fixtures)
      (fun _ g => g.portBound = bound ∧ readbackFrame g sock fixtures) := by
  let P : WGWorld → Prop := fun g => g.portBound = bound ∧ readbackFrame g sock fixtures
  have step (pid : PeerId) : Ensures (clearPeerEndpointSrc pid) P (fun _ => P) := by
    intro g ambient value final after pre run
    exact ⟨clearEndpointSource_portBound pid bound g ambient value final after pre.1 run,
      clearEndpointSource_readbackFrame pid sock fixtures g ambient value final after pre.2 run⟩
  induction pids with
  | nil =>
    intro g ambient value final after pre run
    cases run
    exact pre
  | cons pid rest ih =>
    simp only [List.forIn_cons, bind_assoc]
    refine ensures_bind (Q := fun _ => P) _ _ ?_ ?_
    · exact (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branch site true) P)
    · intro _
      refine ensures_bind (Q := fun _ => P) _ _ (step pid) ?_
      intro _
      exact ih


end Leanux.Proofs.WG.Config
