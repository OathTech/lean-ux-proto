import Leanux.Proofs.WG.Config.MixedAttributeFrames
import Leanux.Proofs.WG.Config.OperationFrames
import Leanux.Proofs.WG.Config.RunningPort

/-! Substantive WireGuard state frames for the actual source-clearing and refused-bind paths. -/

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

/-- The nonzero bind-refusal branch writes no WireGuard state. -/
theorem socketInit_nonzero_collision_frame (d : Device) (port : Nat) (bound : Nat → Bool)
    (nonzero : port ≠ 0) (net : d.creatingNet = true)
    (collision : (bound port || d.sock4 == some port || d.sock6 == some port) = true)
    (P : WGWorld → Prop) :
    Ensures (socketInit port) (fun g => g.dev = some d ∧ g.portBound = bound ∧ P g)
      (fun ret g => ret = -EADDRINUSE ∧ g.dev = some d ∧ P g) := by
  intro g ambient value final after pre run
  simp only [Bool.or_eq_true, beq_iff_eq] at collision
  simp [socketInit, getDev, pre.1, pre.2.1, net, nonzero, collision,
    iputReport, AmbientM.iputReport, AmbientM.branch] at run
  rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
  exact ⟨rfl, pre.1, pre.2.2⟩

end Leanux.Proofs.WG.Config
