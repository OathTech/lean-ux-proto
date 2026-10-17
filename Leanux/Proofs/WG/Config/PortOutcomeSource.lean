import Leanux.Proofs.WG.Config.PortOutcomeModel
import Leanux.Proofs.WG.Config.MultiMixedModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean

/-- The original nonzero request retains its same-port branch and otherwise
its actual ordered source-clearing effect. No completion is assumed. -/
theorem setDevice_nonzeroPort_effect (d : Device) (port : Nat) (bound : Nat → Bool)
    (nonzero : port ≠ 0) (net : d.creatingNet = true) :
    Ensures (wgSetDevice (portAttrs d port))
      (fun g => g.dev = some d ∧ selectsDevice g d ∧ g.portBound = bound)
      (fun ret g => ret = (nonzeroPortRequestOutcome d port bound).1 ∧
        ∃ current, g.dev = some current ∧
          withoutPeers current = withoutPeers (nonzeroPortRequestOutcome d port bound).2 ∧
          if d.incomingPort = port then current = requestGeneration d
          else ClearedPeerStore d current d.peerList) := by
  intro g ambient ret final after pre run
  have effect := setDevice_port_nonzero d port nonzero net bound g ambient ret final after pre run
  by_cases same : d.incomingPort = port
  · simp only [ite_eq_left same] at effect
    refine ⟨?_,requestGeneration d,effect.2,?_,?_⟩
    · simpa only [nonzeroPortRequestOutcome,same,ite_true] using effect.1
    · simp only [nonzeroPortRequestOutcome,same,ite_true]
    · simp only [same,ite_true]
  · simp only [ite_eq_right same] at effect
    obtain ⟨code,outer,clears⟩ := effect
    obtain ⟨current,device,fields⟩ := Option.map_eq_some_iff.mp outer
    refine ⟨?_,current,device,?_,?_⟩
    · simpa only [nonzeroPortRequestOutcome,same,ite_false,requestGeneration] using code
    · simpa only [nonzeroPortRequestOutcome,same,ite_false,requestGeneration] using fields
    · simp only [same,ite_false]
      simpa only [clearedPeers,device,Option.bind_some,ClearedPeerStore] using clears

end Leanux.Proofs.WG.Config
