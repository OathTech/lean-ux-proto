import Leanux.Proofs.WG.Config.ZeroPortOutcomeModel
import Leanux.Proofs.WG.Config.ZeroPort
import Leanux.Proofs.WG.Config.MultiMixedModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean

/-- Normalize the existing actual zero-port normal-run effect. The chosen port
is obtained from that execution; missing draws, collisions and reset Stops do
not become successful outcomes or extra premises. -/
theorem setDevice_zeroPort_effect (d : Device) (net : d.creatingNet = true) :
    Ensures (wgSetDevice (portAttrs d 0))
      (fun g => g.dev = some d ∧ selectsDevice g d)
      (fun ret g => ret = 0 ∧ ∃ chosen current,
        ZeroPortRequestChoice d chosen ∧ g.dev = some current ∧
        withoutPeers current = withoutPeers (zeroPortRequestDevice d chosen) ∧
        if d.incomingPort = 0 then current = requestGeneration d
        else ClearedPeerStore d current d.peerList) := by
  intro g ambient ret final after pre run
  obtain ⟨code,effect⟩ := setDevice_port_zero d net g ambient ret final after pre run
  by_cases same : d.incomingPort = 0
  · have device : final.dev = some (requestGeneration d) := by
      simpa only [zeroPortEffects,requestGeneration,same,ite_true] using effect
    refine ⟨code,0,requestGeneration d,?_,device,?_,?_⟩
    · simp only [ZeroPortRequestChoice,same,ite_true]
    · simp only [zeroPortRequestDevice,same,ite_true]
    · simp only [same,ite_true]
  · have changed : clearedPeers d final d.peerList ∧
        if d.running then ∃ chosen, LOCAL_PORT_LOW ≤ chosen ∧ chosen ≤ LOCAL_PORT_HIGH ∧
          final.dev.map withoutPeers = some (withoutPeers
            {requestGeneration d with sock4 := some chosen,sock6 := some chosen,incomingPort := chosen})
        else final.dev.map withoutPeers = some (withoutPeers {requestGeneration d with incomingPort := 0}) := by
      simpa only [zeroPortEffects,requestGeneration,same,ite_false,clearedPeers] using effect
    obtain ⟨clears,changed⟩ := changed
    cases running : d.running with
    | false =>
      have outer : final.dev.map withoutPeers = some (withoutPeers {requestGeneration d with incomingPort := 0}) := by
        simpa only [running,Bool.false_eq_true,ite_false] using changed
      obtain ⟨current,device,fields⟩ := Option.map_eq_some_iff.mp outer
      refine ⟨code,0,current,?_,device,?_,?_⟩
      · simp only [ZeroPortRequestChoice,same,ite_false,running,Bool.false_eq_true]
      · simpa only [zeroPortRequestDevice,same,ite_false,running,Bool.false_eq_true] using fields
      · simp only [same,ite_false]
        simpa only [clearedPeers,device,Option.bind_some,ClearedPeerStore] using clears
    | true =>
      obtain ⟨chosen,low,high,outer⟩ := (show ∃ chosen, LOCAL_PORT_LOW ≤ chosen ∧ chosen ≤ LOCAL_PORT_HIGH ∧
          final.dev.map withoutPeers = some (withoutPeers
            {requestGeneration d with sock4 := some chosen,sock6 := some chosen,incomingPort := chosen}) by
        simpa only [running,ite_true] using changed)
      obtain ⟨current,device,fields⟩ := Option.map_eq_some_iff.mp outer
      refine ⟨code,chosen,current,?_,device,?_,?_⟩
      · simpa only [ZeroPortRequestChoice,same,ite_false,running,ite_true] using And.intro low high
      · simpa only [zeroPortRequestDevice,same,ite_false,running,ite_true] using fields
      · simp only [same,ite_false]
        simpa only [clearedPeers,device,Option.bind_some,ClearedPeerStore] using clears

end Leanux.Proofs.WG.Config
