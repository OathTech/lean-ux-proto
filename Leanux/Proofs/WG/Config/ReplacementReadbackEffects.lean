import Leanux.Proofs.WG.Config.ReplacementReadbackFrames
import Leanux.Proofs.WG.Config.AllowedGeneralReplacement
import Leanux.Proofs.WG.Config.AllowedRemovalEffects

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean

/-- Actual replacement effects give exact peer lookups with filtered lists,
the table sequence and all other getter input fields. The actual roots and
node store stay in the existential removal successor. -/
theorem replacementReadback_effect (d removed : Device) (pid : PeerId) (p : Peer)
    (resident : d.peers[pid]? = some p)
    (steps : RemovalEffect (withPeer (requestGeneration d) pid {p with refcount := p.refcount+1})
      p.allowedipsList removed) :
    let current := generalReplacementDevice removed pid p
    let baseline := replacementReadbackInputs d p.allowedipsList
    replacementOuter current = replacementOuter baseline ∧
    current.peerAllowedips.seq = baseline.peerAllowedips.seq ∧
    ∀ q : PeerId, current.peers[q]? = baseline.peers[q]? := by
  dsimp only
  refine ⟨?_,?_,?_⟩
  · have h := removalEffect_readback_outer steps
    exact h
  · have h := removalEffect_seq steps
    exact h
  · intro q
    by_cases same : q = pid
    · subst q
      simp only [generalReplacementDevice,withPeer,Std.TreeMap.getElem?_insert_self,
        replacementReadbackInputs,requestGeneration,Std.TreeMap.getElem?_map,resident,Option.map_some,
        erasePeerList_refcount_update]
      have count := erasePeerList_refcount p.allowedipsList p
      rw [← count]
    · have looked := removalEffect_peers steps q
      simpa [generalReplacementDevice,withPeer,Std.TreeMap.getElem?_insert,
        same,Ne.symm same,ite_false,replacementReadbackInputs,requestGeneration,
        Std.TreeMap.getElem?_map] using looked

end Leanux.Proofs.WG.Config
