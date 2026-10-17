import Leanux.Proofs.WG.Noise.ResponseTagModel
import Leanux.Proofs.WG.Noise.SlotFrames

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG Std.Do

/-- Local variant of Keypairs.Frames.WGTransitions.modifyPeer_spec.
The actual read supplies residency; arbitrary optional entry states are kept. -/
theorem modifyPeer_spec_creationTagMap_variant (entry : Option Device) (pid : PeerId)
    (f : Peer → Peer) (next : Option Nat → Option Nat)
    (tag : ∀p, some (f p).handshakeState = next (some p.handshakeState)) :
    Ensures (modifyPeer pid f)
      (fun g => responseTagMap g.dev = responseTagMap entry)
      (fun _ g => ∀target, responseTagMap g.dev target =
        if pid = target then next (responseTagMap entry target) else responseTagMap entry target) := by
  intro g ambient result final after pre run
  change (((do let p ← getPeer pid; setPeer pid (f p)) : WG.M Unit).run g).run ambient = _ at run
  cases device : g.dev with
  | none =>
    simp [getPeer,getDev,device,invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    cases resident : d.peers[pid]? with
    | none =>
      simp [getPeer,getDev,device,resident,invariant,AmbientM.invariant] at run
      cases run
    | some p =>
      simp [getPeer,getDev,device,resident,setPeer,modifyDev] at run
      rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
      intro target
      by_cases same : pid = target
      · subst target
        have prior := congrFun pre pid
        simp only [responseTagMap,device,Option.bind_some,resident,Option.map_some] at prior
        simpa [responseTagMap,← prior] using tag p
      · simpa [responseTagMap,device,Std.TreeMap.getElem?_insert,same] using congrFun pre target

end Leanux.Proofs.WG.Noise
