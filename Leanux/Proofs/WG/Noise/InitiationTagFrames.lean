import Leanux.Proofs.WG.Noise.ResponseTagFrames

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG Std.Do

/-- Local read/write variant of Keypairs.Frames.WGTransitions.modifyPeer_spec for
all tags and the reference actually held by this consumer. -/
theorem modifyPeer_spec_initiationTagMap_variant (entry : Option Device) (pid : PeerId)
    (f : Peer → Peer) (tag : ∀p, (f p).handshakeState = p.handshakeState)
    (count : ∀p, (f p).refcount = p.refcount) :
    Ensures (modifyPeer pid f) (ResponseTagHeld entry pid)
      (fun _ => ResponseTagHeld entry pid) := by
  intro g ambient result final after pre run
  obtain ⟨same,d,p,device,resident,retained⟩ := pre
  change (((do let p ← getPeer pid; setPeer pid (f p)) : WG.M Unit).run g).run ambient = _ at run
  simp [getPeer, getDev, device, resident, setPeer, modifyDev] at run
  rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
  refine ⟨?_,_,f p,rfl,by simp,?_⟩
  · exact (tagMap_write d pid p (f p) resident (tag p)).trans (by simpa [device] using same)
  · simpa only [count] using retained

end Leanux.Proofs.WG.Noise
