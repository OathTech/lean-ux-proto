import Leanux.Proofs.WG.Roaming.Frames
import Leanux.Proofs.WG.Noise.SlotFrames
import Leanux.Proofs.WG.Queues.RxPollPrimitives
import Leanux.Proofs.WG.Keypairs.MaterialOrigin

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Noise Lifetimes Leanux.Proofs.Framing Std.Do

theorem modifyPeer_remotes (pid : PeerId) (f : Peer → Peer)
    (kept : ∀p, (f p).endpoint.map destination = p.endpoint.map destination) :
    SameView destinationAt (modifyPeer pid f) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g ambient result final after run
  change (((getPeer pid >>= fun p => setPeer pid (f p)).run g).run ambient) = _ at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨p,middle,inputs,read,write⟩ := run
  obtain ⟨same,records,d,device,resident⟩ :=
    Queues.getPeer_normal pid g middle p ambient inputs read
  subst middle
  subst inputs
  cases write
  funext target
  by_cases equal : pid = target
  · subst target
    simp [destinationAt,peerAt,device,resident,kept]
  · simp [destinationAt,peerAt,device,Std.TreeMap.getElem?_insert,equal]

theorem modifyDev_remotes (f : Device → Device) (peers : ∀ d, (f d).peers = d.peers) :
    SameView destinationAt (modifyDev f) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g ambient result final after run
  cases run
  funext pid
  simp [destinationAt,peerAt,Option.bind_map,Function.comp_def,peers]

end Leanux.Proofs.WG.Roaming
