import Leanux.Proofs.WG.Index.ResponseIndexModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Std.Do Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues Queues.RxCredits Queues.RxCredits.DurableHolders

theorem endpointBounds_affiliation (d e : Device)
    (same : Affiliation.state e = Affiliation.state d)
    (pre : InitializedBounds.EndpointBounds d) : InitializedBounds.EndpointBounds e := by
  refine ⟨same ▸ pre.slots,?_,?_⟩
  · intro pid p resident
    have cells := congrFun (congrArg Affiliation.State.peers same) pid
    have old : d.peers[pid]?.map Affiliation.peerCell = some (Affiliation.peerCell p) := by
      simpa only [Affiliation.state,resident,Option.map_some] using cells.symm
    obtain ⟨q,found,_⟩ := Option.map_eq_some_iff.mp old
    have frontier := congrArg Affiliation.State.nextPeer same
    change e.nextPeer = d.nextPeer at frontier
    rw [frontier]
    exact pre.peers pid q found
  · intro kid key resident
    have cells := congrFun (congrArg Affiliation.State.keys same) kid
    have old : d.keypairs[kid]?.map Affiliation.keyCell = some (Affiliation.keyCell key) := by
      simpa only [Affiliation.state,resident,Option.map_some] using cells.symm
    obtain ⟨k,found,_⟩ := Option.map_eq_some_iff.mp old
    have frontier := congrArg Affiliation.State.nextKey same
    change e.nextKeypairId = d.nextKeypairId at frontier
    rw [frontier]
    exact pre.keys kid k found

end Leanux.Proofs.WG.Index
