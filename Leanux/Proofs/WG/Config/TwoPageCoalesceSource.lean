import Leanux.Proofs.WG.Config.MultiPeerCoalesceSource
import Leanux.Proofs.WG.Config.MultiPeerDumpModel
set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Lean

/-- A fresh page appends every peer when the previous page has no partial
last peer. The empty-page flag and original attribute normalization remain. -/
theorem coalescePeers_complete_front (prior : Array PeerDumpAttrs) (ps : List PeerDumpAttrs)
    (safe : prior = #[] ∨ prior.back!.split = false) :
    forIn ps (prior,true) coalescePeerStep =
      (pure (prior ++ (ps.map peerDumpWithIps).toArray,ps.isEmpty) : WG.M _) := by
  cases ps with
  | nil => simp
  | cons p ps =>
    have noContinue : (true && prior.size > 0 && prior.back!.split &&
        prior.back!.publicKey == p.publicKey) = false := by
      rcases safe with empty | last
      · simp [empty]
      · simp [last]
    simp only [List.forIn_cons, coalescePeerStep, noContinue, Bool.false_eq_true, ite_false]
    change forIn ps (prior.push (peerDumpWithIps p),false) coalescePeerStep = _
    rw [coalescePeers_afterFirst]
    simp

/-- Fixed complete peer records have no partial last peer, including the
empty array's default value. Repeated peer IDs and keys are unrestricted. -/
theorem complete_parts_last (peers : PeerId → Peer) (ids : List PeerId) :
    ((multiPeerParts peers ids).map peerDumpWithIps).toArray = #[] ∨
    ((multiPeerParts peers ids).map peerDumpWithIps).toArray.back!.split = false := by
  right
  simp only [List.back!_toArray, List.getLast!_eq_getLast?_getD,
    multiPeerParts, List.map_map, List.getLast?_map]
  cases ids.getLast? <;> rfl

end Leanux.Proofs.WG.Config
