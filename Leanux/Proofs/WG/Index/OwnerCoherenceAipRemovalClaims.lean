import Leanux.Proofs.WG.Index.OwnerCoherenceAipRemovalSource
import Leanux.Proofs.WG.Index.OwnerCoherenceSlotRemovalSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Std.Do

/-- Whole peer removal preserves local owner coherence under last-reference
slot coverage, with arbitrary allowed-IP lists and node representations. Empty
handshake work queues remain required; no trie/readiness/budget premise is added. -/
theorem peerRemove_covered_owner_coherent (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount)
    (count : 0 < d.numPeers) (send : d.sendWorkQueue = []) (clear : d.clearWorkQueue = [])
    (covered : LastOwnerCovered d pid p) :
    Campaign2.Ensures (peerRemove (some pid))
      (fun s => s.wg.device = some d ∧ View.OwnerCoherentSafe s)
      (fun _ s => View.OwnerCoherentSafe s) := by
  intro g ambient value final after pre run
  let afterNull := {ambient with steps := ambient.steps.push {
    decision := .peerRemoveNull, outcome := false, netRx := ambient.netRxSection}}
  have factor : ((peerRemove (some pid)).run g).run ambient =
      (((peerMakeDead pid).run g).run afterNull >>= fun ((_,state),inputs) =>
        ((peerRemoveAfterDead pid).run state).run inputs) := rfl
  rw [factor] at run
  cases made : ((peerMakeDead pid).run g).run afterNull with
  | error stop => rw [made] at run; cases run
  | ok output =>
    rcases output with ⟨⟨u,current⟩,middle⟩
    rw [made] at run
    obtain ⟨dead,q,device,found,deadFlag,refs,safe,coverage,number,sendFrame,clearFrame⟩ :=
      peerMakeDead_spec_aipOwner_variant pid d p resident (pre.2 d pre.1) covered
        g afterNull u current middle pre.1 made
    have currentSafe : View.OwnerCoherentSafe (Campaign2.snapshot current middle) := by
      intro observed present
      change current.dev = some observed at present
      rw [device] at present
      cases present
      exact safe
    exact peerRemoveAfterDead_slot_owner_coherent pid dead q found deadFlag
      (by rw [refs]; exact live) (by rw [number]; exact count)
      (sendFrame.trans send) (clearFrame.trans clear) coverage
      current middle value final after ⟨device,currentSafe⟩ run

end Leanux.Proofs.WG.Index
