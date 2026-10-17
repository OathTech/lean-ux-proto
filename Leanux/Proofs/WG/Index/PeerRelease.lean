import Leanux.Proofs.WG.Index.Release
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Config Std.Do

/-- Corrected exact outcome of the original resident, positive-reference domain.
Final release may stop at the queue or timer invariant; all other runs return the
original ordered device effect. This is a semantic correction, not a totality
claim with new readiness hypotheses. -/
theorem peerPut_exact (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount) :
    Campaign2.Observes (peerPut (some pid)) (fun s => s.wg.device = some d)
      (fun _ out =>
        let refusal : Option Stop := if p.refcount = 1 then
          if p.txQueue.peeked.isSome || !p.txQueue.items.isEmpty ||
              p.rxQueue.peeked.isSome || !p.rxQueue.items.isEmpty then
            some (.invariant "rcu_release: a released peer with packets on its tx_queue or rx_queue (peer.c:191)")
          else (PeerTimer.all.find? (fun t => p.timerPending t || (p.wheel t).isSome)).map
            (fun t => .invariant s!"peer {pid} released with its {repr t} timer pending")
        else none
        match refusal with
        | some stop => out = .error stop
        | none => ∃ final, out = .ok ((), final) ∧
            final.wg.device = some (releasedPeerDevice d pid p)) := by
  intro g ambient device
  change g.dev = some d at device
  have nonzero : p.refcount ≠ 0 := by omega
  have removeForm : indexRemove (.handshake pid) = (do
    _ ← branch .idxRemoveHashed ((← get).any (·.owner == .handshake pid))
    modify fun table => table.filter fun e => !(e.owner == .handshake pid) : IndexM Unit) := rfl
  have lifted : (monadLift (indexRemove (.handshake pid)) : WG.M Unit) =
      liftIndex (indexRemove (.handshake pid)) := rfl
  by_cases last : p.refcount = 1
  · cases queued : (p.txQueue.peeked.isSome || !p.txQueue.items.isEmpty ||
        p.rxQueue.peeked.isSome || !p.rxQueue.items.isEmpty)
    · have queuedProp : ¬(((p.txQueue.peeked.isSome = true ∨ ¬p.txQueue.items = []) ∨
          p.rxQueue.peeked.isSome = true) ∨ ¬p.rxQueue.items = []) := by simpa using queued
      cases timer : PeerTimer.all.find? (fun t => p.timerPending t || (p.wheel t).isSome)
      all_goals simp only [peerPut, lifted]
      all_goals simp [requireNotPending, getPeer, getDev, setPeer, modifyDev,
        refcountDecAndTest, branch, branchCmp, AmbientM.branch, AmbientM.branchCmp,
        removeForm, liftIndex, invariant, AmbientM.invariant, retirePeerUnits,
        Campaign2.observeResult, Campaign2.snapshot, Campaign2.core,
        device, resident, last, queuedProp, timer, releasedPeerDevice, removeOwner]
      all_goals first | exact ⟨_, rfl, rfl⟩ | rfl
    · have queuedProp : ((p.txQueue.peeked.isSome = true ∨ ¬p.txQueue.items = []) ∨
          p.rxQueue.peeked.isSome = true) ∨ ¬p.rxQueue.items = [] := by simpa using queued
      simp only [peerPut, lifted]
      simp [requireNotPending, getPeer, getDev, setPeer, modifyDev,
        refcountDecAndTest, branch, branchCmp, AmbientM.branch, AmbientM.branchCmp,
        removeForm, liftIndex, invariant, AmbientM.invariant,
        Campaign2.observeResult, device, resident, last, queuedProp]
      rfl
  · simp only [peerPut, lifted]
    simp [requireNotPending, getPeer, getDev, setPeer, modifyDev,
      refcountDecAndTest, branch, branchCmp, AmbientM.branch, AmbientM.branchCmp,
      Campaign2.observeResult, Campaign2.snapshot, Campaign2.core,
      device, resident, live, nonzero, last, releasedPeerDevice]
    exact ⟨_, rfl, rfl⟩

end Leanux.Proofs.WG.Index
