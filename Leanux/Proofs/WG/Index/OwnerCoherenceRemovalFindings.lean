import Leanux.Proofs.WG.Index.OwnerCoherenceModel
import Leanux.Proofs.WG.Index.OwnerCoherenceRemovalFindingModel
import Leanux.Proofs.WG.Config.QuietRemoval

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG

/-- The whole original removal, not merely its final peerPut, can normally
remove a peer while retaining a hashed keypair that names it. The entry is
locally owner-coherent; the theorem quantifies every Ambient and native state
realizing this Device. It is a missing lifecycle-invariant finding, not a
reachable-state or driver-bug claim. -/
theorem peerRemove_ownerCoherentSafe_counterexample :
    HashedOwnersCoherent RemovalOwnerWitness.device ∧
    Campaign2.Observes (peerRemove (some 0))
      (fun s => s.wg.device = some RemovalOwnerWitness.device)
      (fun _ out => ∃ final, out = .ok ((), final) ∧
        final.wg.device = some RemovalOwnerWitness.finalDevice ∧
        ¬ View.OwnerCoherentSafe final) := by
  let p := RemovalOwnerWitness.peer
  let k := RemovalOwnerWitness.key
  let e := RemovalOwnerWitness.entry
  let d := RemovalOwnerWitness.device
  have coherent : HashedOwnersCoherent d := by
    intro item member
    have same : item = e := by simpa [d, RemovalOwnerWitness.device] using member
    subst item
    refine ⟨0, p, ?_, ?_, ?_, ?_⟩
    · simp [ownerWord, e, d, RemovalOwnerWitness.entry,
        RemovalOwnerWitness.device, RemovalOwnerWitness.key]
    · simp [d, p, RemovalOwnerWitness.device]
    · decide
    · exact ⟨k, by simp [d, k, RemovalOwnerWitness.device], by decide⟩
  have resident : d.peers[0]? = some p := by simp [d, p, RemovalOwnerWitness.device]
  have live : 0 < p.refcount := by decide
  have count : 0 < d.numPeers := by decide
  have empty : p.keypairNext = none ∧ p.keypairPrevious = none ∧ p.keypairCurrent = none := by decide
  have send : d.sendWorkQueue = [] := rfl
  have clear : d.clearWorkQueue = [] := rfl
  have removal : Config.RemovalEffect (Config.unlistPeer d 0) p.allowedipsList
      (Config.unlistPeer d 0) := rfl
  refine ⟨coherent, ?_⟩
  intro g ambient device
  have specialized (input : Device) (selected : Peer)
      (found : input.peers[0]? = some selected) (positive : 0 < selected.refcount)
      (number : 0 < input.numPeers)
      (slots : selected.keypairNext = none ∧ selected.keypairPrevious = none ∧ selected.keypairCurrent = none)
      (sendEmpty : input.sendWorkQueue = []) (clearEmpty : input.clearWorkQueue = [])
      (noList : selected.allowedipsList = []) :
      Campaign2.Observes (peerRemove (some 0)) (fun s => s.wg.device = some input)
        (fun _ out => Config.quietRemovalOutcome
          (Config.deadPeerDevice (Config.unlistPeer input 0) 0 selected) 0
          {selected with isDead := true} out) := by
    have steps : Config.RemovalEffect (Config.unlistPeer input 0) selected.allowedipsList
        (Config.unlistPeer input 0) := by rw [noList]; rfl
    have source := Config.peerRemove_quiet_returns 0 input (Config.unlistPeer input 0) selected
      found positive number slots sendEmpty clearEmpty steps
    simpa only [noList, Config.erasePeerList] using source
  generalize inputEq : RemovalOwnerWitness.device = input at device
  generalize selectedEq : RemovalOwnerWitness.peer = selected
  have found : input.peers[0]? = some selected := by rw [← inputEq, ← selectedEq]; exact resident
  have positive : 0 < selected.refcount := by rw [← selectedEq]; exact live
  have number : 0 < input.numPeers := by rw [← inputEq]; exact count
  have slots : selected.keypairNext = none ∧ selected.keypairPrevious = none ∧ selected.keypairCurrent = none := by
    rw [← selectedEq]; exact empty
  have sendEmpty : input.sendWorkQueue = [] := by rw [← inputEq]; exact send
  have clearEmpty : input.clearWorkQueue = [] := by rw [← inputEq]; exact clear
  have noList : selected.allowedipsList = [] := by rw [← selectedEq]; rfl
  have full := specialized input selected found positive number slots sendEmpty clearEmpty noList
  have actual := full g ambient device
  rw [← inputEq, ← selectedEq] at actual
  change Config.quietRemovalOutcome RemovalOwnerWitness.deadDevice 0
    RemovalOwnerWitness.deadPeer
    (Campaign2.observeResult (((peerRemove (some 0)).run g).run ambient)) at actual
  let cleaned := Config.quietCleanupDevice RemovalOwnerWitness.deadDevice 0 RemovalOwnerWitness.deadPeer
  have singletonReplace (old new : Peer) :
      ((({} : Std.TreeMap PeerId Peer).insert 0 old).insert 0 new) =
        ({} : Std.TreeMap PeerId Peer).insert 0 new := rfl
  have cleanup : cleaned = RemovalOwnerWitness.deadDevice := by
    simp [cleaned, Config.quietCleanupDevice, Config.deleteTimersDevice, Config.emptyKeysDevice,
      Config.emptyKeysPeer, PeerTimer.all, Peer.setTimer, Peer.setWheel, Config.withPeer,
      RemovalOwnerWitness.deadPeer, RemovalOwnerWitness.deadDevice, Config.deadPeerDevice,
      Config.erasePeerList, RemovalOwnerWitness.peer, Config.unlistPeer,
      RemovalOwnerWitness.device, singletonReplace]
  have noCrypt : (!cleaned.encryptQueue.empty || !cleaned.decryptQueue.empty ||
      !cleaned.txWorkQueue.isEmpty || cleaned.peers.toList.any (·.2.napiScheduled)) = false := by
    rw [cleanup]
    simp [RemovalOwnerWitness.deadDevice, Config.deadPeerDevice, Config.withPeer,
      Config.unlistPeer, RemovalOwnerWitness.device, RemovalOwnerWitness.peer,
      Config.erasePeerList, singletonReplace, PtrRing.empty, PtrRing.peek, PtrRing.init,
      Std.TreeMap.getElem?_insert]
    simp [MAX_QUEUED_PACKETS]
  have peerSame : Config.quietCleanupPeer RemovalOwnerWitness.deadPeer = RemovalOwnerWitness.deadPeer := rfl
  have noPackets : (RemovalOwnerWitness.deadPeer.txQueue.peeked.isSome ||
      !RemovalOwnerWitness.deadPeer.txQueue.items.isEmpty ||
      RemovalOwnerWitness.deadPeer.rxQueue.peeked.isSome ||
      !RemovalOwnerWitness.deadPeer.rxQueue.items.isEmpty) = false := by decide
  have noTimers : (PeerTimer.all.find? (fun t => RemovalOwnerWitness.deadPeer.timerPending t ||
      (RemovalOwnerWitness.deadPeer.wheel t).isSome)) = none := by decide
  unfold Config.quietRemovalOutcome at actual
  change (if (!cleaned.encryptQueue.empty || !cleaned.decryptQueue.empty ||
      !cleaned.txWorkQueue.isEmpty || cleaned.peers.toList.any (·.2.napiScheduled)) then _ else _) at actual
  rw [noCrypt] at actual
  simp only [Bool.false_eq_true, peerSame,
    show RemovalOwnerWitness.deadPeer.refcount = 1 from rfl, ↓reduceIte,
    noPackets, noTimers, Option.map_none] at actual
  obtain ⟨final, normal, finalDevice⟩ := actual
  refine ⟨final, normal, finalDevice, ?_⟩
  intro safe
  have resultShape : RemovalOwnerWitness.finalDevice =
      releasedPeerDevice {RemovalOwnerWitness.deadDevice with numPeers := 0} 0
        RemovalOwnerWitness.deadPeer := by
    unfold RemovalOwnerWitness.finalDevice Config.quietRemovedDevice
    rw [peerSame, show Config.quietCleanupDevice RemovalOwnerWitness.deadDevice 0
      RemovalOwnerWitness.deadPeer = RemovalOwnerWitness.deadDevice from cleanup]
    rfl
  have member : e ∈ RemovalOwnerWitness.finalDevice.indexTable := by
    rw [resultShape]
    simp [releasedPeerDevice, RemovalOwnerWitness.deadPeer, RemovalOwnerWitness.peer,
      RemovalOwnerWitness.deadDevice, Config.deadPeerDevice, Config.withPeer,
      Config.unlistPeer, RemovalOwnerWitness.device, removeOwner, e, RemovalOwnerWitness.entry]
  have bad := safe RemovalOwnerWitness.finalDevice finalDevice e member
  obtain ⟨pid, q, word, found, positive, owner⟩ := bad
  have absent : RemovalOwnerWitness.finalDevice.peers[pid]? = none := by
    rw [resultShape]
    simp [releasedPeerDevice, RemovalOwnerWitness.deadPeer, RemovalOwnerWitness.peer,
      RemovalOwnerWitness.deadDevice, Config.deadPeerDevice, Config.withPeer,
      Config.unlistPeer, RemovalOwnerWitness.device]
  rw [absent] at found
  cases found

end Leanux.Proofs.WG.Index
