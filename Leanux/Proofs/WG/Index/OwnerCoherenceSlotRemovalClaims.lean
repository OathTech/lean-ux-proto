import Leanux.Proofs.WG.Index.OwnerCoherenceSlotRemovalSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise

/-- Whole removal with live or aliased key slots preserves local owner coherence
when all owners naming a last-reference peer are covered by its original slots
or its own handshake. Actual clear/refcount and cleanup refusals are retained. -/
theorem peerRemove_slot_owner_coherent (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount)
    (count : 0 < d.numPeers) (noList : p.allowedipsList = [])
    (send : d.sendWorkQueue = []) (clear : d.clearWorkQueue = [])
    (covered : LastOwnerCovered d pid p) :
    Campaign2.Ensures (peerRemove (some pid))
      (fun s => s.wg.device = some d ∧ View.OwnerCoherentSafe s)
      (fun _ s => View.OwnerCoherentSafe s) := by
  intro g ambient value final after pre run
  have removal : Config.RemovalEffect (Config.unlistPeer d pid) p.allowedipsList
      (Config.unlistPeer d pid) := by rw [noList]; rfl
  let afterNull := {ambient with steps := ambient.steps.push {
    decision := .peerRemoveNull, outcome := false, netRx := ambient.netRxSection}}
  obtain ⟨u,current,middle,made,currentDevice⟩ :=
    Config.peerMakeDead_returns pid p d (Config.unlistPeer d pid) resident removal g afterNull pre.1
  cases u
  let unlisted : Device := {Config.unlistPeer d pid with
    peerHashtable := d.peerHashtable.filter (·.2 != pid)}
  let dead := Config.deadPeerDevice (Config.unlistPeer d pid) pid p
  let marked := {p with isDead := true}
  have shape : dead = Config.withPeer unlisted pid marked := by
    simp only [dead,Config.deadPeerDevice,unlisted,marked,Config.unlistPeer,
      noList,Config.erasePeerList]
  have coherent : HashedOwnersCoherent dead := by
    rw [shape]
    exact peerWrite_owner_coherent unlisted pid p marked resident rfl rfl (pre.2 d pre.1)
  have coveredDead : LastOwnerCovered dead pid marked := by
    rw [shape]
    exact peerWrite_lastOwnerCovered unlisted pid p marked rfl rfl covered
  have residentDead : dead.peers[pid]? = some marked := by rw [shape]; simp [Config.withPeer]
  have source : ((peerRemove (some pid)).run g).run ambient =
      ((peerRemoveAfterDead pid).run current).run middle := by
    change (((peerMakeDead pid).run g).run afterNull >>= fun ((_, state), inputs) =>
      ((peerRemoveAfterDead pid).run state).run inputs) = _
    rw [made]
    rfl
  have safe : View.OwnerCoherentSafe (Campaign2.snapshot current middle) := by
    intro observed present
    change current.dev = some observed at present
    rw [currentDevice] at present
    cases present
    exact coherent
  exact peerRemoveAfterDead_slot_owner_coherent pid dead marked residentDead rfl live count
    send clear coveredDead current middle value final after ⟨currentDevice,safe⟩ (source ▸ run)

end Leanux.Proofs.WG.Index
