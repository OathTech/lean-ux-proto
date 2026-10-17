import Leanux.Proofs.WG.Config.PeerScalars
import Leanux.Proofs.WG.Config.AllowedOwnerClear

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

def unlistPeer (d : Device) (pid : PeerId) : Device :=
  { d with peerList := d.peerList.filter (· != pid) }

def deadPeerDevice (removed : Device) (pid : PeerId) (p : Peer) : Device :=
  withPeer { removed with peerHashtable := removed.peerHashtable.filter (·.2 != pid) }
    pid { erasePeerList p.allowedipsList p with isDead := true }

def makeDeadAfterRemoval (pid : PeerId) : WG.M Unit := do
  _ ← branch .pubkeyRemoveHashed ((← getDev).peerHashtable.any (·.2 == pid))
  modifyDev fun d => { d with peerHashtable := d.peerHashtable.filter (·.2 != pid) }
  setPeer pid { (← getPeer pid) with isDead := true }

theorem peerMakeDead_source (pid : PeerId) :
    peerMakeDead pid = (do
      modifyDev (unlistPeer · pid)
      removeByPeer pid
      makeDeadAfterRemoval pid) := rfl

theorem peerMakeDead_returns (pid : PeerId) (p : Peer) (d removed : Device)
    (resident : d.peers[pid]? = some p)
    (steps : RemovalEffect (unlistPeer d pid) p.allowedipsList removed) :
    Returns (peerMakeDead pid) (fun w => w.dev = some d)
      (fun _ w => w.dev = some (deadPeerDevice removed pid p)) := by
  have removedPeer : removed.peers[pid]? = some (erasePeerList p.allowedipsList p) := by
    simpa only [unlistPeer, resident, Option.map_some] using removalEffect_peers steps pid
  have hl : Returns (modifyDev (unlistPeer · pid)) (fun w => w.dev = some d)
      (fun _ w => w.dev = some (unlistPeer d pid)) := by
    intro g ambient device
    refine ⟨(), {g with dev := some (unlistPeer d pid)}, ambient, ?_, rfl⟩
    simp [modifyDev, device]
    rfl
  have ht : Returns (makeDeadAfterRemoval pid) (fun w => w.dev = some removed)
      (fun _ w => w.dev = some (deadPeerDevice removed pid p)) := by
    intro g ambient device
    let after := {ambient with steps := ambient.steps.push {
      decision := .pubkeyRemoveHashed, outcome := removed.peerHashtable.any (·.2 == pid),
      netRx := ambient.netRxSection}}
    refine ⟨(), {g with dev := some (deadPeerDevice removed pid p)}, after, ?_, rfl⟩
    simp [makeDeadAfterRemoval, getDev, device, branch, AmbientM.branch, modifyDev,
      setPeer, getPeer, removedPeer, deadPeerDevice, withPeer, after]
    rfl
  rw [peerMakeDead_source]
  refine returns_bind _ _ hl ?_
  intro u
  refine returns_bind _ _ (removeByPeer_general pid p (unlistPeer d pid) removed resident steps) ?_
  intro u
  exact ht

theorem deadPeerDevice_effects (pid : PeerId) (p : Peer) (d removed : Device)
    (steps : RemovalEffect (unlistPeer d pid) p.allowedipsList removed) :
    let final := deadPeerDevice removed pid p
    final.peerList = d.peerList.filter (· != pid) ∧
    final.peerHashtable = d.peerHashtable.filter (·.2 != pid) ∧
    final.indexTable = d.indexTable ∧ final.numPeers = d.numPeers ∧
    final.peers[pid]? = some { erasePeerList p.allowedipsList p with isDead := true } ∧
    (erasePeerList p.allowedipsList p).allowedipsList = [] ∧
    (erasePeerList p.allowedipsList p).refcount = p.refcount ∧
    (∀ id ∈ p.allowedipsList, nodeOwner final id = none) := by
  have metadata := removalEffect_metadata steps
  have lists := congrArg (fun data => data.1) metadata
  have tables := congrArg (fun data => data.2.1) metadata
  have indices := congrArg (fun data => data.2.2.1) metadata
  have counts := congrArg (fun data => data.2.2.2) metadata
  refine ⟨lists, ?_, indices, counts, ?_, erasePeerList_own_empty p,
    erasePeerList_refcount _ p, ?_⟩
  · change removed.peerHashtable.filter (·.2 != pid) = _
    exact congrArg (fun table => table.filter (·.2 != pid)) tables
  · simp [deadPeerDevice, withPeer]
  · intro id member
    exact removalEffect_owner_none steps id (Or.inl member)

end Leanux.Proofs.WG.Config
