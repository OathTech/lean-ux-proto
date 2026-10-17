import Leanux.Proofs.WG.Index.OwnerCoherenceQuietRemovalModel
import Leanux.Proofs.WG.Index.OwnerCoherenceSessionFrames
import Leanux.Proofs.WG.Index.OwnerCoherenceReleaseFrames
import Leanux.Proofs.WG.Index.OwnerCoherenceDecrementFrames
import Leanux.Proofs.WG.Config.QuietRemovalFrames

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG

/-- Rewriting the released peer without changing its reference count retains
the detachment obligation: the surviving owners exclude its own handshake. -/
theorem peerWrite_lastOwnerDetached (d : Device) (pid : PeerId) (p q : Peer)
    (count : q.refcount = p.refcount) (detached : LastOwnerDetached d pid p) :
    LastOwnerDetached {d with peers := d.peers.insert pid q} pid q := by
  intro last e member kept
  have old := detached (count ▸ last) e member kept
  cases owner : e.owner with
  | keypair id => simpa only [owner, ownerWord] using old
  | handshake own =>
    have different : pid ≠ own := by intro same; subst own; exact kept owner
    simpa [owner, ownerWord, Std.TreeMap.getElem?_insert, different] using old

/-- The actual quiet cleanup's ordered slot and timer writes retain owner
coherence and the entry detachment condition, including all peer aliases. -/
theorem quietCleanup_owner_conditions (d : Device) (pid : PeerId) (p : Peer)
    (resident : d.peers[pid]? = some p) (coherent : HashedOwnersCoherent d)
    (detached : LastOwnerDetached d pid p) :
    HashedOwnersCoherent (Config.quietCleanupDevice d pid p) ∧
      LastOwnerDetached (Config.quietCleanupDevice d pid p) pid (Config.quietCleanupPeer p) := by
  have write (before : Device) (old new : Peer)
      (found : before.peers[pid]? = some old)
      (word : new.handshakeEntryPeer = old.handshakeEntryPeer)
      (count : new.refcount = old.refcount)
      (safe : HashedOwnersCoherent before ∧ LastOwnerDetached before pid old) :
      HashedOwnersCoherent (Config.withPeer before pid new) ∧
        LastOwnerDetached (Config.withPeer before pid new) pid new :=
    ⟨peerWrite_owner_coherent before pid old new found word count safe.1,
      peerWrite_lastOwnerDetached before pid old new count safe.2⟩
  have timers (ts : List PeerTimer) (before : Device) (old : Peer)
      (found : before.peers[pid]? = some old)
      (safe : HashedOwnersCoherent before ∧ LastOwnerDetached before pid old) :
      HashedOwnersCoherent (Config.deleteTimersDevice ts before pid old) ∧
        LastOwnerDetached (Config.deleteTimersDevice ts before pid old) pid
          (Config.deleteTimersPeer ts old) := by
    induction ts generalizing before old with
    | nil => exact safe
    | cons t ts ih =>
      exact ih (Config.withPeer before pid ((old.setTimer t none).setWheel t none))
        ((old.setTimer t none).setWheel t none) (by simp [Config.withPeer])
        (write before old _ found (by cases t <;> rfl) (by cases t <;> rfl) safe)
  have first := write d p {p with keypairNext := none} resident rfl rfl ⟨coherent,detached⟩
  have second := write (Config.withPeer d pid {p with keypairNext := none})
    {p with keypairNext := none} {p with keypairNext := none, keypairPrevious := none}
    (by simp [Config.withPeer]) rfl rfl first
  have third := write
    (Config.withPeer (Config.withPeer d pid {p with keypairNext := none}) pid
      {p with keypairNext := none, keypairPrevious := none})
    {p with keypairNext := none, keypairPrevious := none} (Config.emptyKeysPeer p)
    (by simp [Config.withPeer]) rfl rfl second
  exact timers PeerTimer.all (Config.emptyKeysDevice d pid p) (Config.emptyKeysPeer p)
    (by simp [Config.emptyKeysDevice, Config.withPeer]) third

/-- The quiet cleanup and count decrement transport the entry condition to
the exact last-reference or retained-reference peer release. -/
theorem quietRemoved_owner_coherent (d : Device) (pid : PeerId) (p : Peer)
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount)
    (coherent : HashedOwnersCoherent d) (detached : LastOwnerDetached d pid p) :
    HashedOwnersCoherent (Config.quietRemovedDevice d pid p) := by
  obtain ⟨safe,detached⟩ := quietCleanup_owner_conditions d pid p resident coherent detached
  generalize cleanedEq : Config.quietCleanupDevice d pid p = cleaned at safe detached ⊢
  generalize peerEq : Config.quietCleanupPeer p = released at detached ⊢
  have refcount : released.refcount = p.refcount := by
    rw [← peerEq]
    exact Config.quietCleanup_refcount p
  have found : cleaned.peers[pid]? = some released := by
    rw [← cleanedEq, ← peerEq]
    exact Config.quietCleanup_resident d pid p
  unfold Config.quietRemovedDevice
  rw [cleanedEq, peerEq]
  by_cases last : released.refcount = 1
  · exact (lastPeerRelease_coherent_iff {cleaned with numPeers := cleaned.numPeers - 1}
      pid released last safe).mpr (detached last)
  · exact nonlastPeerRelease_coherent {cleaned with numPeers := cleaned.numPeers - 1}
      pid released found (by rw [refcount] at last ⊢; omega) safe

/-- Dead-marking and unlisting change no owner word or reference count; the
quiet full-removal transform then preserves coherence from entry detachment. -/
theorem quietRemovedDead_owner_coherent (d : Device) (pid : PeerId) (p : Peer)
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount)
    (noList : p.allowedipsList = []) (coherent : HashedOwnersCoherent d)
    (detached : LastOwnerDetached d pid p) :
    HashedOwnersCoherent (Config.quietRemovedDevice
      (Config.deadPeerDevice (Config.unlistPeer d pid) pid p) pid {p with isDead := true}) := by
  let unlisted : Device := {Config.unlistPeer d pid with
    peerHashtable := d.peerHashtable.filter (·.2 != pid)}
  let dead := Config.deadPeerDevice (Config.unlistPeer d pid) pid p
  let marked := {p with isDead := true}
  have shape : dead = Config.withPeer unlisted pid marked := by
    simp only [dead, Config.deadPeerDevice, unlisted, marked, Config.unlistPeer,
      noList, Config.erasePeerList]
  have safeDead : HashedOwnersCoherent dead := by
    rw [shape]
    exact peerWrite_owner_coherent unlisted pid p marked resident rfl rfl coherent
  have detachDead : LastOwnerDetached dead pid marked := by
    rw [shape]
    exact peerWrite_lastOwnerDetached unlisted pid p marked rfl detached
  have residentDead : dead.peers[pid]? = some marked := by rw [shape]; simp [Config.withPeer]
  exact quietRemoved_owner_coherent dead pid marked residentDead live safeDead detachDead

end Leanux.Proofs.WG.Index
