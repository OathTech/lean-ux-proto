import Leanux.Proofs.WG.Config.CollisionRemovalSource
import Leanux.Proofs.WG.Config.KeyRequest
import Leanux.Proofs.WG.Config.ScalarReturns

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem keyCollision_present_effect (d : Device) (key pub : Key) (pid : PeerId) (p : Peer)
    (generated : publicResult key = (some pub, true))
    (found : d.peerHashtable.find? (·.1 == pub) = some (pub, pid))
    (resident : d.peers[pid]? = some p) (pairs : NodePairs d)
    (live : 0 < p.refcount) (bounded : p.refcount + 1 < 2 ^ 31) (count : 0 < d.numPeers)
    (send : d.sendWorkQueue = []) (clear : d.clearWorkQueue = []) :
    Ensures (keyCollisionSource key) (fun w => w.k.wg = some d)
      (fun _ w => ∃ final, w.k.wg = some final ∧
        CollisionRemovalEffect pid (collisionLookupDevice d pid p) p final) := by
  let acquired := withPeer d pid { p with refcount := p.refcount + 1 }
  have hg : Ensures (generatePublic key) (fun w => w.k.wg = some d)
      (fun result w => result = (some pub, true) ∧ w.k.wg = some d) := by
    intro w result out pre run
    have actual := removal_returns_ensures (generatePublic_return key d) w result out pre run
    simpa only [generated] using actual
  have hl := removal_returns_ensures ((returns_iff _ _ _).mpr
    (pubkeyLookup_present_returns pub pid d p found resident live bounded))
  have hp : Ensures (peerPut (some pid)) (fun w => w.k.wg = some acquired)
      (fun _ w => w.k.wg = some (collisionLookupDevice d pid p)) := by
    intro w result out pre run
    have actual := removal_returns_ensures ((returns_iff _ _ _).mpr
      (peerPut_retained_returns pid acquired { p with refcount := p.refcount + 1 }
        (by simp [acquired, withPeer]) (by simpa using live))) w result out pre run
    simpa [collisionLookupDevice, acquired] using actual
  have hr := peerRemove_live_effect_pairs pid (collisionLookupDevice d pid p) p
    (by simp [collisionLookupDevice, withPeer]) pairs live count send clear
  have putRemove := ensures_bind _ _ hp (fun _ => hr)
  have afterLookup : Ensures (do
      if ← branch .setDevOldPeer (some pid).isSome then
        peerPut (some pid)
        peerRemove (some pid)) (fun w => w.k.wg = some acquired)
      (fun _ w => ∃ final, w.k.wg = some final ∧
        CollisionRemovalEffect pid (collisionLookupDevice d pid p) p final) := by
    refine ensures_bind _ _ (Q := fun result w => result = true ∧ w.k.wg = some acquired) ?_ ?_
    · rw [ensures_iff]
      mvcgen [branch]
    · intro result w u out pre run
      obtain ⟨rfl, device⟩ := pre
      exact putRemove w u out device run
  have lookup : Ensures (do
      let peer ← pubkeyLookup pub
      if ← branch .setDevOldPeer peer.isSome then
        peerPut peer
        peerRemove peer) (fun w => w.k.wg = some d)
      (fun _ w => ∃ final, w.k.wg = some final ∧
        CollisionRemovalEffect pid (collisionLookupDevice d pid p) p final) := by
    refine ensures_bind _ _ hl ?_
    intro result w u out pre run
    obtain ⟨rfl, device⟩ := pre
    exact afterLookup w u out device run
  have afterPublic : Ensures (do
      if ← branch .setDevGenPublic true then
        let peer ← pubkeyLookup pub
        if ← branch .setDevOldPeer peer.isSome then
          peerPut peer
          peerRemove peer) (fun w => w.k.wg = some d)
      (fun _ w => ∃ final, w.k.wg = some final ∧
        CollisionRemovalEffect pid (collisionLookupDevice d pid p) p final) := by
    refine ensures_bind _ _ (Q := fun result w => result = true ∧ w.k.wg = some d) ?_ ?_
    · rw [ensures_iff]
      mvcgen [branch]
    · intro result w u out pre run
      obtain ⟨rfl, device⟩ := pre
      exact lookup w u out device run
  unfold keyCollisionSource
  refine ensures_bind _ _ hg ?_
  intro result w u out pre run
  obtain ⟨rfl, device⟩ := pre
  exact afterPublic w u out device run

/-- Compose lookup/put/removal before installing from the actual resulting
device. No surviving-peer frame against request-entry state is used. -/
theorem setDevice_private_collision (d : Device) (key pub : Key) (pid : PeerId) (p : Peer)
    (changed : d.staticIdentity.staticPrivate ≠ key)
    (generated : publicResult key = (some pub, true))
    (found : d.peerHashtable.find? (·.1 == pub) = some (pub, pid))
    (resident : d.peers[pid]? = some p) (pairs : NodePairs d)
    (live : 0 < p.refcount) (bounded : p.refcount + 1 < 2 ^ 31) (count : 0 < d.numPeers)
    (send : d.sendWorkQueue = []) (clear : d.clearWorkQueue = []) :
    Ensures (wgSetDevice (privateKeyAttrs d key))
      (fun w => w.k.wg = some d ∧ selectsDevice w d)
      (fun ret w => ret = 0 ∧ ∃ final, w.k.wg = some final ∧
        CollisionKeyEffect pid (requestGeneration d) p key final) := by
  have hl := lookupInterface_index d
  have hc := (ensures_iff _ _ _).mp
    (keyCollision_present_effect (requestGeneration d) key pub pid p
      generated found resident pairs live bounded count send clear)
  have install : Ensures (keyInstallSource key)
      (fun w => ∃ baseline, w.k.wg = some baseline ∧
        CollisionRemovalEffect pid (collisionLookupDevice (requestGeneration d) pid p) p baseline)
      (fun _ w => ∃ final, w.k.wg = some final ∧
        CollisionKeyEffect pid (requestGeneration d) p key final) := by
    intro w result out pre run
    obtain ⟨baseline, device, removed⟩ := pre
    obtain ⟨final, actual, installed⟩ := keyInstall_complete baseline key w result out device run
    exact ⟨final, actual, baseline, removed, installed⟩
  have hi := (ensures_iff _ _ _).mp install
  rw [← wgSetDevice_source, ensures_iff]
  simp only [wgSetDeviceSource, deviceUpdateSource, ← devicePrivate_source]
  simp [devicePrivateSource, devicePeersSource, privateKeyAttrs, branch, bind_assoc,
    WG.andM, WG.orM, WGDEVICE_F_ALL, WGDEVICE_F_REPLACE_PEERS]
  mvcgen [getDev, getK, modifyDev, modifyK, invariant, hl, hc, hi]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [changed, requestGeneration]
  all_goals subst_vars
  all_goals simp_all
  all_goals grind only

end Leanux.Proofs.WG.Config
