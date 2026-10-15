import Leanux.Proofs.WG.Config.RemoveFlagEffects
import Leanux.Proofs.WG.Config.CollisionRemovalSource
import Leanux.Proofs.WG.Config.ScalarReturns

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem removeFlag_body (pid : PeerId) (d : Device) (p : Peer)
    (pairs : NodePairs d) (live : 0 < p.refcount) (count : 0 < d.numPeers)
    (send : d.sendWorkQueue = []) (clear : d.clearWorkQueue = []) :
    Ensures (do peerRemove (some pid); peerPut (some pid))
      (fun w => w.k.wg = some (withPeer d pid { p with refcount := p.refcount + 1 }))
      (fun _ w => ∃ final, w.k.wg = some final ∧ RemoveFlagEffect pid d p final) := by
  let acquired := { p with refcount := p.refcount + 1 }
  let entry := withPeer d pid acquired
  have removal := peerRemove_live_effect_pairs pid entry acquired
    (by simp [entry, withPeer]) pairs (by simp [acquired]) count send clear
  refine ensures_bind _ _ removal ?_
  intro u w result out pre run
  obtain ⟨removed, device, effect⟩ := pre
  obtain ⟨q, resident, refs⟩ := collisionRemoval_retained effect (by simpa [acquired] using live)
  have restored : q.refcount = p.refcount := by simpa [acquired] using refs
  have finish := removal_returns_ensures (Index.peerPut_exact pid removed q resident
    (by rwa [restored])) w result out device run
  exact ⟨_, finish, removed, q, effect, resident, restored, rfl⟩

theorem removeFlag_update (a : PeerAttrs) (flags : UInt32) (psk : Option Key)
    (pid : PeerId) (d : Device) (p : Peer)
    (remove : flags &&& WGPEER_F_REMOVE_ME ≠ 0)
    (pairs : NodePairs d) (live : 0 < p.refcount) (count : 0 < d.numPeers)
    (send : d.sendWorkQueue = []) (clear : d.clearWorkQueue = []) :
    Ensures (peerConfigUpdateSource a (some pid) flags psk pid)
      (fun w => w.k.wg = some (withPeer d pid { p with refcount := p.refcount + 1 }))
      (fun ret w => ret = 0 ∧ ∃ final, w.k.wg = some final ∧ RemoveFlagEffect pid d p final) := by
  rw [peerUpdate_remove_source a (some pid) flags psk pid remove]
  have head : Ensures (branch .peerRemoveMe true)
      (fun w => w.k.wg = some (withPeer d pid { p with refcount := p.refcount + 1 }))
      (fun _ w => w.k.wg = some (withPeer d pid { p with refcount := p.refcount + 1 })) := by
    rw [ensures_iff]
    mvcgen [branch]
  refine ensures_bind _ _ head (fun _ => ?_)
  have body := removeFlag_body pid d p pairs live count send clear
  have factor : (do
      peerRemove (some pid)
      peerPut (some pid)
      _ ← branch .peerZeroPsk a.presharedKey.isSome
      pure (0 : Int)) = (do
      _ ← (do peerRemove (some pid); peerPut (some pid))
      _ ← branch .peerZeroPsk a.presharedKey.isSome
      pure (0 : Int)) := by simp only [bind_assoc]
  rw [factor]
  refine ensures_bind _ _ body (fun _ => ?_)
  rw [ensures_iff]
  mvcgen [branch]


theorem setPeer_remove_flag (a : PeerAttrs) (key : Key) (flags : UInt32)
    (pid : PeerId) (d : Device) (p : Peer)
    (pubkey : a.publicKey = some key) (flagattr : a.flags = some flags)
    (valid : flags &&& ~~~WGPEER_F_ALL = 0)
    (protocol : a.protocolVersion = none ∨ a.protocolVersion = some 1)
    (remove : flags &&& WGPEER_F_REMOVE_ME ≠ 0)
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (resident : d.peers[pid]? = some p) (pairs : NodePairs d)
    (live : 0 < p.refcount) (bounded : p.refcount + 1 < 2 ^ 31)
    (count : 0 < d.numPeers) (send : d.sendWorkQueue = []) (clear : d.clearWorkQueue = []) :
    Ensures (setPeerCmd a) (fun w => w.k.wg = some d)
      (fun ret w => ret = 0 ∧ ∃ final, w.k.wg = some final ∧ RemoveFlagEffect pid d p final) := by
  have hl := (ensures_iff _ _ _).mp (removal_returns_ensures
    ((returns_iff _ _ _).mpr (pubkeyLookup_present_returns key pid d p found resident live bounded)))
  have hu := fun psk => (ensures_iff _ _ _).mp
    (removeFlag_update a flags psk pid d p remove pairs live count send clear)
  rw [← setPeerCmd_source, ensures_iff]
  simp only [setPeerCmdSource, pubkey, flagattr, Option.isSome_some, Option.getD_some]
  mvcgen [WG.andM, branch, invariant, hl, hu]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all
  all_goals subst_vars
  all_goals try simp_all
  all_goals exact hu _ _ (by simp_all)

end Leanux.Proofs.WG.Config
