import Leanux.Proofs.WG.Config.CollisionRemovalSource
import Leanux.Proofs.WG.Config.RemoveFlagEffects
import Leanux.Proofs.WG.Config.ScalarReturns
import Leanux.Proofs.WG.Config.Flags

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem removeFlag_body (pid : PeerId) (d : Device) (p : Peer)
    (pairs : NodePairs d) (live : 0 < p.refcount) (count : 0 < d.numPeers)
    (send : d.sendWorkQueue = []) (clear : d.clearWorkQueue = []) :
    Ensures (do peerRemove (some pid); peerPut (some pid))
      (fun w => w.dev = some (withPeer d pid { p with refcount := p.refcount + 1 }))
      (fun _ w => ∃ final, w.dev = some final ∧ RemoveFlagEffect pid d p final) := by
  let acquired := { p with refcount := p.refcount + 1 }
  let entry := withPeer d pid acquired
  have removal := peerRemove_live_effect_pairs pid entry acquired
    (by simp [entry, withPeer]) pairs (by simp [acquired]) count send clear
  refine ensures_bind _ _ removal ?_
  intro u w ambient result out after pre run
  obtain ⟨removed, device, effect⟩ := pre
  obtain ⟨q, resident, refs⟩ := collisionRemoval_retained effect (by simpa [acquired] using live)
  have restored : q.refcount = p.refcount := by simpa [acquired] using refs
  have finish := Index.peerPut_exact pid removed q resident (by rwa [restored])
    w ambient device
  change (match Index.peerReleaseRefusal pid q with
    | some stop => Campaign2.observeResult (((peerPut (some pid)).run w).run ambient) = .error stop
    | none => ∃ final, Campaign2.observeResult (((peerPut (some pid)).run w).run ambient) = .ok ((), final) ∧
        final.wg.device = some (Index.releasedPeerDevice removed pid q)) at finish
  rw [run] at finish
  cases refusal : Index.peerReleaseRefusal pid q
  · rw [refusal] at finish
    obtain ⟨final, returned, post⟩ := finish
    simp only [Campaign2.observeResult, Except.map, Except.ok.injEq, Prod.mk.injEq] at returned
    obtain ⟨_, rfl⟩ := returned
    exact ⟨_, post, removed, q, effect, resident, restored, rfl⟩
  · rw [refusal] at finish
    cases finish

theorem removeFlag_update (a : PeerAttrs) (flags : UInt32) (psk : Option Key)
    (pid : PeerId) (d : Device) (p : Peer)
    (remove : flags &&& WGPEER_F_REMOVE_ME ≠ 0)
    (pairs : NodePairs d) (live : 0 < p.refcount) (count : 0 < d.numPeers)
    (send : d.sendWorkQueue = []) (clear : d.clearWorkQueue = []) :
    Ensures (peerConfigUpdateSource a (some pid) flags psk pid)
      (fun w => w.dev = some (withPeer d pid { p with refcount := p.refcount + 1 }))
      (fun ret w => ret = 0 ∧ ∃ final, w.dev = some final ∧ RemoveFlagEffect pid d p final) := by
  rw [peerUpdate_remove_source a (some pid) flags psk pid remove]
  have head : Ensures (branch .peerRemoveMe true : WG.M Bool)
      (fun w => w.dev = some (withPeer d pid { p with refcount := p.refcount + 1 }))
      (fun _ w => w.dev = some (withPeer d pid { p with refcount := p.refcount + 1 })) := by
    intro g ambient value final after pre run
    change Except.ok ((true, g), _) = Except.ok ((value, final), after) at run
    cases run
    exact pre
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
  intro g ambient value final after pre run
  change Except.ok ((0, g), _) = Except.ok ((value, final), after) at run
  cases run
  exact ⟨rfl, pre⟩

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
    Ensures (setPeerCmd a) (fun w => w.dev = some d)
      (fun ret w => ret = 0 ∧ ∃ final, w.dev = some final ∧ RemoveFlagEffect pid d p final) := by
  intro g ambient result final after device run
  have nonzero : p.refcount ≠ 0 := by omega
  have noOverflow : ¬ 2147483647 ≤ p.refcount := by omega
  rw [← setPeerCmd_source] at run
  rcases protocol with protocol | protocol
  all_goals cases psk : a.presharedKey
  all_goals simp [setPeerCmdSource, pubkey, flagattr, valid, protocol, psk,
    WG.andM, branch, branchCmp, AmbientM.branch, AmbientM.branchCmp,
    pubkeyLookup, peerGetMaybeZero, requireNotPending, refcountIncNotZero,
    getPeer, getDev, device, found, resident, nonzero, noOverflow, setPeer, modifyDev] at run
  all_goals exact removeFlag_update a flags _ pid d p remove pairs live count send clear _ _ result final after rfl run

end Leanux.Proofs.WG.Config
