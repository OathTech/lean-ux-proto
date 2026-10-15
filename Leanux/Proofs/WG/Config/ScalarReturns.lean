import Leanux.Proofs.WG.Config.PeerScalars
import Leanux.Proofs.WG.Config.Returns

set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem pubkeyLookup_present_returns (key : Key) (pid : PeerId) (d : Device) (p : Peer)
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount) (bounded : p.refcount + 1 < 2 ^ 31) :
    ⦃fun w => ⌜w.k.wg = some d⌝⦄ pubkeyLookup key
    ⦃⇓ ret w => ⌜ret = some pid ∧ w.k.wg = some
      (withPeer d pid { p with refcount := p.refcount + 1 })⌝⦄ := by
  mvcgen [pubkeyLookup, peerGetMaybeZero, requireNotPending, refcountIncNotZero,
    branch, branchCmp, getPeer, getDev, getK, setPeer, modifyDev, modifyK,
    invariant, unsupported]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [-List.find?_eq_none, withPeer]
  all_goals grind only

theorem peerPut_retained_returns (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (retained : 1 < p.refcount) :
    ⦃fun w => ⌜w.k.wg = some d⌝⦄ peerPut (some pid)
    ⦃⇓ _ w => ⌜w.k.wg = some (withPeer d pid { p with refcount := p.refcount - 1 })⌝⦄ := by
  mvcgen [peerPut, requireNotPending, refcountDecAndTest, branch, branchCmp,
    getPeer, getDev, getK, setPeer, modifyDev, modifyK, invariant, unsupported]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [withPeer]
  all_goals omega

theorem scalarTail_down_returns (key psk : Key) (interval : Nat) (pid : PeerId)
    (d : Device) (p : Peer) (resident : d.peers[pid]? = some p)
    (down : d.running = false) (retained : 1 < p.refcount) :
    ⦃fun w => ⌜w.k.wg = some d⌝⦄ peerConfigTailSource (scalarAttrs key psk interval) (some pid) pid
    ⦃⇓ ret w => ⌜ret = 0 ∧ w.k.wg = some (withPeer (withPeer d pid { p with persistentKeepaliveInterval := interval }) pid
      { p with persistentKeepaliveInterval := interval, refcount := p.refcount - 1 })⌝⦄ := by
  let p1 := { p with persistentKeepaliveInterval := interval }
  let d1 := withPeer d pid p1
  have hp := peerPut_retained_returns pid d1 p1
    (by simp [d1, withPeer]) (by simpa [p1] using retained)
  simp [peerConfigTailSource, scalarAttrs]
  mvcgen [Leanux.WG.andM, branch, getPeer, getDev, getK, setPeer,
    modifyDev, modifyK, invariant, hp]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [withPeer, d1, p1]
  all_goals grind only

theorem scalarUpdate_down_returns (key psk : Key) (interval : Nat) (pid : PeerId)
    (d : Device) (p : Peer) (resident : d.peers[pid]? = some p)
    (down : d.running = false) (retained : 1 < p.refcount) :
    ⦃fun w => ⌜w.k.wg = some d⌝⦄
      peerConfigUpdateSource (scalarAttrs key psk interval) (some pid) 0 (some psk) pid
    ⦃⇓ ret w => ⌜ret = 0 ∧ w.k.wg = some
      (withPeer
        (withPeer (withPeer d pid { p with presharedKey := psk }) pid
          { p with presharedKey := psk, persistentKeepaliveInterval := interval }) pid
        { p with
          presharedKey := psk, persistentKeepaliveInterval := interval,
          refcount := p.refcount - 1 })⌝⦄ := by
  let p1 := { p with presharedKey := psk }
  let d1 := withPeer d pid p1
  have ht := scalarTail_down_returns key psk interval pid d1 p1
    (by simp [d1, withPeer]) (by simpa [d1, withPeer] using down)
    (by simpa [p1] using retained)
  simp [peerConfigUpdateSource, scalarAttrs, WGPEER_F_REMOVE_ME, WGPEER_F_REPLACE_ALLOWEDIPS]
  mvcgen [branch, getPeer, getDev, getK, setPeer, modifyDev, modifyK, invariant, ht]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [withPeer, d1, p1]
  all_goals first | exact ht _ (by simp_all [withPeer, d1, p1]) | grind only

theorem setPeer_scalars_down_returns (key psk : Key) (interval : Nat) (pid : PeerId)
    (d : Device) (p : Peer)
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount) (bounded : p.refcount + 1 < 2 ^ 31) (down : d.running = false) :
    Returns (setPeerCmd (scalarAttrs key psk interval)) (fun w => w.k.wg = some d)
      (fun ret w => ret = 0 ∧ w.k.wg = some (scalarDevice d pid p psk interval)) := by
  let p1 := { p with refcount := p.refcount + 1 }
  let d1 := withPeer d pid p1
  have hl := pubkeyLookup_present_returns key pid d p found resident live bounded
  have hu := scalarUpdate_down_returns key psk interval pid d1 p1
    (by simp [d1, withPeer]) (by simpa [d1, withPeer] using down)
    (by simpa [p1] using live)
  rw [← setPeerCmd_source, returns_iff]
  simp [setPeerCmdSource, scalarAttrs, WGPEER_F_ALL]
  mvcgen [Leanux.WG.andM, branch, invariant, hl, hu]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [scalarDevice, withPeer, p1, d1]
  all_goals first | exact hu _ (by simp_all [withPeer, d1, p1]) | grind only

end Leanux.Proofs.WG.Config
