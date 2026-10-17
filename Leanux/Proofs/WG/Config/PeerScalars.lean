import Leanux.Proofs.WG.Config.Flags
import Leanux.Proofs.WG.Noise.Slots

set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

def withPeer (d : Device) (pid : PeerId) (p : Peer) : Device :=
  { d with peers := d.peers.insert pid p }

theorem pubkeyLookup_present (key : Key) (pid : PeerId) (d : Device) (p : Peer)
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount) :
    ⦃fun w => ⌜w.dev = some d⌝⦄ pubkeyLookup key
    ⦃⇓? ret w => ⌜ret = some pid ∧ w.dev = some
      (withPeer d pid { p with refcount := p.refcount + 1 })⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro g ambient result final after device run
  have nonzero : p.refcount ≠ 0 := by omega
  by_cases overflow : 2147483647 ≤ p.refcount
  · simp [pubkeyLookup, peerGetMaybeZero, requireNotPending, refcountIncNotZero,
      branch, branchCmp, AmbientM.branch, AmbientM.branchCmp, getPeer, getDev,
      device, found, resident, nonzero, overflow, unsupported, AmbientM.unsupported] at run
    cases run
  · simp [pubkeyLookup, peerGetMaybeZero, requireNotPending, refcountIncNotZero,
      branch, branchCmp, AmbientM.branch, AmbientM.branchCmp, getPeer, getDev,
      device, found, resident, nonzero, overflow, setPeer, modifyDev] at run
    rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
    exact ⟨rfl, rfl⟩

theorem peerPut_retained (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (retained : 1 < p.refcount) :
    ⦃fun w => ⌜w.dev = some d⌝⦄ peerPut (some pid)
    ⦃⇓? _ w => ⌜w.dev = some (withPeer d pid { p with refcount := p.refcount - 1 })⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro g ambient result final after device run
  have positive : 0 < p.refcount := by omega
  have nonzero : p.refcount ≠ 0 := by omega
  have notLast : p.refcount ≠ 1 := by omega
  simp [peerPut, requireNotPending, refcountDecAndTest, branch, branchCmp,
    AmbientM.branch, AmbientM.branchCmp, getPeer, getDev, device, resident,
    setPeer, modifyDev, positive, nonzero, notLast] at run
  rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
  rfl

def scalarAttrs (key psk : Key) (interval : Nat) : PeerAttrs :=
  { publicKey := some key, presharedKey := some psk, keepalive := some interval }

theorem scalarTail_down (key psk : Key) (interval : Nat) (pid : PeerId)
    (d : Device) (p : Peer) (resident : d.peers[pid]? = some p)
    (down : d.running = false) (retained : 1 < p.refcount) :
    ⦃fun w => ⌜w.dev = some d⌝⦄ peerConfigTailSource (scalarAttrs key psk interval) (some pid) pid
    ⦃⇓? ret w => ⌜ret = 0 ∧ w.dev = some (withPeer (withPeer d pid { p with persistentKeepaliveInterval := interval }) pid
      { p with persistentKeepaliveInterval := interval, refcount := p.refcount - 1 })⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro g ambient result final after device run
  have positive : 0 < p.refcount := by omega
  have nonzero : p.refcount ≠ 0 := by omega
  have notLast : p.refcount ≠ 1 := by omega
  all_goals by_cases wasZero : p.persistentKeepaliveInterval = 0
  all_goals by_cases intervalZero : interval = 0
  all_goals simp [scalarAttrs, peerConfigTailSource, WG.andM, branch, branchCmp,
    AmbientM.branch, AmbientM.branchCmp, peerPut, requireNotPending, refcountDecAndTest,
    getPeer, getDev, device, resident, setPeer, modifyDev, down, nonzero, wasZero, intervalZero, positive, notLast] at run
  all_goals try (solve | cases run)
  all_goals rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
  all_goals simp [withPeer, down, intervalZero]

theorem scalarUpdate_down (key psk : Key) (interval : Nat) (pid : PeerId)
    (d : Device) (p : Peer) (resident : d.peers[pid]? = some p)
    (down : d.running = false) (retained : 1 < p.refcount) :
    ⦃fun w => ⌜w.dev = some d⌝⦄
      peerConfigUpdateSource (scalarAttrs key psk interval) (some pid) 0 (some psk) pid
    ⦃⇓? ret w => ⌜ret = 0 ∧ w.dev = some
      (withPeer
        (withPeer (withPeer d pid { p with presharedKey := psk }) pid
          { p with presharedKey := psk, persistentKeepaliveInterval := interval }) pid
        { p with
          presharedKey := psk, persistentKeepaliveInterval := interval,
          refcount := p.refcount - 1 })⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro g ambient result final after device run
  have positive : 0 < p.refcount := by omega
  have nonzero : p.refcount ≠ 0 := by omega
  have notLast : p.refcount ≠ 1 := by omega
  all_goals by_cases wasZero : p.persistentKeepaliveInterval = 0
  all_goals by_cases intervalZero : interval = 0
  all_goals simp [scalarAttrs, peerConfigTailSource, WG.andM, branch, branchCmp,
    AmbientM.branch, AmbientM.branchCmp, peerPut, requireNotPending, refcountDecAndTest,
    getPeer, getDev, device, resident, setPeer, modifyDev, down, nonzero, wasZero, intervalZero, peerConfigUpdateSource, positive, notLast, WGPEER_F_REMOVE_ME, WGPEER_F_REPLACE_ALLOWEDIPS] at run
  all_goals try (solve | cases run)
  all_goals rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
  all_goals simp [withPeer, down, intervalZero, wasZero]

/-- Concrete map updates in the order performed by lookup, set and put. -/
def scalarDevice (d : Device) (pid : PeerId) (p : Peer) (psk : Key) (interval : Nat) : Device :=
  let acquired := { p with refcount := p.refcount + 1 }
  let keyed := { acquired with presharedKey := psk }
  let configured := { keyed with persistentKeepaliveInterval := interval }
  withPeer (withPeer (withPeer (withPeer d pid acquired) pid keyed) pid configured) pid
    { configured with refcount := configured.refcount - 1 }

theorem setPeer_scalars_down (key psk : Key) (interval : Nat) (pid : PeerId)
    (d : Device) (p : Peer)
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount) (down : d.running = false) :
    Ensures (setPeerCmd (scalarAttrs key psk interval)) (fun w => w.dev = some d)
      (fun ret w => ret = 0 ∧ w.dev = some (scalarDevice d pid p psk interval)) := by
  intro g ambient result final after device run
  rw [← setPeerCmd_source] at run
  have nonzero : p.refcount ≠ 0 := by omega
  by_cases overflow : 2147483647 ≤ p.refcount
  all_goals by_cases wasZero : p.persistentKeepaliveInterval = 0
  all_goals by_cases intervalZero : interval = 0
  all_goals simp [scalarAttrs, peerConfigTailSource, WG.andM, branch, branchCmp,
    AmbientM.branch, AmbientM.branchCmp, peerPut, requireNotPending, refcountDecAndTest,
    getPeer, getDev, device, resident, setPeer, modifyDev, down, nonzero, wasZero, intervalZero, setPeerCmdSource, peerConfigUpdateSource, pubkeyLookup, peerGetMaybeZero,
    refcountIncNotZero, found, overflow, WGPEER_F_ALL, WGPEER_F_REMOVE_ME,
    WGPEER_F_REPLACE_ALLOWEDIPS, unsupported, AmbientM.unsupported] at run
  all_goals try (solve | cases run)
  all_goals rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
  all_goals simp [scalarDevice, withPeer, down, intervalZero, wasZero]

theorem scalarDevice_peer (d : Device) (pid : PeerId) (p : Peer) (psk : Key) (interval : Nat) :
    (scalarDevice d pid p psk interval).peers[pid]? = some
      { p with presharedKey := psk, persistentKeepaliveInterval := interval } := by
  simp [scalarDevice, withPeer]

end Leanux.Proofs.WG.Config
