import Leanux.Proofs.WG.Config.Getter
import Leanux.Proofs.WG.Config.ReadbackFrames

set_option pp.structureInstances false
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Lean Std.Do

theorem pubkeyLookup_present_returns_framed (sock : NlSock) (fixtures : FixtureDevices) (key : Key) (pid : PeerId) (d : Device) (p : Peer)
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount) (bounded : p.refcount + 1 < 2 ^ 31) :
    ⦃fun w => ⌜w.dev = some d ∧ readbackFrame w sock fixtures⌝⦄ pubkeyLookup key
    ⦃⇓ ret w => ⌜ret = some pid ∧ w.dev = some
      (withPeer d pid { p with refcount := p.refcount + 1 }) ∧ readbackFrame w sock fixtures⌝⦄ := by
  apply (returns_iff _ _ _).mp
  intro g ambient pre
  obtain ⟨device, framed⟩ := pre
  have nonzero : p.refcount ≠ 0 := by omega
  have noOverflow : ¬ 2147483647 ≤ p.refcount := by omega
  have complete : ∃ x final after, ((pubkeyLookup key).run g).run ambient = .ok ((x, final), after) ∧ readbackFrame final sock fixtures := by
    simp [readbackFrame, framed.1, framed.2, pubkeyLookup, peerGetMaybeZero, requireNotPending, refcountIncNotZero, branch, branchCmp,
      AmbientM.branch, AmbientM.branchCmp, getPeer, getDev, device, found, resident, nonzero, noOverflow,
      setPeer, modifyDev]
    all_goals exact ⟨_, _, ⟨_, rfl⟩, rfl, rfl⟩
  obtain ⟨x, final, after, run, frame⟩ := complete
  have effect := ((ensures_iff _ _ _).mpr (pubkeyLookup_present key pid d p found resident live)) g ambient x final after device run
  exact ⟨x, final, after, run, effect.1, effect.2, frame⟩

theorem peerPut_retained_returns_framed (sock : NlSock) (fixtures : FixtureDevices) (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (retained : 1 < p.refcount) :
    ⦃fun w => ⌜w.dev = some d ∧ readbackFrame w sock fixtures⌝⦄ peerPut (some pid)
    ⦃⇓ _ w => ⌜w.dev = some (withPeer d pid { p with refcount := p.refcount - 1 }) ∧ readbackFrame w sock fixtures⌝⦄ := by
  apply (returns_iff _ _ _).mp
  intro g ambient pre
  obtain ⟨device, framed⟩ := pre
  have positive : 0 < p.refcount := by omega
  have nonzero : p.refcount ≠ 0 := by omega
  have notLast : p.refcount ≠ 1 := by omega
  have complete : ∃ x final after, ((peerPut (some pid)).run g).run ambient = .ok ((x, final), after) ∧ readbackFrame final sock fixtures := by
    simp [readbackFrame, framed.1, framed.2, peerPut, requireNotPending, refcountDecAndTest, branch, branchCmp, AmbientM.branch,
      AmbientM.branchCmp, getPeer, getDev, device, resident, setPeer, modifyDev, positive, nonzero,
      notLast]
    all_goals exact ⟨_, _, ⟨_, rfl⟩, rfl, rfl⟩
  obtain ⟨x, final, after, run, frame⟩ := complete
  have effect := ((ensures_iff _ _ _).mpr (peerPut_retained pid d p resident retained)) g ambient x final after device run
  exact ⟨x, final, after, run, effect, frame⟩

theorem scalarTail_down_returns_framed (sock : NlSock) (fixtures : FixtureDevices) (key psk : Key) (interval : Nat) (pid : PeerId)
    (d : Device) (p : Peer) (resident : d.peers[pid]? = some p)
    (down : d.running = false) (retained : 1 < p.refcount) :
    ⦃fun w => ⌜w.dev = some d ∧ readbackFrame w sock fixtures⌝⦄ peerConfigTailSource (scalarAttrs key psk interval) (some pid) pid
    ⦃⇓ ret w => ⌜ret = 0 ∧ w.dev = some (withPeer (withPeer d pid { p with persistentKeepaliveInterval := interval }) pid
      { p with persistentKeepaliveInterval := interval, refcount := p.refcount - 1 }) ∧ readbackFrame w sock fixtures⌝⦄ := by
  apply (returns_iff _ _ _).mp
  intro g ambient pre
  obtain ⟨device, framed⟩ := pre
  have positive : 0 < p.refcount := by omega
  have nonzero : p.refcount ≠ 0 := by omega
  have notLast : p.refcount ≠ 1 := by omega
  have complete : ∃ x final after, ((peerConfigTailSource (scalarAttrs key psk interval) (some pid) pid).run g).run ambient = .ok ((x, final), after) ∧ readbackFrame final sock fixtures := by
    by_cases wasZero : p.persistentKeepaliveInterval = 0
    all_goals by_cases intervalZero : interval = 0
    all_goals simp [readbackFrame, framed.1, framed.2, scalarAttrs, peerConfigTailSource, WG.andM, branch, branchCmp, AmbientM.branch,
      AmbientM.branchCmp, peerPut, requireNotPending, refcountDecAndTest, getPeer, getDev, device,
      resident, setPeer, modifyDev, down, nonzero, positive, notLast, wasZero, intervalZero]
    all_goals exact ⟨_, _, ⟨_, rfl⟩, rfl, rfl⟩
  obtain ⟨x, final, after, run, frame⟩ := complete
  have effect := ((ensures_iff _ _ _).mpr (scalarTail_down key psk interval pid d p resident down retained)) g ambient x final after device run
  exact ⟨x, final, after, run, effect.1, effect.2, frame⟩

theorem scalarUpdate_down_returns_framed (sock : NlSock) (fixtures : FixtureDevices) (key psk : Key) (interval : Nat) (pid : PeerId)
    (d : Device) (p : Peer) (resident : d.peers[pid]? = some p)
    (down : d.running = false) (retained : 1 < p.refcount) :
    ⦃fun w => ⌜w.dev = some d ∧ readbackFrame w sock fixtures⌝⦄
      peerConfigUpdateSource (scalarAttrs key psk interval) (some pid) 0 (some psk) pid
    ⦃⇓ ret w => ⌜ret = 0 ∧ w.dev = some
      (withPeer
        (withPeer (withPeer d pid { p with presharedKey := psk }) pid
          { p with presharedKey := psk, persistentKeepaliveInterval := interval }) pid
        { p with
          presharedKey := psk, persistentKeepaliveInterval := interval,
          refcount := p.refcount - 1 }) ∧ readbackFrame w sock fixtures⌝⦄ := by
  apply (returns_iff _ _ _).mp
  intro g ambient pre
  obtain ⟨device, framed⟩ := pre
  have positive : 0 < p.refcount := by omega
  have nonzero : p.refcount ≠ 0 := by omega
  have notLast : p.refcount ≠ 1 := by omega
  have complete : ∃ x final after, ((peerConfigUpdateSource (scalarAttrs key psk interval) (some pid) 0 (some psk) pid).run g).run ambient = .ok ((x, final), after) ∧ readbackFrame final sock fixtures := by
    by_cases wasZero : p.persistentKeepaliveInterval = 0
    all_goals by_cases intervalZero : interval = 0
    all_goals simp [readbackFrame, framed.1, framed.2, scalarAttrs, peerConfigTailSource, WG.andM, branch, branchCmp, AmbientM.branch,
      AmbientM.branchCmp, peerPut, requireNotPending, refcountDecAndTest, getPeer, getDev, device,
      resident, setPeer, modifyDev, down, nonzero, positive, notLast, peerConfigUpdateSource,
      WGPEER_F_REMOVE_ME, WGPEER_F_REPLACE_ALLOWEDIPS, wasZero, intervalZero]
    all_goals exact ⟨_, _, ⟨_, rfl⟩, rfl, rfl⟩
  obtain ⟨x, final, after, run, frame⟩ := complete
  have effect := ((ensures_iff _ _ _).mpr (scalarUpdate_down key psk interval pid d p resident down retained)) g ambient x final after device run
  exact ⟨x, final, after, run, effect.1, effect.2, frame⟩

theorem setPeer_scalars_down_returns_framed (sock : NlSock) (fixtures : FixtureDevices) (key psk : Key) (interval : Nat) (pid : PeerId)
    (d : Device) (p : Peer)
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount) (bounded : p.refcount + 1 < 2 ^ 31) (down : d.running = false) :
    Returns (setPeerCmd (scalarAttrs key psk interval)) (fun w => w.dev = some d ∧ readbackFrame w sock fixtures)
      (fun ret w => ret = 0 ∧ w.dev = some (scalarDevice d pid p psk interval) ∧ readbackFrame w sock fixtures) := by
  intro g ambient pre
  obtain ⟨device, framed⟩ := pre
  have nonzero : p.refcount ≠ 0 := by omega
  have noOverflow : ¬ 2147483647 ≤ p.refcount := by omega
  have complete : ∃ x final after, ((setPeerCmd (scalarAttrs key psk interval)).run g).run ambient = .ok ((x, final), after) ∧ readbackFrame final sock fixtures := by
    rw [← setPeerCmd_source]
    by_cases wasZero : p.persistentKeepaliveInterval = 0
    all_goals by_cases intervalZero : interval = 0
    all_goals simp [readbackFrame, framed.1, framed.2, scalarAttrs, peerConfigTailSource, WG.andM, branch, branchCmp, AmbientM.branch,
      AmbientM.branchCmp, peerPut, requireNotPending, refcountDecAndTest, getPeer, getDev, device,
      resident, setPeer, modifyDev, down, nonzero, setPeerCmdSource, peerConfigUpdateSource,
      pubkeyLookup, peerGetMaybeZero, refcountIncNotZero, found, noOverflow, WGPEER_F_ALL,
      WGPEER_F_REMOVE_ME, WGPEER_F_REPLACE_ALLOWEDIPS, wasZero, intervalZero]
    all_goals exact ⟨_, _, ⟨_, rfl⟩, rfl, rfl⟩
  obtain ⟨x, final, after, run, frame⟩ := complete
  have effect := (setPeer_scalars_down key psk interval pid d p found resident live down) g ambient x final after device run
  exact ⟨x, final, after, run, effect.1, effect.2, frame⟩

end Leanux.Proofs.WG.Config
