import Leanux.Proofs.WG.Config.MixedPeerModel
import Leanux.Proofs.WG.Config.AllowedInsertSource

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Std.Do Lean

/-- Normal completion preserves each earlier attribute when insertion refuses
or a later Allowed-IP entry is malformed. Hidden-input Stops stay outside this
normal-return contract; no readiness of allocation records is assumed. -/
theorem setPeer_mixed_allowedip (v4 : Bool) (key psk : Key) (interval addr cidr : Nat)
    (bad : Bool) (d : Device) (pid : PeerId) (p : Peer)
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount)
    (bounded : p.refcount + 1 < 2 ^ 31) (down : d.running = false)
    (root : allowedRootValue v4 d = none) (width : cidr ≤ allowedBits v4) :
    Ensures (setPeerCmd (mixedPeerAttrs v4 key psk interval addr cidr bad))
      (fun g => g.dev = some d)
      (fun ret g => ∃ final, g.dev = some final ∧
        MixedPeerEffect v4 d pid p psk interval addr cidr bad ret final) := by
  intro g ambient result final after device run
  have hok {α β : Type} (x : α) (f : α → Except Stop β) :
      ((Except.ok x : Except Stop α) >>= f) = f x := rfl
  have nonzero : p.refcount ≠ 0 := by omega
  have noOverflow : ¬ 2147483647 ≤ p.refcount := by omega
  rw [← setPeerCmd_source] at run
  simp [mixedPeerAttrs, setPeerCmdSource, peerConfigUpdateSource, peerConfigTailSource,
    WG.andM, branch, branchCmp, AmbientM.branch, AmbientM.branchCmp,
    pubkeyLookup, peerGetMaybeZero, requireNotPending, refcountIncNotZero,
    getPeer, getDev, device, found, resident, nonzero, noOverflow,
    setPeer, modifyDev, WGPEER_F_ALL, WGPEER_F_REMOVE_ME, WGPEER_F_REPLACE_ALLOWEDIPS,
    List.forIn_cons] at run
  generalize hA : ((setAllowedip pid (allowedAttrs v4 addr cidr)).run _).run _ = out at run
  cases out with
  | error stop => cases run
  | ok out =>
    obtain ⟨⟨ret, middle⟩, next⟩ := out
    have effect := setAllowedip_empty_root_effect v4 (mixedPeerBase d pid p psk) pid
      (mixedPeerKeyed p psk) addr cidr
      (by simp [mixedPeerBase, withPeer]) root width _ _ ret middle next rfl hA
    clear hA
    obtain ⟨current, hd, he⟩ := effect
    rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp [hok, peerPut, requireNotPending, refcountDecAndTest, getPeer, getDev, hd,
        setPeer, modifyDev, branch, branchCmp, AmbientM.branch, AmbientM.branchCmp,
        mixedPeerBase, mixedPeerKeyed, withPeer, insertSequenceDevice, ENOMEM,
        nonzero] at run
      rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
      refine ⟨_, rfl, Or.inl ⟨rfl, ?_⟩⟩
      simp [mixedPeerExit, mixedPeerBase, mixedPeerKeyed, withPeer, insertSequenceDevice]
    · cases bad <;> by_cases wasZero : p.persistentKeepaliveInterval = 0 <;>
        by_cases intervalZero : interval = 0
      all_goals simp [hok, peerPut, requireNotPending, refcountDecAndTest, getPeer, getDev, hd,
        setPeer, modifyDev, branch, branchCmp, AmbientM.branch, AmbientM.branchCmp,
        mixedPeerBase, mixedPeerKeyed, withPeer, insertSequenceDevice, emptyRootInserted,
        List.forIn_cons, List.forIn_nil, down, nonzero, wasZero, intervalZero] at run
      all_goals rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
      all_goals refine ⟨_, rfl, Or.inr ⟨rfl, ?_⟩⟩
      all_goals simp [mixedPeerExit, mixedPeerBase, mixedPeerKeyed, withPeer,
        insertSequenceDevice, emptyRootInserted, wasZero, intervalZero, down]

end Leanux.Proofs.WG.Config
