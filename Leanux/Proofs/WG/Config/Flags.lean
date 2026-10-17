import Leanux.Proofs.WG.Config.Port
import Leanux.Proofs.WG.Config.PeerSource

set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem pubkeyLookup_absent (key : Key) (initial : WGWorld) (d : Device)
    (device : initial.dev = some d)
    (missing : d.peerHashtable.find? (·.1 == key) = none) :
    ⦃fun w => ⌜w = initial⌝⦄ pubkeyLookup key
    ⦃⇓? ret w => ⌜ret = none ∧ w = initial⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro g ambient result final after pre run
  subst g
  simp [pubkeyLookup, peerGetMaybeZero, getDev, device, missing, branch, AmbientM.branch] at run
  rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
  exact ⟨rfl, rfl⟩

theorem setPeer_absent_remove_update (a : PeerAttrs) (key : Key) (flags : UInt32)
    (initial : WGWorld) (d : Device)
    (device : initial.dev = some d)
    (missing : d.peerHashtable.find? (·.1 == key) = none)
    (pubkey : a.publicKey = some key) (flagattr : a.flags = some flags)
    (valid : flags &&& ~~~WGPEER_F_ALL = 0)
    (protocol : a.protocolVersion = none ∨ a.protocolVersion = some 1)
    (noCreate : flags &&& (WGPEER_F_REMOVE_ME ||| WGPEER_F_UPDATE_ONLY) ≠ 0) :
    Ensures (setPeerCmd a) (fun w => w = initial)
      (fun ret w => ret = 0 ∧ w = initial) := by
  intro g ambient result final after pre run
  subst g
  rw [← setPeerCmd_source] at run
  cases psk : a.presharedKey
  all_goals rcases protocol with protocol | protocol
  all_goals simp [setPeerCmdSource, pubkey, flagattr, psk, WG.andM, branch,
    AmbientM.branch, peerPut, valid, protocol, pubkeyLookup, getDev,
    device, missing, peerGetMaybeZero, noCreate] at run
  all_goals rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
  all_goals exact ⟨rfl, rfl⟩

theorem setPeer_invalid_flags (a : PeerAttrs) (key : Key) (flags : UInt32)
    (pubkey : a.publicKey = some key) (flagattr : a.flags = some flags)
    (invalid : flags &&& ~~~WGPEER_F_ALL ≠ 0) (initial : WGWorld) :
    Ensures (setPeerCmd a) (fun w => w = initial)
      (fun ret w => ret = -EOPNOTSUPP ∧ w = initial) := by
  intro g ambient result final after pre run
  subst g
  rw [← setPeerCmd_source] at run
  cases psk : a.presharedKey
  all_goals simp [setPeerCmdSource, pubkey, flagattr, psk, WG.andM, branch,
    AmbientM.branch, peerPut, invalid] at run
  all_goals rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
  all_goals exact ⟨rfl, rfl⟩

theorem setPeer_invalid_protocol (a : PeerAttrs) (key : Key) (flags : UInt32)
    (version : Nat) (pubkey : a.publicKey = some key) (flagattr : a.flags = some flags)
    (valid : flags &&& ~~~WGPEER_F_ALL = 0)
    (protocol : a.protocolVersion = some version) (invalid : version ≠ 1)
    (initial : WGWorld) :
    Ensures (setPeerCmd a) (fun w => w = initial)
      (fun ret w => ret = -EPFNOSUPPORT ∧ w = initial) := by
  intro g ambient result final after pre run
  subst g
  rw [← setPeerCmd_source] at run
  cases psk : a.presharedKey
  all_goals simp [setPeerCmdSource, pubkey, flagattr, psk, WG.andM, branch,
    AmbientM.branch, peerPut, valid, protocol, invalid] at run
  all_goals rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
  all_goals exact ⟨rfl, rfl⟩

theorem setPeer_absent_self (a : PeerAttrs) (key : Key) (flags : UInt32)
    (initial : WGWorld) (d : Device)
    (device : initial.dev = some d)
    (missing : d.peerHashtable.find? (·.1 == key) = none)
    (pubkey : a.publicKey = some key) (flagattr : a.flags = some flags)
    (valid : flags &&& ~~~WGPEER_F_ALL = 0)
    (protocol : a.protocolVersion = none ∨ a.protocolVersion = some 1)
    (identity : d.staticIdentity.hasIdentity = true) (self : key = d.staticIdentity.staticPublic) :
    Ensures (setPeerCmd a) (fun w => w = initial)
      (fun ret w => ret = 0 ∧ w = initial) := by
  intro g ambient result final after pre run
  subst g
  subst key
  rw [← setPeerCmd_source] at run
  cases psk : a.presharedKey
  all_goals rcases protocol with protocol | protocol
  all_goals by_cases early : flags &&& (WGPEER_F_REMOVE_ME ||| WGPEER_F_UPDATE_ONLY) ≠ 0
  all_goals simp [setPeerCmdSource, pubkey, flagattr, psk, WG.andM, branch,
    AmbientM.branch, peerPut, valid, protocol, pubkeyLookup, getDev,
    device, missing, peerGetMaybeZero, early, identity] at run
  all_goals rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
  all_goals exact ⟨rfl, rfl⟩

/-- Removal precedes all acquired-peer attribute updates, including replacement. -/
theorem peerUpdate_remove_source (a : PeerAttrs) (peer : Option PeerId) (flags : UInt32)
    (psk : Option Key) (pid : PeerId) (remove : flags &&& WGPEER_F_REMOVE_ME ≠ 0) :
    peerConfigUpdateSource a peer flags psk pid = (do
      _ ← branch .peerRemoveMe true
      peerRemove peer
      peerPut peer
      _ ← branch .peerZeroPsk a.presharedKey.isSome
      pure 0) := by
  have hr : (flags &&& WGPEER_F_REMOVE_ME != 0) = true := by simpa using remove
  funext g ambient
  simp [peerConfigUpdateSource, hr, branch, AmbientM.branch]

end Leanux.Proofs.WG.Config
