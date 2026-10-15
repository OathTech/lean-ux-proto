import Leanux.Proofs.WG.Config.Port
import Leanux.Proofs.WG.Config.PeerSource

set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem pubkeyLookup_absent (key : Key) (initial : Kernel) (d : Device)
    (device : initial.wg = some d)
    (missing : d.peerHashtable.find? (·.1 == key) = none) :
    ⦃fun w => ⌜w.k = initial⌝⦄ pubkeyLookup key
    ⦃⇓? ret w => ⌜ret = none ∧ w.k = initial⌝⦄ := by
  mvcgen [pubkeyLookup, peerGetMaybeZero, getDev, getK, branch, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [-List.find?_eq_none]

theorem setPeer_absent_remove_update (a : PeerAttrs) (key : Key) (flags : UInt32)
    (initial : Kernel) (d : Device)
    (device : initial.wg = some d)
    (missing : d.peerHashtable.find? (·.1 == key) = none)
    (pubkey : a.publicKey = some key) (flagattr : a.flags = some flags)
    (valid : flags &&& ~~~WGPEER_F_ALL = 0)
    (protocol : a.protocolVersion = none ∨ a.protocolVersion = some 1)
    (noCreate : flags &&& (WGPEER_F_REMOVE_ME ||| WGPEER_F_UPDATE_ONLY) ≠ 0) :
    Ensures (setPeerCmd a) (fun w => w.k = initial)
      (fun ret w => ret = 0 ∧ w.k = initial) := by
  rw [← setPeerCmd_source, ensures_iff]
  have hl := pubkeyLookup_absent key initial d device missing
  simp only [setPeerCmdSource, pubkey, flagattr, Option.isSome_some, Option.getD_some]
  mvcgen [Leanux.WG.andM, branch, getDev, getK, peerPut, invariant, hl]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all
  all_goals grind only

theorem setPeer_invalid_flags (a : PeerAttrs) (key : Key) (flags : UInt32)
    (pubkey : a.publicKey = some key) (flagattr : a.flags = some flags)
    (invalid : flags &&& ~~~WGPEER_F_ALL ≠ 0) (initial : Kernel) :
    Ensures (setPeerCmd a) (fun w => w.k = initial)
      (fun ret w => ret = -EOPNOTSUPP ∧ w.k = initial) := by
  rw [← setPeerCmd_source, ensures_iff]
  simp only [setPeerCmdSource, pubkey, flagattr, Option.isSome_some, Option.getD_some]
  mvcgen [Leanux.WG.andM, branch, peerPut, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all

theorem setPeer_invalid_protocol (a : PeerAttrs) (key : Key) (flags : UInt32)
    (version : Nat) (pubkey : a.publicKey = some key) (flagattr : a.flags = some flags)
    (valid : flags &&& ~~~WGPEER_F_ALL = 0)
    (protocol : a.protocolVersion = some version) (invalid : version ≠ 1)
    (initial : Kernel) :
    Ensures (setPeerCmd a) (fun w => w.k = initial)
      (fun ret w => ret = -EPFNOSUPPORT ∧ w.k = initial) := by
  rw [← setPeerCmd_source, ensures_iff]
  simp only [setPeerCmdSource, pubkey, flagattr, protocol, Option.isSome_some, Option.getD_some]
  mvcgen [Leanux.WG.andM, branch, peerPut, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all

theorem setPeer_absent_self (a : PeerAttrs) (key : Key) (flags : UInt32)
    (initial : Kernel) (d : Device)
    (device : initial.wg = some d)
    (missing : d.peerHashtable.find? (·.1 == key) = none)
    (pubkey : a.publicKey = some key) (flagattr : a.flags = some flags)
    (valid : flags &&& ~~~WGPEER_F_ALL = 0)
    (protocol : a.protocolVersion = none ∨ a.protocolVersion = some 1)
    (identity : d.staticIdentity.hasIdentity = true) (self : key = d.staticIdentity.staticPublic) :
    Ensures (setPeerCmd a) (fun w => w.k = initial)
      (fun ret w => ret = 0 ∧ w.k = initial) := by
  rw [← setPeerCmd_source, ensures_iff]
  have hl := pubkeyLookup_absent key initial d device missing
  simp only [setPeerCmdSource, pubkey, flagattr, Option.isSome_some, Option.getD_some]
  mvcgen [Leanux.WG.andM, branch, getDev, getK, peerPut, invariant, hl]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all
  all_goals grind only

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
  simp [peerConfigUpdateSource, hr, branch, bind_assoc]

end Leanux.Proofs.WG.Config
