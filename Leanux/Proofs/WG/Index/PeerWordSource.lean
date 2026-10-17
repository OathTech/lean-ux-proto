import Leanux.Proofs.WG.Index.LookupSource
import Leanux.Proofs.WG.Index.OwnerWordModel

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config Std.Do

theorem peerWord_returns (owner : IndexOwner) (d : Device) (word : Option PeerId)
    (resident : ownerWord d owner = some word) :
    Returns owner.peerWord (fun g => g.dev = some d)
      (fun result g => result = word ∧ g.dev = some d) := by
  intro g ambient device
  refine ⟨word, g, ambient, ?_, rfl, device⟩
  cases owner with
  | handshake pid =>
    cases h : d.peers[pid]? with
    | none => simp [ownerWord, h] at resident
    | some p =>
      have hp : p.handshakeEntryPeer = word := by simpa [ownerWord, h] using resident
      simp [IndexOwner.peerWord, getPeer, getDev, device, h, hp]
      rfl
  | keypair kp =>
    cases h : d.keypairs[kp]? with
    | none => simp [ownerWord, h] at resident
    | some p =>
      have hp : p.peer = word := by simpa [ownerWord, h] using resident
      simp [IndexOwner.peerWord, getKeypair, getDev, device, h, hp]
      rfl

theorem setPeerWord_returns (owner : IndexOwner) (d : Device) (old word : Option PeerId)
    (resident : ownerWord d owner = some old) :
    Returns (owner.setPeerWord word) (fun g => g.dev = some d)
      (fun _ g => g.dev = some (writeOwnerWord d owner word)) := by
  intro g ambient device
  refine ⟨(), {g with dev := some (writeOwnerWord d owner word)}, ambient, ?_, rfl⟩
  cases owner with
  | handshake pid =>
    cases h : d.peers[pid]? with
    | none => simp [ownerWord, h] at resident
    | some p =>
      simp [IndexOwner.setPeerWord, getPeer, getDev, device, h, setPeer, modifyDev, writeOwnerWord]
      rfl
  | keypair kp =>
    cases h : d.keypairs[kp]? with
    | none => simp [ownerWord, h] at resident
    | some p =>
      simp [IndexOwner.setPeerWord, getKeypair, getDev, device, h, setKeypair, modifyDev, writeOwnerWord]
      rfl

/-- The outer option distinguishes an absent owner object from its NULL word. -/
theorem lookupFinish_null (index : Nat) (owner : IndexOwner) (d : Device)
    (word : ownerWord d owner = some none) :
    Returns (lookupFinish (some { index, owner }, true)) (fun g => g.dev = some d)
      (fun result g => result = none ∧ g.dev = some (writeOwnerWord d owner none)) := by
  intro g ambient device
  let after := recordStep (recordStep (recordStep ambient .idxFound true)
    .peerGetMaybeZeroNull true) .idxPeerAlive false
  refine ⟨none, {g with dev := some (writeOwnerWord d owner none)}, after, ?_, rfl, rfl⟩
  cases owner with
  | handshake pid =>
    cases h : d.peers[pid]? with
    | none => simp [ownerWord, h] at word
    | some p =>
      have hp : p.handshakeEntryPeer = none := by simpa [ownerWord, h] using word
      simp [lookupFinish, IndexOwner.peerWord, IndexOwner.setPeerWord, peerGetMaybeZero,
        getPeer, getDev, device, h, hp, setPeer, modifyDev, writeOwnerWord,
        branch, AmbientM.branch, after, recordStep]
      rfl
  | keypair kp =>
    cases h : d.keypairs[kp]? with
    | none => simp [ownerWord, h] at word
    | some p =>
      have hp : p.peer = none := by simpa [ownerWord, h] using word
      simp [lookupFinish, IndexOwner.peerWord, IndexOwner.setPeerWord, peerGetMaybeZero,
        getKeypair, getDev, device, h, hp, setKeypair, modifyDev, writeOwnerWord,
        branch, AmbientM.branch, after, recordStep]
      rfl

theorem lookupFinish_dead (index : Nat) (owner : IndexOwner) (d : Device)
    (pid : PeerId) (p : Peer) (word : ownerWord d owner = some (some pid))
    (resident : d.peers[pid]? = some p) (dead : p.refcount = 0) :
    Returns (lookupFinish (some { index, owner }, true)) (fun g => g.dev = some d)
      (fun result g => result = none ∧ g.dev = some (writeOwnerWord d owner none)) := by
  intro g ambient device
  let start := recordStep (recordStep ambient .idxFound true) .peerGetMaybeZeroNull false
  let zero := {start with steps := start.steps.push {
    decision := .refcountAddNzZero, outcome := true, operands := some (0, 0),
    netRx := start.netRxSection}}
  let after := recordStep (recordStep (recordStep (recordStep zero
    .refcountAddNzNegative false) .refcountAddNzWraps false)
    .peerGetMaybeZeroDead true) .idxPeerAlive false
  refine ⟨none, {g with dev := some (writeOwnerWord d owner none)}, after, ?_, rfl, rfl⟩
  cases owner with
  | handshake own =>
    cases h : d.peers[own]? with
    | none => simp [ownerWord, h] at word
    | some q =>
      have hp : q.handshakeEntryPeer = some pid := by simpa [ownerWord, h] using word
      simp [lookupFinish, IndexOwner.peerWord, IndexOwner.setPeerWord, peerGetMaybeZero,
        requireNotPending, refcountIncNotZero, getPeer, getDev, device, h, hp, resident, dead,
        setPeer, modifyDev, writeOwnerWord, branch, branchCmp, AmbientM.branch, AmbientM.branchCmp,
        start, zero, after, recordStep]
      rfl
  | keypair kp =>
    cases h : d.keypairs[kp]? with
    | none => simp [ownerWord, h] at word
    | some q =>
      have hp : q.peer = some pid := by simpa [ownerWord, h] using word
      simp [lookupFinish, IndexOwner.peerWord, IndexOwner.setPeerWord, peerGetMaybeZero,
        requireNotPending, refcountIncNotZero, getPeer, getKeypair, getDev, device, h, hp, resident, dead,
        setPeer, setKeypair, modifyDev, writeOwnerWord, branch, branchCmp, AmbientM.branch, AmbientM.branchCmp,
        start, zero, after, recordStep]
      rfl

theorem peerGet_live_returns (d : Device) (pid : PeerId) (p : Peer)
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount)
    (bounded : p.refcount + 1 < 2 ^ 31) :
    Returns (peerGetMaybeZero (some pid)) (fun g => g.dev = some d)
      (fun result g => result = some pid ∧ g.dev = some (acquirePeer d pid p)) := by
  intro g ambient device
  let start := recordStep ambient .peerGetMaybeZeroNull false
  let zero := {start with steps := start.steps.push {
    decision := .refcountAddNzZero, outcome := false, operands := some (p.refcount, 0),
    netRx := start.netRxSection}}
  let after := recordStep (recordStep (recordStep (recordStep zero
    .refcountAddNzRetry false) .refcountAddNzNegative false)
    .refcountAddNzWraps false) .peerGetMaybeZeroDead false
  refine ⟨some pid, {g with dev := some (acquirePeer d pid p)}, after, ?_, rfl, rfl⟩
  have nonzero : p.refcount ≠ 0 := by omega
  have isNonzero : (p.refcount == 0) = false := by simp [nonzero]
  have isLive : (p.refcount != 0) = true := by simp [nonzero]
  have nowrap : ¬2147483647 ≤ p.refcount := by omega
  simp [peerGetMaybeZero, requireNotPending, refcountIncNotZero, getPeer, getDev,
    device, resident, nonzero, isNonzero, isLive, nowrap, setPeer, modifyDev, acquirePeer, branch, branchCmp,
    AmbientM.branch, AmbientM.branchCmp, start, zero, after, recordStep]
  rfl

end Leanux.Proofs.WG.Index
