import Leanux.Proofs.WG.Noise.Basic

set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG Std.Do

abbrev unhashEntry := noise_const _private.Leanux.WG.Peer.«0».Leanux.WG.unhashEntry
abbrev modifyPeer := noise_const _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer

theorem modifyDev_peers_spec (P : (PeerId → Option Peer) → Prop)
    (f : Device → Device) (hf : ∀ d, (f d).peers = d.peers) :
    ⦃fun w => ⌜P (peerAt w)⌝⦄ modifyDev f
    ⦃⇓? _ w => ⌜P (peerAt w)⌝⦄ := by
  mvcgen [modifyDev, modifyK]
  all_goals try dsimp +zetaDelta only at *
  all_goals rename_i w h t
  have he : peerAt { w with k := { w.k with wg := w.k.wg.map f } } = peerAt w := by
    funext pid
    simp [peerAt, Option.bind_map, Function.comp_def, hf]
  exact he ▸ h

theorem keypairPut_peers_spec (P : (PeerId → Option Peer) → Prop)
    (kp : Option KeypairId) (now : Bool) :
    ⦃fun w => ⌜P (peerAt w)⌝⦄ keypairPut kp now
    ⦃⇓? _ w => ⌜P (peerAt w)⌝⦄ := by
  have hm := modifyDev_peers_spec P
  noise_vcgen [keypairPut, indexRemoveKeypair, _private.Leanux.WG.Peer.«0».Leanux.WG.unhashEntry, getKeypair, getDev,
    getK, setKeypair, refcountDecAndTest, branch, branchCmp, branchCmpExcluded,
    invariant, unsupported, hm]
  all_goals try dsimp +zetaDelta only at *
  all_goals dsimp [peerAt] at *
  all_goals simp_all

theorem addNewKeypair_slots (pid : PeerId) (newKey : KeypairId)
    (p : Peer) (k : Keypair) :
    Ensures (addNewKeypair pid newKey)
      (fun w => peerAt w pid = some p ∧
        (w.k.wg.bind fun d => d.keypairs[newKey]?) = some k)
      (fun _ w => ∃ p', peerAt w pid = some p' ∧
        slots p' = rotate (slots p) k.iAmTheInitiator newKey) := by
  rw [ensures_iff]
  have hp := fun (initial : Option Peer) => keypairPut_peers_spec (fun v => v pid = initial)
  noise_vcgen [addNewKeypair, _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer, getPeer, getKeypair, getDev, getK,
    setPeer, modifyDev, modifyK, branch, invariant, hp]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [peerAt, slots, rotate, Option.bind_map, Function.comp_def, Std.TreeMap.getElem?_insert]
  all_goals grind

theorem receivedWithKeypair_slots (pid : PeerId) (received : KeypairId) (p : Peer) :
    Ensures (receivedWithKeypair pid received)
      (fun w => peerAt w pid = some p)
      (fun ok w => ∃ p', peerAt w pid = some p' ∧
        (ok, slots p') = confirm (slots p) received) := by
  rw [ensures_iff]
  have hp := fun (initial : Option Peer) => keypairPut_peers_spec (fun v => v pid = initial)
  noise_vcgen [receivedWithKeypair, _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer,
    getPeer, getDev, getK, setPeer, modifyDev, modifyK, branch, invariant, hp]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [peerAt, slots, confirm, Option.bind_map, Function.comp_def,
    Std.TreeMap.getElem?_insert]
  all_goals grind

theorem getPeer_exact_spec (pid : PeerId) (p : Peer) :
    ⦃fun w => ⌜peerAt w pid = some p⌝⦄ getPeer pid
    ⦃⇓? r w => ⌜r = p ∧ peerAt w pid = some p⌝⦄ := by
  mvcgen [getPeer, getDev, getK, invariant]
  all_goals simp_all [peerAt]

theorem modifyPeer_exact_spec (pid : PeerId) (f : Peer → Peer) (p : Peer) :
    ⦃fun w => ⌜peerAt w pid = some p⌝⦄ modifyPeer pid f
    ⦃⇓? _ w => ⌜peerAt w pid = some (f p)⌝⦄ := by
  noise_vcgen [_private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer,
    getPeer, getDev, getK, setPeer, modifyDev, modifyK, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [peerAt, Option.bind_map, Function.comp_def,
    Std.TreeMap.getElem?_insert]

def clearOne (pid : PeerId) (pick : Peer → Option KeypairId) (clear : Peer → Peer) : M Unit := do
  let old := pick (← getPeer pid)
  modifyPeer pid clear
  keypairPut old true

theorem clearOne_peer (pid : PeerId) (pick : Peer → Option KeypairId)
    (clear : Peer → Peer) (p : Peer) :
    Ensures (clearOne pid pick clear) (fun w => peerAt w pid = some p)
      (fun _ w => peerAt w pid = some (clear p)) := by
  rw [ensures_iff]
  have hp := fun (initial : Option Peer) => keypairPut_peers_spec (fun v => v pid = initial)
  noise_vcgen [clearOne, _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer,
    getPeer, getDev, getK, setPeer, modifyDev, modifyK, invariant, hp]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [peerAt, Option.bind_map, Function.comp_def, Std.TreeMap.getElem?_insert]
  all_goals grind

theorem keypairsClear_source (pid : PeerId) :
    keypairsClear pid = (do
      clearOne pid Peer.keypairNext (fun p => { p with keypairNext := none })
      clearOne pid Peer.keypairPrevious (fun p => { p with keypairPrevious := none })
      clearOne pid Peer.keypairCurrent (fun p => { p with keypairCurrent := none })) := by
  simp only [keypairsClear, clearOne, bind_assoc]

theorem keypairsClear_peer (pid : PeerId) (p : Peer) :
    Ensures (keypairsClear pid) (fun w => peerAt w pid = some p)
      (fun _ w => peerAt w pid = some { p with
        keypairNext := none, keypairPrevious := none, keypairCurrent := none }) := by
  rw [keypairsClear_source]
  exact ensures_bind _ _ (clearOne_peer pid _ _ p) fun _ =>
    ensures_bind _ _ (clearOne_peer pid _ _ { p with keypairNext := none }) fun _ =>
      clearOne_peer pid _ _ { p with keypairNext := none, keypairPrevious := none }

theorem keypairsClear_slots (pid : PeerId) (p : Peer) :
    Ensures (keypairsClear pid) (fun w => peerAt w pid = some p)
      (fun _ w => ∃ p', peerAt w pid = some p' ∧ slots p' = ⟨none, none, none⟩) := by
  intro w x w' hp hr
  exact ⟨_, keypairsClear_peer pid p w x w' hp hr, rfl⟩

theorem handshakeZero_peer (pid : PeerId) (p : Peer) :
    Ensures (handshakeZero pid)
      (fun w => peerAt w pid = some p)
      (fun _ w => peerAt w pid = some { p with
        ephemeralPrivate := List.replicate 32 0,
        remoteEphemeral := List.replicate 32 0,
        hash := List.replicate 32 0,
        chainingKey := List.replicate 32 0,
        remoteIndex := 0, handshakeState := 0 }) := by
  rw [ensures_iff]
  noise_vcgen [handshakeZero, getPeer, getDev, getK, setPeer, modifyDev, modifyK, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [peerAt, Option.bind_map, Function.comp_def,
    Std.TreeMap.getElem?_insert]

end Leanux.Proofs.WG.Noise
