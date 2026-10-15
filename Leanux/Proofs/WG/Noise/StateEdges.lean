import Leanux.Proofs.WG.Noise.PeerFrames

set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG Std.Do

def tagAt (k : Kernel) (pid : PeerId) : Option Nat :=
  (k.wg.bind fun d => d.peers[pid]?).map Peer.handshakeState

theorem createInitiation_tag (pid : PeerId) (old : Nat) :
    Ensures (createInitiation pid)
      (fun w => tagAt w.k pid = some old)
      (fun result w => tagAt w.k pid = some
        (if result.isSome then HANDSHAKE_CREATED_INITIATION else old)) := by
  rw [ensures_iff]
  let P := fun k : Kernel => tagAt k pid = some old
  have hh := hidden_kernel_spec P
  have hg := generatePublic_kernel_spec P
  have he := messageEphemeral_kernel_spec P
  have hd := mixDh_kernel_spec P
  have hs := mixPrecomputedDh_kernel_spec P
  have hi := indexInsert_peers_spec (fun ps => (ps pid).map Peer.handshakeState = some old)
  noise_vcgen [createInitiation, _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain,
    IndexOwner.peerDeref, IndexOwner.peerWord, unsupported, getPeer, getDev, getK, setPeer, modifyDev, modifyK, branch, invariant,
    hh, hg, he, hd, hs, hi]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [P, tagAt, peerAt, Option.bind_map, Function.comp_def,
    Std.TreeMap.getElem?_insert]
  all_goals grind

theorem createResponse_tag (pid : PeerId) (old : Nat) :
    Ensures (createResponse pid)
      (fun w => tagAt w.k pid = some old)
      (fun result w => tagAt w.k pid = some
        (if result.isSome then HANDSHAKE_CREATED_RESPONSE else old) ∧
        (result.isSome → old = HANDSHAKE_CONSUMED_INITIATION)) := by
  rw [ensures_iff]
  let P := fun k : Kernel => tagAt k pid = some old
  have hh := hidden_kernel_spec P
  have hg := generatePublic_kernel_spec P
  have he := messageEphemeral_kernel_spec P
  have hd := mixDh_kernel_spec P
  have hk := kdf_kernel_spec P
  have ho := kdfOut_kernel_spec P
  have hi := indexInsert_peers_spec (fun ps => (ps pid).map Peer.handshakeState = some old)
  noise_vcgen [createResponse, _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain,
    IndexOwner.peerDeref, IndexOwner.peerWord, unsupported, getPeer, getDev, getK, setPeer, modifyDev, modifyK, branch, invariant,
    hh, hg, he, hd, hk, ho, hi]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [P, tagAt, peerAt, Option.bind_map, Function.comp_def,
    Std.TreeMap.getElem?_insert]
  all_goals grind

theorem expireCurrentPeerKeypairs_slots (pid : PeerId) (p : Peer) :
    Ensures (expireCurrentPeerKeypairs pid)
      (fun w => peerAt w pid = some p)
      (fun _ w => ∃ p', peerAt w pid = some p' ∧
        slots p' = slots p ∧ p'.handshakeState = 0) := by
  rw [ensures_iff]
  let P := fun k : Kernel => ∃ p',
    (k.wg.bind fun d => d.peers[pid]?) = some p' ∧
      slots p' = slots p ∧ p'.handshakeState = 0
  have hh := hiddenClock64_kernel_spec P
  have hi := indexRemove_peers_spec (fun ps => ps pid = some p)
  noise_vcgen [expireCurrentPeerKeypairs, requireNotPending, handshakeClear, IndexOwner.peerDeref, IndexOwner.peerWord, unsupported, handshakeZero,
    resetLastSentHandshake, getPeer, getKeypair, getDev, getK, setPeer,
    setKeypair, modifyDev, modifyK, branch, invariant, hh, hi]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [P, peerAt, slots, Option.bind_map, Function.comp_def,
    Std.TreeMap.getElem?_insert]
  all_goals grind

theorem addNewKeypair_tag_spec (pid : PeerId) (kp : KeypairId) (tag : Nat) :
    ⦃fun w => ⌜tagAt w.k pid = some tag⌝⦄ addNewKeypair pid kp
    ⦃⇓? _ w => ⌜tagAt w.k pid = some tag⌝⦄ := by
  have hp := keypairPut_peers_spec (fun ps => (ps pid).map Peer.handshakeState = some tag)
  noise_vcgen [addNewKeypair, _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer,
    getPeer, getKeypair, getDev, getK, setPeer, modifyDev, modifyK, branch, invariant, hp]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [tagAt, peerAt, Option.bind_map, Function.comp_def,
    Std.TreeMap.getElem?_insert]
  all_goals grind

theorem beginSession_tag (pid : PeerId) (old : Nat) :
    Ensures (beginSession pid) (fun w => tagAt w.k pid = some old)
      (fun ok w => tagAt w.k pid = some (if ok then HANDSHAKE_ZEROED else old) ∧
        (ok = true → old = HANDSHAKE_CREATED_RESPONSE ∨ old = HANDSHAKE_CONSUMED_RESPONSE)) := by
  rw [ensures_iff]
  have hc := keypairCreate_peers_spec (fun ps => (ps pid).map Peer.handshakeState = some old)
  have hd := deriveKeys_peers_spec (fun ps => (ps pid).map Peer.handshakeState = some old)
  have hi := indexReplaceHandshake_peers_spec (fun ps => (ps pid).map Peer.handshakeState = some 0)
  have ha := fun kp => addNewKeypair_tag_spec pid kp 0
  mvcgen [beginSession, IndexOwner.peerDeref, IndexOwner.peerWord, Leanux.WG.andM, handshakeZero, getPeer, getKeypair,
    getDev, getK, setPeer, setKeypair, modifyDev, modifyK, branch, invariant,
    unsupported, hc, hd, hi, ha]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [tagAt, peerAt, HANDSHAKE_ZEROED, Option.bind_map, Function.comp_def,
    Std.TreeMap.getElem?_insert]
  all_goals try assumption
  all_goals grind (gen := 8)

end Leanux.Proofs.WG.Noise
