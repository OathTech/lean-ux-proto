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
  noise_vcgen [keypairPut, indexRemove, IndexOwner.peerDeref, IndexOwner.peerWord, _private.Leanux.WG.Peer.«0».Leanux.WG.unhashEntry, getKeypair, getDev,
    getK, setKeypair, refcountDecAndTest, branch, branchCmp, branchCmpExcluded,
    invariant, unsupported, hm]
  all_goals try dsimp +zetaDelta only at *
  all_goals dsimp [peerAt] at *
  all_goals simp_all

def tagAt (k : Kernel) (pid : PeerId) : Option Nat :=
  (k.wg.bind fun d => d.peers[pid]?).map Peer.handshakeState

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

end Leanux.Proofs.WG.Noise
