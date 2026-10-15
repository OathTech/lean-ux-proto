import Leanux.Proofs.WG.TimerDiscipline.SendCutFrames

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem getPeer_initiationView (pid : PeerId) (v : InitiationView) :
    ⦃fun w => ⌜initiationAt w pid = some v⌝⦄ getPeer pid
      ⦃⇓ p w => ⌜initiationView p = v ∧ initiationAt w pid = some v⌝⦄ := by
  mvcgen [getPeer, getDev, getK, invariant]
  all_goals simp_all [initiationAt, peerAt]

theorem setPeer_initiationView (pid : PeerId) (v : InitiationView) (p : Peer) :
    ⦃fun w => ⌜initiationView p = v ∧ initiationAt w pid = some v⌝⦄ setPeer pid p
      ⦃⇓? _ w => ⌜initiationAt w pid = some v⌝⦄ := by
  mvcgen [setPeer, modifyDev, modifyK]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [initiationAt, peerAt, Option.bind_map, Function.comp_def]
  all_goals cases hd : (by assumption : World).k.wg <;> simp_all

theorem dstCacheGet_initiationView (pid : PeerId) (gen : Nat) (v : InitiationView) :
    ⦃fun w => ⌜initiationAt w pid = some v⌝⦄ dstCacheGet pid gen
      ⦃⇓? _ w => ⌜initiationAt w pid = some v⌝⦄ := by
  have hg := getPeer_initiationView pid v
  have hp := setPeer_initiationView pid v
  have hh := hidden_kernel_spec
    (fun k => ((k.wg.bind fun d => d.peers[pid]?).map initiationView) = some v)
  mvcgen [dstCacheGet, hiddenJiffies, invariant, unsupported, hg, hp, hh]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [initiationAt, initiationView, peerAt]

theorem dstCacheSet_initiationView (pid : PeerId) (src gen dev : Nat) (v : InitiationView) :
    ⦃fun w => ⌜initiationAt w pid = some v⌝⦄ dstCacheSet pid src gen dev
      ⦃⇓? _ w => ⌜initiationAt w pid = some v⌝⦄ := by
  have hg := getPeer_initiationView pid v
  have hp := setPeer_initiationView pid v
  mvcgen [dstCacheSet, hg, hp]
  all_goals simp_all [initiationView]

theorem dstCacheReset_initiationView (pid : PeerId) (v : InitiationView) :
    ⦃fun w => ⌜initiationAt w pid = some v⌝⦄ dstCacheReset pid
      ⦃⇓? _ w => ⌜initiationAt w pid = some v⌝⦄ := by
  have hg := getPeer_initiationView pid v
  have hp := setPeer_initiationView pid v
  have hh := hidden_kernel_spec
    (fun k => ((k.wg.bind fun d => d.peers[pid]?).map initiationView) = some v)
  mvcgen [dstCacheReset, hiddenJiffies, invariant, unsupported, hg, hp, hh]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [initiationAt, initiationView, peerAt]

abbrev tunnelXmit := noise_const _private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit

theorem tunnelXmit_initiationView (pid : PeerId) (e : Endpoint) (bytes : List UInt8)
    (ds : Nat) (r : Route) (exactRx : Bool) (v : InitiationView) :
    ⦃fun w => ⌜initiationAt w pid = some v⌝⦄ tunnelXmit e bytes ds r exactRx
      ⦃⇓? _ w => ⌜initiationAt w pid = some v⌝⦄ := by
  let P := fun k : Kernel => ((k.wg.bind fun d => d.peers[pid]?).map initiationView) = some v
  have hc := skipCut_spec_kernel_variant P
  have hl := loopbackSend_spec_kernel_variant P
  noise_vcgen [_private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit, socketPort,
    getDev, getK, modifyDev, modifyK, invariant, unsupported, hc, hl]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [P, initiationAt, peerAt, Option.bind_map, Function.comp_def]

end Leanux.Proofs.WG.TimerDiscipline
