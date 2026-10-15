import Leanux.Proofs.WG.TimerDiscipline.SendCutFrames
import Leanux.Proofs.WG.TimerDiscipline.SendView
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

def sendKernel (k : Kernel) (pid : PeerId) : SendView :=
  (k.wg.map tableCursor, (k.wg.bind fun d => d.peers[pid]?).map initiationView)

def sendAt (w : World) (pid : PeerId) : SendView := sendKernel w.k pid

theorem sendAt_observation (w : World) (pid : PeerId) :
    sendAt w pid = sendObservation (Campaign2.snapshot w) pid := rfl

/-- Forget only the additional table/cursor observation of a send frame. -/
theorem initiation_frame_of_send {α : Type} (action : M α) (pid : PeerId)
    (frame : ∀ (q : Option TableCursor) (v : Option InitiationView),
      ⦃fun w => ⌜sendAt w pid = (q, v)⌝⦄ action
        ⦃⇓? _ w => ⌜sendAt w pid = (q, v)⌝⦄) (v : InitiationView) :
    ⦃fun w => ⌜initiationAt w pid = some v⌝⦄ action
      ⦃⇓? _ w => ⌜initiationAt w pid = some v⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro w result final pre run
  have h := (ensures_iff _ _ _).mpr (frame (sendAt w pid).1 (some v)) w result final
    (by simpa [sendAt, sendKernel, initiationAt, peerAt] using pre) run
  exact congrArg Prod.snd h

theorem getPeer_sendView (pid : PeerId) (q : Option TableCursor) (v : Option InitiationView) :
    ⦃fun w => ⌜sendAt w pid = (q, v)⌝⦄ getPeer pid
      ⦃⇓? p w => ⌜some (initiationView p) = v ∧ sendAt w pid = (q, v)⌝⦄ := by
  mvcgen [getPeer, getDev, getK, invariant]
  all_goals simp_all [sendAt, sendKernel, tableCursor, initiationAt, peerAt]

theorem setPeer_sendView (pid : PeerId) (q : Option TableCursor) (v : Option InitiationView) (p : Peer) :
    ⦃fun w => ⌜some (initiationView p) = v ∧ sendAt w pid = (q, v)⌝⦄ setPeer pid p
      ⦃⇓? _ w => ⌜sendAt w pid = (q, v)⌝⦄ := by
  mvcgen [setPeer, modifyDev, modifyK]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [sendAt, sendKernel, tableCursor, initiationAt, peerAt, Option.bind_map, Function.comp_def]
  all_goals cases hd : (by assumption : World).k.wg <;> simp_all [tableCursor]

theorem dstCacheGet_sendView (pid : PeerId) (gen : Nat) (q : Option TableCursor) (v : Option InitiationView) :
    ⦃fun w => ⌜sendAt w pid = (q, v)⌝⦄ dstCacheGet pid gen
      ⦃⇓? _ w => ⌜sendAt w pid = (q, v)⌝⦄ := by
  have hg := getPeer_sendView pid q v
  have hp := setPeer_sendView pid q v
  have hh := hidden_kernel_spec
    (fun k => sendKernel k pid = (q, v))
  mvcgen [dstCacheGet, hiddenJiffies, invariant, unsupported, hg, hp, hh]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [sendAt, sendKernel, tableCursor, initiationAt, initiationView, peerAt]

theorem dstCacheSet_sendView (pid : PeerId) (src gen dev : Nat) (q : Option TableCursor) (v : Option InitiationView) :
    ⦃fun w => ⌜sendAt w pid = (q, v)⌝⦄ dstCacheSet pid src gen dev
      ⦃⇓? _ w => ⌜sendAt w pid = (q, v)⌝⦄ := by
  have hg := getPeer_sendView pid q v
  have hp := setPeer_sendView pid q v
  mvcgen [dstCacheSet, hg, hp]
  all_goals simp_all [initiationView]

theorem dstCacheReset_sendView (pid : PeerId) (q : Option TableCursor) (v : Option InitiationView) :
    ⦃fun w => ⌜sendAt w pid = (q, v)⌝⦄ dstCacheReset pid
      ⦃⇓? _ w => ⌜sendAt w pid = (q, v)⌝⦄ := by
  have hg := getPeer_sendView pid q v
  have hp := setPeer_sendView pid q v
  have hh := hidden_kernel_spec
    (fun k => sendKernel k pid = (q, v))
  mvcgen [dstCacheReset, hiddenJiffies, invariant, unsupported, hg, hp, hh]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [sendAt, sendKernel, tableCursor, initiationAt, initiationView, peerAt]

abbrev tunnelXmit := noise_const _private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit

theorem tunnelXmit_sendView (pid : PeerId) (e : Endpoint) (bytes : List UInt8)
    (ds : Nat) (r : Route) (exactRx : Bool) (q : Option TableCursor) (v : Option InitiationView) :
    ⦃fun w => ⌜sendAt w pid = (q, v)⌝⦄ tunnelXmit e bytes ds r exactRx
      ⦃⇓? _ w => ⌜sendAt w pid = (q, v)⌝⦄ := by
  let P := fun k : Kernel => sendKernel k pid = (q, v)
  have hc := skipCut_spec_kernel_variant P
  have hl := loopbackSend_spec_kernel_variant P
  noise_vcgen [_private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit, socketPort,
    getDev, getK, modifyDev, modifyK, invariant, unsupported, hc, hl]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [P, sendAt, sendKernel, tableCursor, initiationAt, peerAt, Option.bind_map, Function.comp_def]

  all_goals grind [tableCursor]

theorem getPeer_initiationView (pid : PeerId) (v : InitiationView) :
    ⦃fun w => ⌜initiationAt w pid = some v⌝⦄ getPeer pid
      ⦃⇓ p w => ⌜initiationView p = v ∧ initiationAt w pid = some v⌝⦄ := by
  mvcgen [getPeer, getDev, getK, invariant]
  all_goals simp_all [initiationAt, peerAt]

theorem setPeer_initiationView (pid : PeerId) (v : InitiationView) (p : Peer) :
    ⦃fun w => ⌜initiationView p = v ∧ initiationAt w pid = some v⌝⦄ setPeer pid p
      ⦃⇓? _ w => ⌜initiationAt w pid = some v⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro w result final pre run
  have h := (ensures_iff _ _ _).mpr
    (setPeer_sendView pid (sendAt w pid).1 (some v) p) w result final
    (by simpa [sendAt, sendKernel, initiationAt, peerAt] using pre) run
  exact congrArg Prod.snd h

theorem dstCacheGet_initiationView (pid : PeerId) (gen : Nat) (v : InitiationView) :
    ⦃fun w => ⌜initiationAt w pid = some v⌝⦄ dstCacheGet pid gen
      ⦃⇓? _ w => ⌜initiationAt w pid = some v⌝⦄ := by
  exact initiation_frame_of_send (dstCacheGet pid gen) pid (dstCacheGet_sendView pid gen) v

theorem dstCacheSet_initiationView (pid : PeerId) (src gen dev : Nat) (v : InitiationView) :
    ⦃fun w => ⌜initiationAt w pid = some v⌝⦄ dstCacheSet pid src gen dev
      ⦃⇓? _ w => ⌜initiationAt w pid = some v⌝⦄ := by
  exact initiation_frame_of_send (dstCacheSet pid src gen dev) pid (dstCacheSet_sendView pid src gen dev) v

theorem dstCacheReset_initiationView (pid : PeerId) (v : InitiationView) :
    ⦃fun w => ⌜initiationAt w pid = some v⌝⦄ dstCacheReset pid
      ⦃⇓? _ w => ⌜initiationAt w pid = some v⌝⦄ := by
  exact initiation_frame_of_send (dstCacheReset pid) pid (dstCacheReset_sendView pid) v

theorem tunnelXmit_initiationView (pid : PeerId) (e : Endpoint) (bytes : List UInt8)
    (ds : Nat) (r : Route) (exactRx : Bool) (v : InitiationView) :
    ⦃fun w => ⌜initiationAt w pid = some v⌝⦄ tunnelXmit e bytes ds r exactRx
      ⦃⇓? _ w => ⌜initiationAt w pid = some v⌝⦄ := by
  exact initiation_frame_of_send (tunnelXmit e bytes ds r exactRx) pid (tunnelXmit_sendView pid e bytes ds r exactRx) v

end Leanux.Proofs.WG.TimerDiscipline
