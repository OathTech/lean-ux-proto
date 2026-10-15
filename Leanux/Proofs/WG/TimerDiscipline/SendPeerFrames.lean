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

def sendWorkKernel (k : Kernel) (pid : PeerId) : SendWorkView :=
  (k.wg.map sendWorkDevice, (k.wg.bind fun d => d.peers[pid]?).map sendWorkPeer)

def sendWorkAt (w : World) (pid : PeerId) : SendWorkView := sendWorkKernel w.k pid

def workKernel (k : Kernel) (pid : PeerId) : WorkView :=
  (k.wg.map Device.sendWorkQueue, (k.wg.bind fun d => d.peers[pid]?).map Peer.handshakePending)

def workAt (w : World) (pid : PeerId) : WorkView := workKernel w.k pid

theorem workAt_observation (w : World) (pid : PeerId) :
    workAt w pid = workObservation (Campaign2.snapshot w) pid := rfl

abbrev tunnelXmit := noise_const _private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit

/-- Existing send interfaces forget only the added work-state fields. -/
theorem send_frame_of_sendWork {α : Type} (action : M α) (pid : PeerId)
    (frame : ∀ (q : Option SendWorkDevice) (v : Option SendWorkPeer),
      ⦃fun w => ⌜sendWorkAt w pid = (q, v)⌝⦄ action
        ⦃⇓? _ w => ⌜sendWorkAt w pid = (q, v)⌝⦄)
    (q : Option TableCursor) (v : Option InitiationView) :
    ⦃fun w => ⌜sendAt w pid = (q, v)⌝⦄ action
      ⦃⇓? _ w => ⌜sendAt w pid = (q, v)⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro w result final pre run
  have h := (ensures_iff _ _ _).mpr
    (frame (sendWorkAt w pid).1 (sendWorkAt w pid).2) w result final rfl run
  have projected := congrArg (fun x : SendWorkView =>
    (x.1.map Prod.fst, x.2.map Prod.fst)) h
  have same : sendAt final pid = sendAt w pid := by
    simpa [sendAt, sendKernel, sendWorkAt, sendWorkKernel, sendWorkDevice,
      sendWorkPeer, Option.map_map, Function.comp_def] using projected
  exact same.trans pre

theorem work_frame_of_sendWork {α : Type} (action : M α) (pid : PeerId)
    (frame : ∀ (q : Option SendWorkDevice) (v : Option SendWorkPeer),
      ⦃fun w => ⌜sendWorkAt w pid = (q, v)⌝⦄ action
        ⦃⇓? _ w => ⌜sendWorkAt w pid = (q, v)⌝⦄) (v : WorkView) :
    ⦃fun w => ⌜workAt w pid = v⌝⦄ action
      ⦃⇓? _ w => ⌜workAt w pid = v⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro w result final pre run
  have h := (ensures_iff _ _ _).mpr
    (frame (sendWorkAt w pid).1 (sendWorkAt w pid).2) w result final rfl run
  have projected := congrArg (fun x : SendWorkView =>
    (x.1.map Prod.snd, x.2.map Prod.snd)) h
  have same : workAt final pid = workAt w pid := by
    simpa [workAt, workKernel, sendWorkAt, sendWorkKernel, sendWorkDevice,
      sendWorkPeer, Option.map_map, Function.comp_def] using projected
  exact same.trans pre

theorem getPeer_sendWorkView (pid : PeerId) (q : Option SendWorkDevice) (v : Option SendWorkPeer) :
    ⦃fun w => ⌜sendWorkAt w pid = (q, v)⌝⦄ getPeer pid
      ⦃⇓? p w => ⌜some (sendWorkPeer p) = v ∧ sendWorkAt w pid = (q, v)⌝⦄ := by
  mvcgen [getPeer, getDev, getK, invariant]
  all_goals simp_all [sendWorkAt, sendWorkKernel, sendWorkDevice, tableCursor, initiationAt, peerAt]

theorem setPeer_sendWorkView (pid : PeerId) (q : Option SendWorkDevice) (v : Option SendWorkPeer) (p : Peer) :
    ⦃fun w => ⌜some (sendWorkPeer p) = v ∧ sendWorkAt w pid = (q, v)⌝⦄ setPeer pid p
      ⦃⇓? _ w => ⌜sendWorkAt w pid = (q, v)⌝⦄ := by
  mvcgen [setPeer, modifyDev, modifyK]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [sendWorkAt, sendWorkKernel, sendWorkDevice, tableCursor, initiationAt, peerAt, Option.bind_map, Function.comp_def]
  all_goals cases hd : (by assumption : World).k.wg <;> simp_all [sendWorkDevice, tableCursor]

theorem dstCacheGet_sendWorkView (pid : PeerId) (gen : Nat) (q : Option SendWorkDevice) (v : Option SendWorkPeer) :
    ⦃fun w => ⌜sendWorkAt w pid = (q, v)⌝⦄ dstCacheGet pid gen
      ⦃⇓? _ w => ⌜sendWorkAt w pid = (q, v)⌝⦄ := by
  have hg := getPeer_sendWorkView pid q v
  have hp := setPeer_sendWorkView pid q v
  have hh := hidden_kernel_spec
    (fun k => sendWorkKernel k pid = (q, v))
  mvcgen [dstCacheGet, hiddenJiffies, invariant, unsupported, hg, hp, hh]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [sendWorkAt, sendWorkKernel, sendWorkDevice, tableCursor, initiationAt, sendWorkPeer, initiationView, peerAt]

theorem dstCacheSet_sendWorkView (pid : PeerId) (src gen dev : Nat) (q : Option SendWorkDevice) (v : Option SendWorkPeer) :
    ⦃fun w => ⌜sendWorkAt w pid = (q, v)⌝⦄ dstCacheSet pid src gen dev
      ⦃⇓? _ w => ⌜sendWorkAt w pid = (q, v)⌝⦄ := by
  have hg := getPeer_sendWorkView pid q v
  have hp := setPeer_sendWorkView pid q v
  mvcgen [dstCacheSet, hg, hp]
  all_goals simp_all [sendWorkPeer, initiationView]

theorem dstCacheReset_sendWorkView (pid : PeerId) (q : Option SendWorkDevice) (v : Option SendWorkPeer) :
    ⦃fun w => ⌜sendWorkAt w pid = (q, v)⌝⦄ dstCacheReset pid
      ⦃⇓? _ w => ⌜sendWorkAt w pid = (q, v)⌝⦄ := by
  have hg := getPeer_sendWorkView pid q v
  have hp := setPeer_sendWorkView pid q v
  have hh := hidden_kernel_spec
    (fun k => sendWorkKernel k pid = (q, v))
  mvcgen [dstCacheReset, hiddenJiffies, invariant, unsupported, hg, hp, hh]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [sendWorkAt, sendWorkKernel, sendWorkDevice, tableCursor, initiationAt, sendWorkPeer, initiationView, peerAt]

theorem tunnelXmit_sendWorkView (pid : PeerId) (e : Endpoint) (bytes : List UInt8)
    (ds : Nat) (r : Route) (exactRx : Bool) (q : Option SendWorkDevice) (v : Option SendWorkPeer) :
    ⦃fun w => ⌜sendWorkAt w pid = (q, v)⌝⦄ tunnelXmit e bytes ds r exactRx
      ⦃⇓? _ w => ⌜sendWorkAt w pid = (q, v)⌝⦄ := by
  let P := fun k : Kernel => sendWorkKernel k pid = (q, v)
  have hc := skipCut_spec_kernel_variant P
  have hl := loopbackSend_spec_kernel_variant P
  noise_vcgen [_private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit, socketPort,
    getDev, getK, modifyDev, modifyK, invariant, unsupported, hc, hl]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [P, sendWorkAt, sendWorkKernel, sendWorkDevice, tableCursor, initiationAt, peerAt, Option.bind_map, Function.comp_def]

  all_goals grind [sendWorkDevice, tableCursor]

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
  exact send_frame_of_sendWork (dstCacheGet pid gen) pid (dstCacheGet_sendWorkView pid gen) q v

theorem dstCacheSet_sendView (pid : PeerId) (src gen dev : Nat) (q : Option TableCursor) (v : Option InitiationView) :
    ⦃fun w => ⌜sendAt w pid = (q, v)⌝⦄ dstCacheSet pid src gen dev
      ⦃⇓? _ w => ⌜sendAt w pid = (q, v)⌝⦄ := by
  exact send_frame_of_sendWork (dstCacheSet pid src gen dev) pid (dstCacheSet_sendWorkView pid src gen dev) q v

theorem dstCacheReset_sendView (pid : PeerId) (q : Option TableCursor) (v : Option InitiationView) :
    ⦃fun w => ⌜sendAt w pid = (q, v)⌝⦄ dstCacheReset pid
      ⦃⇓? _ w => ⌜sendAt w pid = (q, v)⌝⦄ := by
  exact send_frame_of_sendWork (dstCacheReset pid) pid (dstCacheReset_sendWorkView pid) q v

theorem tunnelXmit_sendView (pid : PeerId) (e : Endpoint) (bytes : List UInt8) (ds : Nat) (r : Route) (exactRx : Bool) (q : Option TableCursor) (v : Option InitiationView) :
    ⦃fun w => ⌜sendAt w pid = (q, v)⌝⦄ tunnelXmit e bytes ds r exactRx
      ⦃⇓? _ w => ⌜sendAt w pid = (q, v)⌝⦄ := by
  exact send_frame_of_sendWork (tunnelXmit e bytes ds r exactRx) pid (tunnelXmit_sendWorkView pid e bytes ds r exactRx) q v

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
