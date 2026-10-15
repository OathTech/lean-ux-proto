import Leanux.Proofs.WG.TimerDiscipline.SendPeerFrames

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem send4_sendWorkView (pid : PeerId) (e : Endpoint) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) (q : Option SendWorkDevice) (v : Option SendWorkPeer) :
    ⦃fun w => ⌜sendWorkAt w pid = (q, v)⌝⦄ send4 e (some pid) bytes ds exactRx
      ⦃⇓? _ w => ⌜sendWorkAt w pid = (q, v)⌝⦄ := by
  have hg := getPeer_sendWorkView pid q v
  have hp := setPeer_sendWorkView pid q v
  have hc := fun gen => dstCacheGet_sendWorkView pid gen q v
  have hr := dstCacheReset_sendWorkView pid q v
  have hs := fun src gen dev => dstCacheSet_sendWorkView pid src gen dev q v
  have ht := fun r => tunnelXmit_sendWorkView pid e bytes ds r exactRx q v
  have routeFrame (family src dst : Nat) :
      ⦃fun w => ⌜sendWorkAt w pid = (q, v)⌝⦄ routeLookup family src dst
        ⦃⇓? _ w => ⌜sendWorkAt w pid = (q, v)⌝⦄ := by
    mvcgen [routeLookup]
    all_goals simp_all [sendWorkAt, sendWorkKernel, sendWorkDevice, tableCursor, initiationAt, peerAt]
  simp only [send4, Option.get!_some]
  mvcgen [getDev, getK, branch, invariant, unsupported, hg, hp, hc, hr, hs, ht, routeFrame]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [sendWorkAt, sendWorkKernel, sendWorkDevice, tableCursor, initiationAt, sendWorkPeer, initiationView, peerAt]
  all_goals grind only

theorem send6_sendWorkView (pid : PeerId) (e : Endpoint) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) (q : Option SendWorkDevice) (v : Option SendWorkPeer) :
    ⦃fun w => ⌜sendWorkAt w pid = (q, v)⌝⦄ send6 e (some pid) bytes ds exactRx
      ⦃⇓? _ w => ⌜sendWorkAt w pid = (q, v)⌝⦄ := by
  have hg := getPeer_sendWorkView pid q v
  have hp := setPeer_sendWorkView pid q v
  have hc := fun gen => dstCacheGet_sendWorkView pid gen q v
  have hr := dstCacheReset_sendWorkView pid q v
  have hs := fun src gen dev => dstCacheSet_sendWorkView pid src gen dev q v
  have ht := fun r => tunnelXmit_sendWorkView pid e bytes ds r exactRx q v
  have routeFrame (family src dst : Nat) :
      ⦃fun w => ⌜sendWorkAt w pid = (q, v)⌝⦄ routeLookup family src dst
        ⦃⇓? _ w => ⌜sendWorkAt w pid = (q, v)⌝⦄ := by
    mvcgen [routeLookup]
    all_goals simp_all [sendWorkAt, sendWorkKernel, sendWorkDevice, tableCursor, initiationAt, peerAt]
  simp only [send6, Option.get!_some]
  mvcgen [getDev, getK, branch, invariant, unsupported, hg, hp, hc, hr, hs, ht, routeFrame]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [sendWorkAt, sendWorkKernel, sendWorkDevice, tableCursor, initiationAt, sendWorkPeer, initiationView, peerAt]
  all_goals grind only

theorem send4_sendView (pid : PeerId) (e : Endpoint) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) (q : Option TableCursor) (v : Option InitiationView) :
    ⦃fun w => ⌜sendAt w pid = (q, v)⌝⦄ send4 e (some pid) bytes ds exactRx
      ⦃⇓? _ w => ⌜sendAt w pid = (q, v)⌝⦄ := by
  exact send_frame_of_sendWork (send4 e (some pid) bytes ds exactRx) pid
    (send4_sendWorkView pid e bytes ds exactRx) q v

theorem send6_sendView (pid : PeerId) (e : Endpoint) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) (q : Option TableCursor) (v : Option InitiationView) :
    ⦃fun w => ⌜sendAt w pid = (q, v)⌝⦄ send6 e (some pid) bytes ds exactRx
      ⦃⇓? _ w => ⌜sendAt w pid = (q, v)⌝⦄ := by
  exact send_frame_of_sendWork (send6 e (some pid) bytes ds exactRx) pid
    (send6_sendWorkView pid e bytes ds exactRx) q v

theorem send4_initiationView (pid : PeerId) (e : Endpoint) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) (v : InitiationView) :
    ⦃fun w => ⌜initiationAt w pid = some v⌝⦄ send4 e (some pid) bytes ds exactRx
      ⦃⇓? _ w => ⌜initiationAt w pid = some v⌝⦄ := by
  exact initiation_frame_of_send (send4 e (some pid) bytes ds exactRx) pid (send4_sendView pid e bytes ds exactRx) v

theorem send6_initiationView (pid : PeerId) (e : Endpoint) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) (v : InitiationView) :
    ⦃fun w => ⌜initiationAt w pid = some v⌝⦄ send6 e (some pid) bytes ds exactRx
      ⦃⇓? _ w => ⌜initiationAt w pid = some v⌝⦄ := by
  exact initiation_frame_of_send (send6 e (some pid) bytes ds exactRx) pid (send6_sendView pid e bytes ds exactRx) v

end Leanux.Proofs.WG.TimerDiscipline
