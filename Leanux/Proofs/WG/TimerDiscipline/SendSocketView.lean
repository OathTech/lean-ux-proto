import Leanux.Proofs.WG.TimerDiscipline.SendPeerView

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem send4_initiationView (pid : PeerId) (e : Endpoint) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) (v : InitiationView) :
    ⦃fun w => ⌜initiationAt w pid = some v⌝⦄ send4 e (some pid) bytes ds exactRx
      ⦃⇓? _ w => ⌜initiationAt w pid = some v⌝⦄ := by
  have hg := getPeer_initiationView pid v
  have hp := setPeer_initiationView pid v
  have hc := fun gen => dstCacheGet_initiationView pid gen v
  have hr := dstCacheReset_initiationView pid v
  have hs := fun src gen dev => dstCacheSet_initiationView pid src gen dev v
  have ht := fun r => tunnelXmit_initiationView pid e bytes ds r exactRx v
  have routeFrame (family src dst : Nat) :
      ⦃fun w => ⌜initiationAt w pid = some v⌝⦄ routeLookup family src dst
        ⦃⇓? _ w => ⌜initiationAt w pid = some v⌝⦄ := by
    mvcgen [routeLookup]
    all_goals simp_all [initiationAt, peerAt]
  simp only [send4, Option.get!_some]
  mvcgen [getDev, getK, branch, invariant, unsupported, hg, hp, hc, hr, hs, ht, routeFrame]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [initiationAt, initiationView, peerAt]
  all_goals grind only

theorem send6_initiationView (pid : PeerId) (e : Endpoint) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) (v : InitiationView) :
    ⦃fun w => ⌜initiationAt w pid = some v⌝⦄ send6 e (some pid) bytes ds exactRx
      ⦃⇓? _ w => ⌜initiationAt w pid = some v⌝⦄ := by
  have hg := getPeer_initiationView pid v
  have hp := setPeer_initiationView pid v
  have hc := fun gen => dstCacheGet_initiationView pid gen v
  have hr := dstCacheReset_initiationView pid v
  have hs := fun src gen dev => dstCacheSet_initiationView pid src gen dev v
  have ht := fun r => tunnelXmit_initiationView pid e bytes ds r exactRx v
  have routeFrame (family src dst : Nat) :
      ⦃fun w => ⌜initiationAt w pid = some v⌝⦄ routeLookup family src dst
        ⦃⇓? _ w => ⌜initiationAt w pid = some v⌝⦄ := by
    mvcgen [routeLookup]
    all_goals simp_all [initiationAt, peerAt]
  simp only [send6, Option.get!_some]
  mvcgen [getDev, getK, branch, invariant, unsupported, hg, hp, hc, hr, hs, ht, routeFrame]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [initiationAt, initiationView, peerAt]
  all_goals grind only

end Leanux.Proofs.WG.TimerDiscipline
