import Leanux.Proofs.WG.Index.ReceiveFrames
import Leanux.Proofs.WG.Index.ConsumeSource
import Leanux.Proofs.WG.Index.ResponseSource
import Leanux.Proofs.WG.Index.StagedSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- The original post-load body retains actual lookup, installation and release. -/
theorem receivePacketBody_tables (msg : List UInt8) (src : SkbSource) (underLoad : Bool) :
    Ensures (receivePacketBody msg src underLoad) (fun w => TablesSafeKernel w.k)
      (fun _ w => TablesSafeKernel w.k) := by
  have hi := (ensures_iff _ _ _).mp (consumeInitiation_tables msg)
  have hr := (ensures_iff _ _ _).mp (consumeResponse_tables msg)
  have hs := fun pid => (ensures_iff _ _ _).mp (sendHandshakeResponse_tables pid)
  have hk := fun pid => (ensures_iff _ _ _).mp (sendKeepalive_tables pid)
  have hb := beginSession_tables
  have hv := cookieValidatePacket_tables
  have hcook := sendHandshakeCookie_tables
  have he := setPeerEndpointFromSkb_tables
  have ht := timersSessionDerived_tables
  have hcomplete := timersHandshakeComplete_tables
  have ha := timersAnyAuthenticatedPacketReceived_tables
  have htr := traversal_tables
  have hp := peerPut_tables
  have hset := setPeer_tables
  have hstats := receiveStats_tables
  rw [ensures_iff]
  mvcgen [receivePacketBody, WG.andM, WG.orM,
    getPeer, getDev, getK, branch, invariant,
    hstats, hi, hr, hs, hk, hb, hv, hcook, he, ht, hcomplete, ha, htr, hp, hset]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all
  all_goals trivial

/-- Compose the exact original load prefix and packet body, preserving all stops. -/
theorem receiveHandshakePacket_tables (msg : List UInt8) (src : SkbSource) :
    Ensures (receiveHandshakePacket msg src) (fun w => TablesSafeKernel w.k)
      (fun _ w => TablesSafeKernel w.k) := by
  have hc := (ensures_iff _ _ _).mp (cookieMessageConsume_tables msg)
  have hb := fun underLoad => (ensures_iff _ _ _).mp (receivePacketBody_tables msg src underLoad)
  have hl := receiveLoadThen_tables (receivePacketBody msg src) hb
  rw [← receivePacket_source, ensures_iff]
  mvcgen [receivePacketSource, branch, hc, hl]

/-- One original queue iteration, including removal before the packet body and
counter decrement only after normal body completion. No worker scheduler is run. -/
theorem receiveStep_tables : Ensures receiveStep (fun w => TablesSafeKernel w.k)
    (fun _ w => TablesSafeKernel w.k) := by
  have hr := fun msg src => (ensures_iff _ _ _).mp (receiveHandshakePacket_tables msg src)
  rw [ensures_iff]
  mvcgen [receiveStep, getDev, getK, branch, invariant, modifyDev, modifyK, hr]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [TablesSafeKernel, DeviceTablesSafe, KeypairOwnersBounded]
  all_goals grind

end Leanux.Proofs.WG.Index
