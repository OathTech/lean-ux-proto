import Leanux.Proofs.WG.Index.StagedFrames
import Leanux.Proofs.WG.Index.SendSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- Both immediate unhash and final-reference release filter rows; a retained
reference need not have a non-NULL peer word. Only normal returns are claimed. -/
theorem keypairPut_tables (key : Option KeypairId) (now : Bool) :
    ⦃fun w => ⌜TablesSafeKernel w.k⌝⦄ keypairPut key now
      ⦃⇓? _ w => ⌜TablesSafeKernel w.k⌝⦄ := by
  have hp := setKeypair_tables
  have hr := indexRemove_tables
  have hc := refcountDecAndTest_kernel_variant TablesSafeKernel
  mvcgen [keypairPut, IndexOwner.peerDeref, IndexOwner.peerWord,
    getKeypair, getPeer, getDev, getK, branch, invariant,
    modifyDev, modifyK, hp, hr, hc]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [TablesSafeKernel, DeviceTablesSafe, KeypairOwnersBounded]
  all_goals grind

theorem sendQueuedHandshakeInitiation_tables (pid : PeerId) (retry : Bool) :
    ⦃fun w => ⌜TablesSafeKernel w.k⌝⦄ sendQueuedHandshakeInitiation pid retry
      ⦃⇓? _ w => ⌜TablesSafeKernel w.k⌝⦄ := by
  have hs := setPeer_tables
  have hg := peerGet_tables
  have hp := peerPut_tables
  have hh := hiddenClock64_kernel_spec TablesSafeKernel
  have hq := Config.recordQueued_kernel TablesSafeKernel
  mvcgen [sendQueuedHandshakeInitiation, requireNotPending, branchExpired,
    birthdateTest, getPeer, getDev, getK, branch, branchCmp, invariant,
    modifyDev, modifyK, hs, hg, hp, hh, hq]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [TablesSafeKernel, DeviceTablesSafe, KeypairOwnersBounded]
  all_goals grind

theorem enqueuePerPeerTx_tables (item : List SkbId) (state : PacketState) :
    ⦃fun w => ⌜TablesSafeKernel w.k⌝⦄ enqueuePerPeerTx item state
      ⦃⇓? _ w => ⌜TablesSafeKernel w.k⌝⦄ := by
  have hg := peerGet_tables
  have hp := peerPut_tables
  have hs := setTxSkb_tables
  have hc := cpumaskChooseOnline_tables
  have hq := Config.recordQueued_kernel TablesSafeKernel
  have hk := peekQueuedUnit_kernel_variant TablesSafeKernel
  mvcgen [enqueuePerPeerTx, IndexOwner.peerDeref, IndexOwner.peerWord,
    getTxSkb, getKeypair, getPeer, getDev, getK, invariant,
    modifyDev, modifyK, hg, hp, hs, hc, hq, hk]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [TablesSafeKernel, DeviceTablesSafe, KeypairOwnersBounded]
  all_goals grind

/-- Includes EPIPE dead publication, and the other-failure key/peer releases. -/
theorem createData_tables (pid : PeerId) (item : List SkbId) :
    ⦃fun w => ⌜TablesSafeKernel w.k⌝⦄ createData pid item
      ⦃⇓? _ w => ⌜TablesSafeKernel w.k⌝⦄ := by
  have he := enqueuePerDeviceAndPeer_tables
  have ht := enqueuePerPeerTx_tables
  have hk := keypairPut_tables
  have hp := peerPut_tables
  have hf := freeTxSkb_tables
  mvcgen [createData, getPeer, getTxSkb, getDev, getK, branch, invariant, he, ht, hk, hp, hf]
  all_goals try exact ((⇓? _ w => ⌜TablesSafeKernel w.k⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [ExceptConds.true, ExceptConds.const]

theorem stagedFallback_tables (pid : PeerId) (packets : List Packet)
    (key : Option KeypairId) (invalid : Bool) :
    ⦃fun w => ⌜TablesSafeKernel w.k⌝⦄ Config.stagedFallback pid packets key invalid
      ⦃⇓? _ w => ⌜TablesSafeKernel w.k⌝⦄ := by
  have hs := setKeypair_tables
  have hk := keypairPut_tables
  have hp := setPeer_tables
  have hq := sendQueuedHandshakeInitiation_tables
  mvcgen [Config.stagedFallback, getKeypair, getPeer, getDev, getK,
    branch, invariant, hs, hk, hp, hq]
  all_goals try exact ((⇓? _ w => ⌜TablesSafeKernel w.k⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [ExceptConds.true, ExceptConds.const]

theorem stagedAfterGet_tables (pid : PeerId) (packets : List Packet) (key : Option KeypairId) :
    ⦃fun w => ⌜TablesSafeKernel w.k⌝⦄ Config.stagedAfterGet pid packets key
      ⦃⇓? _ w => ⌜TablesSafeKernel w.k⌝⦄ := by
  have hf := stagedFallback_tables
  have hh := hiddenClock64_kernel_spec TablesSafeKernel
  have he := ipTunnelEcnEncap_kernel_variant TablesSafeKernel
  have hs := setKeypair_tables
  have hg := peerGet_tables
  have hn := newTxSkbs_tables
  have hd := createData_tables
  mvcgen [Config.stagedAfterGet, branchExpired, birthdateTest,
    IndexOwner.peerDeref, IndexOwner.peerWord, getKeypair, getPeer, getDev, getK,
    branch, branchCmp, invariant, hf, hh, he, hs, hg, hn, hd]
  all_goals try exact ((⇓? _ w => ⌜TablesSafeKernel w.k⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [ExceptConds.true, ExceptConds.const]

theorem sendStagedPackets_tables (pid : PeerId) :
    Ensures (sendStagedPackets pid) (fun w => TablesSafeKernel w.k)
      (fun _ w => TablesSafeKernel w.k) := by
  rw [← Config.sendStaged_source, ensures_iff]
  have hs := setPeer_tables
  have hg := keypairGet_tables
  have ht := stagedAfterGet_tables
  mvcgen [Config.stagedSource, getPeer, getDev, getK, branch, invariant, hs, hg, ht]

theorem sendKeepalive_tables (pid : PeerId) :
    Ensures (sendKeepalive pid) (fun w => TablesSafeKernel w.k)
      (fun _ w => TablesSafeKernel w.k) := by
  have ha := keypairAllocation_kernel_spec_keepalive_variant TablesSafeKernel
  have hp := setPeer_tables
  have hs := (ensures_iff _ _ _).mp (sendStagedPackets_tables pid)
  rw [ensures_iff]
  mvcgen [sendKeepalive, getPeer, getDev, getK, branch, invariant, ha, hp, hs]

end Leanux.Proofs.WG.Index
