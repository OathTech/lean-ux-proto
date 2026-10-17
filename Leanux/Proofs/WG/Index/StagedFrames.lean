import Leanux.Proofs.WG.Index.ConsumeFrames
import Leanux.Proofs.WG.Config.StagedSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

-- These writes leave both the hashed table and its allocation cursor untouched.
theorem setKeypair_tables (id : KeypairId) (k : Keypair) :
    ⦃fun w => ⌜TablesSafeKernel w.k⌝⦄ setKeypair id k
      ⦃⇓? _ w => ⌜TablesSafeKernel w.k⌝⦄ := by
  mvcgen [setKeypair, modifyDev, modifyK]
  all_goals try dsimp +zetaDelta only at *
  all_goals cases hd : (by assumption : World).k.wg <;>
    simp_all [TablesSafeKernel, DeviceTablesSafe, KeypairOwnersBounded]
  all_goals grind

theorem peerGet_tables (pid : PeerId) :
    ⦃fun w => ⌜TablesSafeKernel w.k⌝⦄ peerGet pid
      ⦃⇓? _ w => ⌜TablesSafeKernel w.k⌝⦄ := by
  have hp := setPeer_tables
  mvcgen [peerGet, requireNotPending, refcountInc, getPeer, getDev, getK,
    branch, branchCmp, invariant, unsupported, hp]

theorem keypairGet_tables (key : Option KeypairId) :
    ⦃fun w => ⌜TablesSafeKernel w.k⌝⦄ keypairGet key
      ⦃⇓? _ w => ⌜TablesSafeKernel w.k⌝⦄ := by
  have hp := setKeypair_tables
  have hr := refcountIncNotZero_kernel_variant TablesSafeKernel
  mvcgen [keypairGet, getKeypair, getDev, getK, branch, invariant, hp, hr]

theorem newTxSkb_tables (packet : DataPacket) :
    ⦃fun w => ⌜TablesSafeKernel w.k⌝⦄ newTxSkb packet
      ⦃⇓? _ w => ⌜TablesSafeKernel w.k⌝⦄ := by
  mvcgen [newTxSkb, getDev, getK, invariant, modifyDev, modifyK]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [TablesSafeKernel, DeviceTablesSafe, KeypairOwnersBounded]
  all_goals grind

theorem setTxSkb_tables (id : SkbId) (f : DataPacket → DataPacket) :
    ⦃fun w => ⌜TablesSafeKernel w.k⌝⦄ setTxSkb id f
      ⦃⇓? _ w => ⌜TablesSafeKernel w.k⌝⦄ := by
  mvcgen [setTxSkb, getTxSkb, getDev, getK, invariant, modifyDev, modifyK]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [TablesSafeKernel, DeviceTablesSafe, KeypairOwnersBounded]
  all_goals grind

theorem freeTxSkb_tables (id : SkbId) :
    ⦃fun w => ⌜TablesSafeKernel w.k⌝⦄ freeTxSkb id
      ⦃⇓? _ w => ⌜TablesSafeKernel w.k⌝⦄ := by
  mvcgen [freeTxSkb, getTxSkb, getDev, getK, invariant, modifyDev, modifyK]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [TablesSafeKernel, DeviceTablesSafe, KeypairOwnersBounded]
  all_goals grind

theorem cpumaskChooseOnline_tables (pid : PeerId) :
    ⦃fun w => ⌜TablesSafeKernel w.k⌝⦄ cpumaskChooseOnline pid
      ⦃⇓? _ w => ⌜TablesSafeKernel w.k⌝⦄ := by
  have hp := setPeer_tables
  simp only [cpumaskChooseOnline, Nat.mod_one]
  mvcgen [getPeer, getDev, getK, branch, invariant, hp]
  case inv1 => exact ((⇓? _ w => ⌜TablesSafeKernel w.k⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [ExceptConds.true, ExceptConds.const]

theorem ipTunnelEcnEncap_kernel_variant (P : Kernel → Prop) (pkt : Packet) :
    ⦃fun w => ⌜P w.k⌝⦄ ipTunnelEcnEncap pkt
      ⦃⇓? _ w => ⌜P w.k⌝⦄ := by
  mvcgen -trivial [ipTunnelEcnEncap, ipTunnelGetDsfield, Packet.protocol, branch, invariant, unsupported]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all
  all_goals trivial

/-- The new-skb map has the original ordered allocations and their actual states. -/
theorem newTxSkbs_tables (packets : List DataPacket) :
    ⦃fun w => ⌜TablesSafeKernel w.k⌝⦄ packets.mapM newTxSkb
      ⦃⇓? _ w => ⌜TablesSafeKernel w.k⌝⦄ := by
  have hf := newTxSkb_tables
  have loop (xs : List DataPacket) (acc : List SkbId) :
      ⦃fun w => ⌜TablesSafeKernel w.k⌝⦄ List.mapM.loop newTxSkb xs acc
        ⦃⇓? _ w => ⌜TablesSafeKernel w.k⌝⦄ := by
    induction xs generalizing acc with
    | nil => mvcgen [List.mapM.loop]
    | cons x xs ih => mvcgen [List.mapM.loop, hf, ih]
  exact loop packets []

theorem enqueuePerDeviceAndPeer_tables (pid : PeerId) (item : List SkbId) :
    ⦃fun w => ⌜TablesSafeKernel w.k⌝⦄ enqueuePerDeviceAndPeer pid item
      ⦃⇓? _ w => ⌜TablesSafeKernel w.k⌝⦄ := by
  have hs := setTxSkb_tables
  have hp := setPeer_tables
  have hq := queueDeviceWork_kernel_variant TablesSafeKernel
  mvcgen [enqueuePerDeviceAndPeer, cpumaskNextOnlineFrom,
    getPeer, getDev, getK, branch, invariant, modifyDev, modifyK, hs, hp, hq]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [TablesSafeKernel, DeviceTablesSafe, KeypairOwnersBounded]
  all_goals grind

end Leanux.Proofs.WG.Index
