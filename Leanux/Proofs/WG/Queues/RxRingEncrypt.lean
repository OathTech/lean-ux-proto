import Leanux.Proofs.WG.Queues.RxRingNapi

/-! Encrypt work can invoke actual NAPI, but its own mutation sites affect
only the encrypt ring. These exact RX-cell frames have no store-validity premise. -/
set_option maxHeartbeats 2000000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Queues.RxRing
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes Std.Do

theorem encryptPacket_cell (checksum : Packet → M Packet)
    (hc : ∀ p, SameView cell (checksum p)) (key : KeypairId) (pkt : DataPacket) :
    SameView cell (encryptPacket checksum key pkt) := by
  apply SameView.of_wp
  intro s
  have hcs := fun p => (hc p).wp (fun t => t = s)
  have hp := fun len mtu => (kernel (calculateSkbPadding_sameKernel len mtu)).wp (fun t => t = s)
  have ha := fun site => (kernel (hiddenAlloc_sameKernel site)).wp (fun t => t = s)
  have hh := (kernel (skipCut_sameKernel [.flowHashSecret])).wp (fun t => t = s)
  have hk := (getKeypair_frame key).wp (fun t => t = s)
  mvcgen [encryptPacket, hcs, hp, ha, hh, hk, branch]

theorem encryptStep_cell (checksum : Packet → M Packet) (softirq : M Unit)
    (hc : ∀ p, SameView cell (checksum p)) (hs : SameView cell softirq) :
    SameView cell (encryptStep checksum softirq) := by
  apply SameView.of_wp
  intro s
  have hi := hs.wp (fun t => t = s)
  have hg := fun id => (getTxSkb_cell id).wp (fun t => t = s)
  have hu := fun id f => (setTxSkb_cell id f).wp (fun t => t = s)
  have he := fun k p => (encryptPacket_cell checksum hc k p).wp (fun t => t = s)
  have hq := fun item state => (enqueuePerPeerTx_cell item state).wp (fun t => t = s)
  have hd := fun r => (modifyDev_cell (fun d => {d with encryptQueue := r}) (fun _ => rfl) (fun _ => rfl)).wp (fun t => t = s)
  have hl (α β : Type) := list_view_spec cell (α := α) (β := β) (fun t => t = s)
  mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, hl, encryptStep,
    hi, hg, hu, he, hq, hd, getDev, getK, branch, invariant]
  all_goals try exact ((⇓? _ w => ⌜cell w = s⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [cell]

theorem encryptIter_cell (checksum : Packet → M Packet) (softirq : M Unit) (resched : M Bool)
    (hc : ∀ p, SameView cell (checksum p)) (hs : SameView cell softirq)
    (hr : SameView cell resched) : SameView cell (encryptIter checksum softirq resched) := by
  apply SameView.of_wp
  intro s
  have he := (encryptStep_cell checksum softirq hc hs).wp (fun t => t = s)
  have hh := hr.wp (fun t => t = s)
  mvcgen [encryptIter, workerIter, he, hh, branch]

theorem actualEncryptIter_cell : SameView cell
    (encryptIter Leanux.Env.checksumHelp Leanux.Env.napiSoftirq (Leanux.Env.condResched .encryptWorker)) :=
  encryptIter_cell _ _ _ (fun p => kernel (checksumHelp_sameKernel p)) napiSoftirq_cell
    (kernel (condResched_sameKernel _))

end Leanux.Proofs.WG.Queues.RxRing
