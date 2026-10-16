import Leanux.Proofs.WG.Queues.RxRingNapi
import Leanux.Proofs.Framing.WGData

/-! Encrypt work can invoke actual NAPI, but its own mutation sites affect
only the encrypt ring. These exact RX-cell frames have no store-validity premise. -/
set_option maxHeartbeats 2000000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Queues.RxRing
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes Std.Do

theorem encryptPacket_cell (checksum : Packet → Leanux.M Packet)
    (hc : ∀ p, SameView cell (checksum p)) (key : KeypairId) (pkt : DataPacket) :
    SameView cell (encryptPacket checksum key pkt) := by
  apply SameView.of_wp
  intro s
  let P := fun t => t = s
  have hcs := fun p => (hc p).wp P
  have native {α : Type} (a : WG.M α) (ha : SameView nativeCell a) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => P (cell w)) (fun _ w => P (cell w)) :=
    (sameView_liftWG cell nativeCell a ha (fun _ _ _ h => h)).wp P
  have hp := fun len mtu => native (calculateSkbPadding len mtu)
    ((calculateSkbPadding_sameWGWorld len mtu).factor nativeCell)
  have hk := native (getKeypair key) (getKeypair_frame key)
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => P (cell w)) (fun _ w => P (cell w)) :=
    productAmbient_spec a _ (fun _ _ h => h)
  unfold Hoare at hp hk ambient
  mvcgen [-Std.Do.Spec.monadLift_StateT, encryptPacket, hcs, hp, hk, ambient,
    hiddenAlloc, skipCut, branch]


theorem encryptStep_cell (checksum : Packet → Leanux.M Packet) (softirq : Leanux.M Unit)
    (hc : ∀ p, SameView cell (checksum p)) (hs : SameView cell softirq) :
    SameView cell (encryptStep checksum softirq) := by
  apply SameView.of_wp
  intro s
  let P := fun t => t = s
  have native {α : Type} (a : WG.M α) (ha : SameView nativeCell a) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => P (cell w)) (fun _ w => P (cell w)) :=
    (sameView_liftWG cell nativeCell a ha (fun _ _ _ h => h)).wp P
  have packets {α : Type} (a : SkbM α) : SameView nativeCell (liftSkb a) := by
    intro initial
    apply hoare_liftSkb
    intro g d store hg hd
    simpa [nativeCell, hd] using hg
  have skb {α : Type} (a : SkbM α) := native (liftSkb a) (packets a)
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => P (cell w)) (fun _ w => P (cell w)) :=
    productAmbient_spec a _ (fun _ _ h => h)
  have dev : SameView nativeCell getDev := by
    apply SameView.of_wp
    intro initial
    mvcgen [getDev, invariant, AmbientM.invariant]
  have hg := native getDev dev
  have hi := hs.wp P
  have he := fun k p => (encryptPacket_cell checksum hc k p).wp P
  have hq := fun item state => native (enqueuePerPeerTx item state) (enqueuePerPeerTx_cell item state)
  have hd := fun r => native (modifyDev (fun d => {d with encryptQueue := r}))
    (modifyDev_cell _ (fun _ => rfl) (fun _ => rfl))
  have hl (α β : Type) := list_view_spec (m := Except Stop) cell (α := α) (β := β) P
  unfold Hoare at skb ambient hg hq hd
  mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, -Std.Do.Spec.monadLift_StateT,
    hl, encryptStep, encryptRingPoll, hi, hg, skb, ambient, he, hq, hd, getTxSkb, setTxSkb, branch, invariant]
  all_goals try exact ((⇓? _ w => ⌜P (cell w)⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals simp_all [cell]


theorem encryptIter_cell (checksum : Packet → Leanux.M Packet) (softirq : Leanux.M Unit) (resched : Leanux.M Bool)
    (hc : ∀ p, SameView cell (checksum p)) (hs : SameView cell softirq)
    (hr : SameView cell resched) : SameView cell (encryptIter checksum softirq resched) := by
  apply SameView.of_wp
  intro s
  have he := (encryptStep_cell checksum softirq hc hs).wp (fun t => t = s)
  have hh := hr.wp (fun t => t = s)
  mvcgen [encryptIter, workerIter, he, hh, branch, AmbientM.branch]

theorem actualEncryptIter_cell : SameView cell
    (encryptIter Leanux.Env.checksumHelp Leanux.Env.napiSoftirq (Leanux.Env.condResched .encryptWorker)) :=
  encryptIter_cell _ _ _ (fun p => (checksumHelp_sameWorld p).factor cell) napiSoftirq_cell
    ((condResched_sameKernel _).of_factor
      (fun store : ProductStore43 => store.2.2.2.dev.map fun d => (d.ifindex, d.decryptQueue))
      cell (fun _ => rfl))

end Leanux.Proofs.WG.Queues.RxRing
