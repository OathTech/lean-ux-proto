import Leanux.Proofs.WG.Queues.TxRingCuts
import Leanux.Proofs.WG.RetirementSecurity.HandshakeQueueNapi
import Leanux.Proofs.WG.Queues.RxRingEncrypt

/-! Actual encryption and decryption callbacks retain the handshake ring.
Their packet-store and crypt-ring updates cannot manufacture handshake inputs. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HandshakeLengths
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Std.Do

theorem encryptPacket_cell (checksum : Packet → Leanux.M Packet)
    (hc : ∀ p, SameView productView (checksum p)) (key : KeypairId) (pkt : DataPacket) :
    SameView productView (encryptPacket checksum key pkt) := by
  apply SameView.of_wp
  intro s
  let P := fun t => t = s
  have hcs := fun p => (hc p).wp P
  have native {α : Type} (a : WG.M α) (ha : SameView view a) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => P (productView w)) (fun _ w => P (productView w)) :=
    (sameView_liftWG productView view a ha (fun _ _ _ h => h)).wp P
  have hp := fun len mtu => native (calculateSkbPadding len mtu)
    ((calculateSkbPadding_sameWGWorld len mtu).factor view)
  have hk := native (getKeypair key) (getKeypair_frame key)
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => P (productView w)) (fun _ w => P (productView w)) :=
    productAmbient_spec a _ (fun _ _ h => h)
  have finish (inner : Packet) (padding : Nat) :
      Preserves (fun w => P (productView w)) (do
        let cowOk ← (hiddenAlloc .skbCowDataTx : Leanux.M Bool)
        if ← branch .encCowDataFailed !cowOk then return none
        if ← branch .encTooManyFrags false then return none
        let k ← getKeypair key
        if ← branch .encSgvecFailed false then return none
        return some (dataMessage k.remoteIndex pkt.nonce k.sending.key
          (inner.bytes ++ List.replicate padding 0))) := by
    apply preserves_bind (ambient _)
    intro cow
    apply preserves_bind (ambient _)
    intro cowFailed
    split
    · exact preserves_pure _
    · apply preserves_bind (ambient _)
      intro fragments
      split
      · exact preserves_pure _
      · apply preserves_bind hk
        intro material
        apply preserves_bind (ambient _)
        intro scatterFailed
        split <;> exact preserves_pure _
  change Preserves (fun w => P (productView w)) (encryptPacket checksum key pkt)
  simp only [encryptPacket, hiddenAlloc, skipCut, branch]
  apply preserves_bind (ambient _)
  intro _
  apply preserves_bind (hp _ _)
  intro padding
  apply preserves_bind (ambient _)
  intro allocated
  apply preserves_bind (ambient _)
  intro failed
  split
  · exact preserves_pure _
  · apply preserves_bind (ambient _)
    intro checksumPartial
    split
    · apply preserves_bind (ambient _)
      intro checksumAllocated
      apply preserves_bind (ambient _)
      intro checksumFailed
      split
      · exact preserves_pure _
      · exact preserves_bind (hcs _) (fun inner => finish inner padding)
    · exact finish pkt.plaintext padding


theorem encryptStep_cell (checksum : Packet → Leanux.M Packet) (softirq : Leanux.M Unit)
    (hc : ∀ p, SameView productView (checksum p)) (hs : SameView productView softirq) :
    SameView productView (encryptStep checksum softirq) := by
  apply SameView.of_wp
  intro s
  let P := fun t => t = s
  have native {α : Type} (a : WG.M α) (ha : SameView view a) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => P (productView w)) (fun _ w => P (productView w)) :=
    (sameView_liftWG productView view a ha (fun _ _ _ h => h)).wp P
  have packets {α : Type} (a : SkbM α) : SameView view (liftSkb a) := by
    intro initial
    apply hoare_liftSkb
    intro g d store hg hd
    simpa [view, hd] using hg
  have skb {α : Type} (a : SkbM α) := native (liftSkb a) (packets a)
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => P (productView w)) (fun _ w => P (productView w)) :=
    productAmbient_spec a _ (fun _ _ h => h)
  have dev : SameView view getDev := kernel (project := id) getDev_sameWGStore
  have hg := native getDev dev
  have hi := hs.wp P
  have he := fun k p => (encryptPacket_cell checksum hc k p).wp P
  have hq := fun item state => native (enqueuePerPeerTx item state) (enqueuePerPeerTx_cell item state)
  have hd := fun r => native (modifyDev (fun d => {d with encryptQueue := r}))
    (modifyDev_cell _ (fun _ => rfl))
  have hl (α β : Type) := list_view_spec (m := Except Stop) productView (α := α) (β := β) P
  have poll : Preserves (fun w => P (productView w)) (encryptRingPoll softirq) := by
    unfold encryptRingPoll
    apply preserves_bind hg
    intro d
    rcases d.encryptQueue.consume with ⟨item, ring⟩
    exact preserves_bind (hd ring) (fun _ => preserves_bind hi (fun _ =>
      preserves_bind (ambient (AmbientM.branch .encWorkerConsumed item.isSome))
        (fun _ => preserves_pure item)))
  change Preserves (fun w => P (productView w)) (encryptStep checksum softirq)
  unfold encryptStep
  apply preserves_bind poll
  intro item
  ·
    cases item with
    | none => exact preserves_pure _
    | some first =>
      dsimp only
      cases hh : first.head? with
      | none => exact ambient (AmbientM.invariant _)
      | some headId =>
        dsimp only
        apply preserves_bind (skb (SkbStore.getTx headId))
        intro head
        refine preserves_bind (hl _ _ _ _ _ ?_) ?_
        · intro id state
          apply preserves_bind (ambient (AmbientM.branch .encWorkerSkbIterate true))
          intro _
          apply preserves_bind (skb (SkbStore.getTx id))
          intro packet
          apply preserves_bind (he head.keypair packet)
          intro encrypted
          apply preserves_bind (ambient (AmbientM.branch .encWorkerEncrypted encrypted.isSome))
          intro success
          split
          · exact preserves_bind (skb (SkbStore.setTx id _)) (fun _ => preserves_pure _)
          · exact preserves_pure _
        · intro state
          split
          · exact preserves_bind (ambient (AmbientM.branch .encWorkerSkbIterate false))
              (fun _ => preserves_bind (hq first state) (fun _ => preserves_pure _))
          · exact preserves_bind (hq first state) (fun _ => preserves_pure _)


theorem encryptIter_cell (checksum : Packet → Leanux.M Packet) (softirq : Leanux.M Unit) (resched : Leanux.M Bool)
    (hc : ∀ p, SameView productView (checksum p)) (hs : SameView productView softirq)
    (hr : SameView productView resched) : SameView productView (encryptIter checksum softirq resched) := by
  apply SameView.of_wp
  intro s
  have he := (encryptStep_cell checksum softirq hc hs).wp (fun t => t = s)
  have hh := hr.wp (fun t => t = s)
  change Preserves (fun w => productView w = s) (encryptIter checksum softirq resched)
  unfold encryptIter workerIter
  apply preserves_bind he
  intro worked
  split
  · exact preserves_pure _
  · apply preserves_bind
      (preserves_bind hh (fun b =>
        productAmbient_spec (AmbientM.branch .encWorkerNeedResched b)
          (fun w => productView w = s) (fun _ _ h => h)))
    intro
    exact preserves_pure _

theorem actualEncryptIter_cell : SameView productView
    (encryptIter Leanux.Env.checksumHelp Leanux.Env.napiSoftirq (Leanux.Env.condResched .encryptWorker)) :=
  encryptIter_cell _ _ _ (fun p => (checksumHelp_sameWorld p).factor productView) napiSoftirq_cell
    ((condResched_sameKernel _).of_factor
      (fun store : ProductStore43 => store.2.2.2.dev.map fun d => d.handshakeQueue)
      productView (fun _ => rfl))

theorem decryptStep_cell (softirq irq : Leanux.M Unit)
    (hs : SameView productView softirq) (hi : SameView productView irq) :
    SameView productView (decryptStep softirq irq) := by
  handshake_poll_source [decryptStep,enqueuePerPeerRx] using [hs,hi]
    with [decryptPacket_frame,peerGet_frame,peerPut_frame]

theorem decryptIter_cell (softirq irq : Leanux.M Unit) (resched : Leanux.M Bool)
    (hs : SameView productView softirq) (hi : SameView productView irq)
    (hr : SameView productView resched) : SameView productView (decryptIter softirq irq resched) := by
  have step := decryptStep_cell softirq irq hs hi
  handshake_poll_source [decryptIter,workerIter] using [step,hr] with []

theorem encryptPoll_cell : SameView view TxRing.pollSource := by
  handshake_cell_source [TxRing.pollSource] using []

end Leanux.Proofs.WG.RetirementSecurity.HandshakeLengths
