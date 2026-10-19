import Leanux.Proofs.WG.Queues.HolderDecryptHistory
import Leanux.Proofs.Framing.WGData

/-! The encrypt ring and TX byte writes preserve all receive funding and
complete holder fields. This view observes actual native state. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.HolderEncrypt
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open DurableHolders

def fields (w : WGWorld) :=
  (DecryptCarrier.decryptView w,passiveView w,sendView w,handoffTxView w)

theorem boundary_fields (hi : Boundary cs loans w) (same : fields v = fields w) :
    Boundary cs loans v := by
  obtain ⟨holders,funded,stable⟩ := hi
  have first := congrArg Prod.fst same
  have frame : Frame w v := ⟨congrArg (fun p => p.2.1) same,
    congrArg (fun p => p.2.2.1) same,fun pid batches found => by
      have tx : handoffTxView v = handoffTxView w := congrArg (fun p => p.2.2.2) same
      rw [←tx]; exact found⟩
  exact ⟨holders,⟨funded.aligned.frame frame,funded.carriers.view (congrArg Prod.fst first)⟩,
    stable.view (congrArg Prod.snd first)⟩

theorem getTx_fields (id : SkbId) : SameView fields (getTxSkb id) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a x v b run
  exact congrArg fields (Packets.getTxSkb_current id w v x a b run).1

theorem setTx_fields (id : SkbId) (f : DataPacket → DataPacket) :
    SameView fields (setTxSkb id f) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a x v b run
  cases hd : w.dev with
  | none => simp [setTxSkb,liftSkb_run,hd] at run
  | some d =>
    cases hp : d.txSkbs[id]? with
    | none =>
      simp [setTxSkb,liftSkb_run,SkbStore.setTx,SkbStore.getTx,hd,hp,invariant,AmbientM.invariant] at run
      cases run
    | some pkt =>
      rw [Packets.setTxSkb_run w a d id pkt f hd hp] at run
      cases run
      unfold fields DecryptCarrier.decryptView carrierView keyView peerView rxView
      unfold keyWords currentCells stableView RxRing.nativeCell passiveView sendView handoffTxView
      simp [Packets.update,hd,rxView]

theorem encryptRing_fields (ring : PtrRing (List SkbId)) :
    SameView fields (modifyDev fun d => {d with encryptQueue := ring}) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a x v b run
  cases run
  unfold fields DecryptCarrier.decryptView carrierView keyView peerView rxView
  unfold keyWords currentCells stableView RxRing.nativeCell passiveView sendView handoffTxView
  cases hd : w.dev <;> simp [hd,rxView]

theorem store_fields {action : WG.M α} (ha : SameWGStore action) : SameView fields action :=
  ha.of_factor (fun s : WGStoreView => fields {dev:=s.dev,nlSock7:=s.nlSock7,nlSock8:=s.nlSock8}) fields (fun _ => rfl)

theorem poll_fields : SameView fields TxRing.pollSource := by
  unfold TxRing.pollSource
  exact (store_fields getDev_sameWGStore).bind (fun d =>
    (encryptRing_fields d.encryptQueue.consume.2).bind (fun _ => SameView.pure _ _))

theorem native_boundary {action : WG.M α} (ha : SameView fields action) :
    Preserves (Boundary cs loans) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b hi run
  exact boundary_fields hi ((ProjectedAction.iff_run_ambient _ _ _).mp ha w a x v b run)

theorem lift_boundary {action : WG.M α} (ha : Preserves (Boundary cs loans) action) :
    Preserves (fun w : World => Boundary cs loans w.wg) (liftWG action) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w x v hi run
  exact (hoare_iff_run_ambient _ _ _).mp ha w.wg w.ambient x v.wg v.ambient hi
    ((pinned_const _private.Leanux.Proofs.WG.Queues.RxPollCarrier.«0».Leanux.Proofs.WG.Queues.RxCredits.native_receipt) action w v x run)


def productFields (w : World) := fields w.wg

theorem getKey_fields (kid : KeypairId) : SameView fields (getKeypair kid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a x v b run
  exact congrArg fields (KeyTimes.getKeypair_return kid w v x a b run).1

theorem encryptPacket_fields (checksum : Leanux.WG.Packet → Leanux.M Leanux.WG.Packet)
    (hc : ∀ p, SameView productFields (checksum p)) (key : KeypairId) (pkt : DataPacket) :
    SameView productFields (encryptPacket checksum key pkt) := by
  apply SameView.of_wp
  intro s
  let P := fun t => t = s
  have hcs := fun p => (hc p).wp P
  have native {α : Type} (a : WG.M α) (ha : SameView fields a) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => P (productFields w)) (fun _ w => P (productFields w)) :=
    (sameView_liftWG productFields fields a ha (fun _ _ _ h => h)).wp P
  have hp := fun len mtu => native (calculateSkbPadding len mtu)
    ((calculateSkbPadding_sameWGWorld len mtu).factor fields)
  have hk := native (getKeypair key) (getKey_fields key)
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => P (productFields w)) (fun _ w => P (productFields w)) :=
    productAmbient_spec a _ (fun _ _ h => h)
  have finish (inner : Leanux.WG.Packet) (padding : Nat) :
      Preserves (fun w => P (productFields w)) (do
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
  change Preserves (fun w => P (productFields w)) (encryptPacket checksum key pkt)
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


end Leanux.Proofs.WG.Queues.RxCredits.HolderEncrypt
