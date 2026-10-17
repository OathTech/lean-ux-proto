import Leanux.Proofs.WG.Queues.RxClearWork
import Leanux.Proofs.WG.Queues.TxDispositionEndpoints

/-! Actual TX disposal pays one explicitly supplied batch reservation. The
normal-endpoint rules keep the original partial frees and key/peer releases;
they neither infer funding from a queued flag nor require final peer survival. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.TxReservation
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

private theorem freeTx_preserves (id : SkbId) :
    Preserves (ClearWork.Inv cs loans) (freeTxSkb id) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi hr
  cases result
  cases hd : w.dev with
  | none => simp [freeTxSkb,liftSkb_run,hd] at hr
  | some d =>
    cases hp : d.txSkbs[id]? with
    | none =>
      simp [freeTxSkb,liftSkb_run,SkbStore.freeTx,SkbStore.getTx,hd,hp,
        invariant,AmbientM.invariant] at hr
      cases hr
    | some pkt =>
      rw [Packets.freeTxSkb_run w a d id pkt hd hp] at hr
      cases hr
      refine ⟨hi.1.view ?_,hi.2.view ?_⟩
      · unfold carrierView peerView rxView keyView RxCredits.keyWords RxCredits.currentCells
        simp [Packets.update,hd]
      · simp [stableView,RxRing.nativeCell,rxView,Packets.update,hd]

/-- Freeing the actual TX list preserves all supplied receive obligations.
Repeated or absent IDs may Stop at the original getter. -/
theorem freeList_preserves (item : List SkbId) :
    Preserves (ClearWork.Inv cs loans) (TxDisposition.freeList item) := by
  induction item with
  | nil => simpa only [TxDisposition.freeList_nil] using
      (preserves_pure () : Preserves (ClearWork.Inv cs loans) (pure ()))
  | cons id rest ih =>
    rw [TxDisposition.freeList_cons]
    exact preserves_bind (freeTx_preserves id) (fun _ => ih)

/-- The native disposal tail consumes exactly one named peer reservation for
the entire batch. Its saved key reference is released before that payment. -/
theorem dispose_normal (o : Owner) (item : List SkbId) (key : KeypairId)
    (hi : ClearWork.Inv cs (o :: loans) w) (a b : Ambient)
    (hr : ((TxDisposition.disposeSource o.slot item key).run w).run a =
      .ok ((result,v),b)) :
    result = true ∧ ClearWork.Inv cs loans v := by
  have factor : TxDisposition.disposeSource o.slot item key = (do
    TxDisposition.freeList item
    keypairPut (some key) false
    peerPut (some o.slot)
    pure true : WG.M Bool) := by
    simp only [TxDisposition.disposeSource,TxDisposition.freeList,bind_assoc,pure_bind]
  rw [factor] at hr
  rw [MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨u,freed,af,hfree,hr⟩ := hr
  cases u
  have hf := (hoare_iff_run_ambient _ _ _).mp (freeList_preserves item)
    w a () freed af hi hfree
  rw [MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨u,keys,ak,hkey,hr⟩ := hr
  cases u
  have hk := (hoare_iff_run_ambient _ _ _).mp
    ((pinned_const _private.Leanux.Proofs.WG.Queues.RxClearWork.«0».Leanux.Proofs.WG.Queues.RxCredits.ClearWork.key_put)
      (some key) false) freed af () keys ak hf hkey
  rw [MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨u,paid,ap,hpay,hr⟩ := hr
  cases u
  have hp := reservation_payment_stable hk.1 hk.2 ak ap hpay
  cases hr
  exact ⟨rfl,hp⟩

/-- The same actual normal run also removes every listed TX cell and sends
no datagram. No distinct-ID, key-validity or positive-refcount premise is added. -/
theorem dispose_endpoint (o : Owner) (item : List SkbId) (key : KeypairId)
    (hi : ClearWork.Inv cs (o :: loans) w) (a b : Ambient)
    (hr : ((TxDisposition.disposeSource o.slot item key).run w).run a =
      .ok ((result,v),b)) :
    result = true ∧ ClearWork.Inv cs loans v ∧
      (∀ id ∈ item, TxDisposition.txPackets v id = none) ∧ v.sent = w.sent := by
  have account := dispose_normal o item key hi a b hr
  have cells := (hoare_iff_run_ambient _ _ _).mp
    (TxDisposition.dispose_endpoint o.slot item key w.sent) w a result v b rfl hr
  exact ⟨account.1,account.2,cells.2⟩

end Leanux.Proofs.WG.Queues.RxCredits.TxReservation
