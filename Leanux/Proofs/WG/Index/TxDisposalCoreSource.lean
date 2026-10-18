import Leanux.Proofs.WG.Index.CryptCoreFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.CryptCore
open Leanux Leanux.WG Noise Queues Queues.RxCredits
open Queues.RxCredits.DurableHolders Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

theorem key_release_core (key : Option KeypairId) (now : Bool) :
    Preserves Reached.Core (keypairPut key now) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b pre run
  have tables := (ensures_iff _ _ _).mpr (keypairPut_tables key now)
    w a result v b (fun d hd => (pre d hd).1) run
  have covered := keypairPut_hashSlots key now
    w a result v b (fun d hd => (pre d hd).2.1) run
  have coherent := keypairPut_owner_coherent key now
    w a result v b (fun d hd => (pre d hd).2.2.1) run
  have reserved := keypairPut_retirement [] key now
    w a result v b (fun d hd => (pre d hd).2.2.2) run
  exact fun d hd => ⟨tables d hd,covered d hd,coherent d hd,reserved d hd⟩

theorem key_release_boundary (cs : Ledger) (loans : Reservations)
    (key : Option KeypairId) (now : Bool) :
    Preserves (fun w => DeviceBoundary.Entry cs loans w ∧ Reached.Core w)
      (keypairPut key now) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b pre run
  obtain ⟨holders,funded,stable⟩ := pre.1.1
  have kept := (hoare_iff_run_ambient _ _ _).mp
    ((pinned_const _private.Leanux.Proofs.WG.Queues.RxClearWork.«0».Leanux.Proofs.WG.Queues.RxCredits.ClearWork.key_put)
      key now) w a result v b ⟨funded.carriers,stable⟩ run
  have frame := (hoare_iff_run_ambient _ _ _).mp
    (HolderWorkFrames.keypairPut_frame key now w) w a result v b (Frame.refl w) run
  have base := BaseCoherence.transport pre.1.2.1
    ((ProjectedAction.iff_run_ambient _ _ _).mp
      ((pinned_const _private.Leanux.Proofs.WG.Queues.BaseCoherenceConfiguration.«0».Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence.keyPut_view)
        key now) w a result v b run)
  have configured := (hoare_iff_run_ambient _ _ _).mp
    (ConfiguredRemoval.frame (ConfiguredIdentity.keypairPut_view key now))
      w a result v b pre.1.2.2 run
  exact ⟨⟨⟨holders,⟨funded.aligned.frame frame,kept.1⟩,kept.2⟩,base,configured⟩,
    (hoare_iff_run_ambient _ _ _).mp (key_release_core key now) w a result v b pre.2 run⟩

theorem freeList_boundary (cs : Ledger) (loans : Reservations) (item : List SkbId) :
    Preserves (fun w => DeviceBoundary.Entry cs loans w ∧ Reached.Core w)
      (TxDisposition.freeList item) := by
  have free (id : SkbId) :
      Preserves (fun w => DeviceBoundary.Entry cs loans w ∧ Reached.Core w) (freeTxSkb id) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b pre run
    have kept := (hoare_iff_run_ambient _ _ _).mp
      ((pinned_const _private.Leanux.Proofs.WG.Queues.TxReservation.«0».Leanux.Proofs.WG.Queues.RxCredits.TxReservation.freeTx_preserves) id)
        w a result v b
        ⟨pre.1.1.choose_spec.1.carriers,pre.1.1.choose_spec.2⟩ run
    have holderFrame : Preserves (Frame w) (freeTxSkb id) := by
      apply hoare_liftSkb
      intro current d store initial device
      refine ⟨?_,?_,?_⟩
      · simpa only [passiveView,device,Option.map_some] using initial.1
      · simpa only [sendView,device,Option.map_some] using initial.2
      · intro q items found
        apply initial.3 q items
        simpa only [handoffTxView,device,Option.bind_some] using found
    have frame := (hoare_iff_run_ambient _ _ _).mp holderFrame
      w a result v b (Frame.refl w) run
    have baseFrame := (pinned_const _private.Leanux.Proofs.WG.Queues.BaseCoherenceConfiguration.«0».Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence.skb_frame)
      (SkbStore.freeTx id)
    have base := BaseCoherence.transport pre.1.2.1
      ((ProjectedAction.iff_run_ambient _ _ _).mp baseFrame w a result v b run)
    have configured := (hoare_iff_run_ambient _ _ _).mp
      ((pinned_const _private.Leanux.Proofs.WG.Origins.ConfiguredTraffic.«0».Leanux.Proofs.WG.ConfiguredTraffic.skb) (SkbStore.freeTx id))
        w a result v b pre.1.2.2 run
    exact ⟨⟨⟨pre.1.1.choose,⟨pre.1.1.choose_spec.1.aligned.frame frame,kept.1⟩,
      kept.2⟩,base,configured⟩,
      (hoare_iff_run_ambient _ _ _).mp (skb (SkbStore.freeTx id)) w a result v b pre.2 run⟩
  unfold TxDisposition.freeList
  apply preserves_bind
  · apply list_view_spec id (fun w => DeviceBoundary.Entry cs loans w ∧ Reached.Core w)
    intro id ignored
    exact preserves_bind (free id) (fun _ => preserves_pure _)
  · intro _
    exact preserves_pure ()

theorem dispose_boundary (cs : Ledger) (paid : Owner) (loans : Reservations)
    (item : List SkbId) (key : KeypairId) :
    Hoare (TxDisposition.disposeSource paid.slot item key)
      (fun w => DeviceBoundary.Entry cs (paid::loans) w ∧ Reached.Core w)
      (fun _ w => DeviceBoundary.Entry cs loans w ∧ Reached.Core w) := by
  have factor : TxDisposition.disposeSource paid.slot item key = (do
      TxDisposition.freeList item
      keypairPut (some key) false
      peerPut (some paid.slot)
      pure true : WG.M Bool) := by
    simp only [TxDisposition.disposeSource,TxDisposition.freeList,bind_assoc,pure_bind]
  rw [factor]
  apply hoare_bind _ _ (freeList_boundary cs (paid::loans) item)
  intro _
  apply hoare_bind _ _ (key_release_boundary cs (paid::loans) (some key) false)
  intro _
  apply hoare_bind _ _ ((ensures_iff _ _ _).mp (Reached.peerPut_boundary_core cs paid loans))
  intro _
  exact preserves_pure true

end Leanux.Proofs.WG.Index.CryptCore
