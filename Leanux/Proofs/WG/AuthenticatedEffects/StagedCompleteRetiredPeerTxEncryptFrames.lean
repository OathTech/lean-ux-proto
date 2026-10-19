import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerTxHistoryFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerPollHistoryFrames
import Leanux.Proofs.WG.Queues.HolderEncryptHistory

/-! The original encrypt-ring and TX publication paths retain the exact peer
balance. The temporary publication loan is acquired and repaid by that source. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes
open Queues Queues.RxCredits DurableHolders

theorem Account.encrypt_fields (account : Account holders cs loans w)
    (same : HolderEncrypt.fields v = HolderEncrypt.fields w) : Account holders cs loans v := by
  have first := congrArg Prod.fst same
  have frame : Frame w v := ⟨congrArg (fun p => p.2.1) same,
    congrArg (fun p => p.2.2.1) same,fun pid batches found => by
      have tx : handoffTxView v = handoffTxView w := congrArg (fun p => p.2.2.2) same
      rw [←tx]; exact found⟩
  exact ⟨⟨account.funded.aligned.frame frame,account.funded.carriers.view (congrArg Prod.fst first)⟩,
    account.upper.peer_view (congrArg (fun p => p.1.1) first),account.stable.view (congrArg Prod.snd first)⟩

theorem Account.tx_publication (account : Account holders cs loans w)
    (item : List SkbId) (state : PacketState) (a b : Ambient)
    (run : ((enqueuePerPeerTx item state).run w).run a = .ok (((),v),b)) :
    Account holders cs loans v := by
  obtain ⟨funded,stable⟩ := enqueuePerPeerTx_funded item state account.funded account.stable a b run
  have fields := (ProjectedAction.iff_run_ambient _ _ _).mp (publication_protect item state) w a () v b run
  exact ⟨funded,account.upper.peer_view (congrArg Prod.fst fields),stable⟩

namespace Encrypt
open HolderEncrypt (fields productFields getTx_fields setTx_fields poll_fields encryptPacket_fields)

theorem native_boundary {action : WG.M α} (ha : SameView fields action) :
    Preserves (ExactBoundary cs loans) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b hi run
  obtain ⟨holders,account⟩ := hi
  exact ⟨holders,account.encrypt_fields ((ProjectedAction.iff_run_ambient _ _ _).mp ha w a x v b run)⟩

theorem lift_boundary {action : WG.M α} (ha : Preserves (ExactBoundary cs loans) action) :
    Preserves (fun w : World => ExactBoundary cs loans w.wg) (liftWG action) :=
  ExactBoundary.lift action ha

theorem publication (item : List SkbId) (state : PacketState) :
    Preserves (ExactBoundary cs loans) (enqueuePerPeerTx item state) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b hi run
  cases x
  obtain ⟨holders,account⟩ := hi
  exact ⟨holders,account.tx_publication item state a b run⟩

theorem product_boundary {action : Leanux.M α} (ha : SameView productFields action) :
    Preserves (fun w : World => ExactBoundary cs loans w.wg) action := by
  apply (hoare_iff_run _ _ _).mpr
  intro w x v hi run
  exact (by
    obtain ⟨holders,account⟩ := hi
    exact ⟨holders,account.encrypt_fields ((ProjectedAction.iff_run _ _ _).mp ha w x v run)⟩)

theorem product_store_boundary {action : Leanux.M α} (ha : SameProductStore action) :
    Preserves (fun w : World => ExactBoundary cs loans w.wg) action :=
  ExactBoundary.product_frame action ha

theorem packet_boundary (kid : KeypairId) (pkt : DataPacket) :
    Preserves (fun w : World => ExactBoundary cs loans w.wg) (encryptPacket Env.checksumHelp kid pkt) :=
  product_boundary (encryptPacket_fields Env.checksumHelp
    (fun p => (checksumHelp_sameWorld p).factor productFields) kid pkt)

theorem step_tail_boundary (item : Option (List SkbId)) :
    Preserves (fun w : World => ExactBoundary cs loans w.wg) (RxWorkers.encryptStepTailSource item) := by
  let P := fun w : World => ExactBoundary cs loans w.wg
  have ambient {α : Type} (a : AmbientM α) : Preserves P (liftAmbient a) :=
    productAmbient_spec a _ (fun _ _ hi => hi)
  have getter := fun id => lift_boundary (cs := cs) (loans := loans) (native_boundary (getTx_fields id))
  have setter := fun id f => lift_boundary (cs := cs) (loans := loans) (native_boundary (setTx_fields id f))
  have publish := fun item state => lift_boundary (cs := cs) (loans := loans) (publication item state)
  change Preserves P _
  unfold RxWorkers.encryptStepTailSource
  apply preserves_bind (ambient (AmbientM.branch .encWorkerConsumed item.isSome))
  intro _
  cases item with
  | none => exact preserves_pure _
  | some first =>
    dsimp only
    cases hh : first.head? with
    | none => exact ambient (AmbientM.invariant _)
    | some headId =>
      dsimp only
      apply preserves_bind (getter headId)
      intro head
      apply preserves_bind
      · apply list_view_spec id P
        intro id state
        apply preserves_bind (ambient (AmbientM.branch .encWorkerSkbIterate true))
        intro _
        apply preserves_bind (getter id)
        intro packet
        apply preserves_bind (packet_boundary head.keypair packet)
        intro encrypted
        apply preserves_bind (ambient (AmbientM.branch .encWorkerEncrypted encrypted.isSome))
        intro success
        split
        · exact preserves_bind (setter id _) (fun _ => preserves_pure _)
        · exact preserves_pure _
      · intro state
        split
        · exact preserves_bind (ambient (AmbientM.branch .encWorkerSkbIterate false))
            (fun _ => preserves_bind (publish first state) (fun _ => preserves_pure _))
        · exact preserves_bind (publish first state) (fun _ => preserves_pure _)


theorem tail_boundary (item : Option (List SkbId)) :
    Preserves (fun w : World => ExactBoundary cs loans w.wg) (RxWorkers.encryptTailSource item) := by
  unfold RxWorkers.encryptTailSource workerIter
  apply preserves_bind (step_tail_boundary item)
  intro more
  split
  · exact preserves_pure _
  · apply preserves_bind
    · apply preserves_bind (product_store_boundary (condResched_sameKernel .encryptWorker))
      intro need
      exact productAmbient_spec (AmbientM.branch .encWorkerNeedResched need) _ (fun _ _ hi => hi)
    · intro yielded
      split <;> exact preserves_pure _


end Encrypt
end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
