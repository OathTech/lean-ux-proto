import Leanux.Proofs.WG.RetirementSecurity.HolderBulkRemoval
import Leanux.Proofs.WG.Queues.HolderDeviceStop

/-! Device shutdown preserves both exact ledgers. These local frames erase
only unrelated fields; actual slot clearing and work payments remain separate
source actions with their own reference equations. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HolderShutdown
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits
open DurableHolders

theorem fields (before : HolderDrain.Ready original carriers loans temporary w)
    (same : HolderEncrypt.fields v = HolderEncrypt.fields w)
    (points : ownershipPointView v = ownershipPointView w) :
    HolderDrain.Ready original carriers loans temporary v := by
  obtain ⟨holders,remainder,funded,stable⟩ := before.1
  have first := congrArg Prod.fst same
  have frame : Frame w v := ⟨congrArg (fun p => p.2.1) same,
    congrArg (fun p => p.2.2.1) same,fun pid batches found => by
      have tx : handoffTxView v = handoffTxView w := congrArg (fun p => p.2.2.2) same
      rw [←tx]; exact found⟩
  exact ⟨⟨holders,remainder,⟨funded.aligned.frame frame,
      funded.carriers.view (congrArg Prod.fst first)⟩,stable.view (congrArg Prod.snd first)⟩,
    before.2.1.points points,
    before.2.2.transport (congrArg (fun x => x.1.1) first) points (List.Perm.refl _)⟩

theorem frame {action : WG.M α} (same : SameView HolderEncrypt.fields action)
    (points : SameView ownershipPointView action) :
    Preserves (HolderDrain.Ready original carriers loans temporary) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact fields before ((ProjectedAction.iff_run_ambient _ _ _).mp same w a result v b run)
    ((ProjectedAction.iff_run_ambient _ _ _).mp points w a result v b run)

theorem read : Preserves (HolderDrain.Ready original carriers loans temporary) getDev :=
  frame (HolderEncrypt.store_fields getDev_sameWGStore) (ownershipPoints_kernel _ getDev_sameWGStore)

theorem modify (f : Device → Device)
    (same : ∀ w : WGWorld, HolderEncrypt.fields {w with dev:=w.dev.map f}=HolderEncrypt.fields w)
    (points : ∀ w : WGWorld, ownershipPointView {w with dev:=w.dev.map f}=ownershipPointView w) :
    Preserves (HolderDrain.Ready original carriers loans temporary) (modifyDev f) := by
  apply hoare_modify
  intro w before
  exact fields before (same w) (points w)

theorem handshake (pid : PeerId) :
    Preserves (HolderDrain.Ready original carriers loans temporary) (handshakeClear pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp
      ((pinned_const _private.Leanux.Proofs.WG.Queues.HolderDrains.«0».Leanux.Proofs.WG.Queues.RxCredits.DurableHolders.during_frame)
        _ (HolderWorkFrames.handshakeClear_frame pid) (fun _ _ => ClearWork.handshakeClear_preserves pid))
      w a result v b before.1 run,
    before.2.1.points ((ProjectedAction.iff_run_ambient _ _ _).mp
      (ClearedSlots.handshake_clear_points pid) w a result v b run),
    (hoare_iff_run_ambient _ _ _).mp (SlotAnchors.handshake_clear pid)
      w a result v b before.2.2 run⟩

theorem update (pid : PeerId) (f : Peer → Peer)
    (stamp : ∀p,(f p).internalId=p.internalId) (count : ∀p,(f p).refcount=p.refcount)
    (rx : ∀p,(f p).rxQueue=p.rxQueue) (napi : ∀p,(f p).napiScheduled=p.napiScheduled)
    (current : ∀p kid,(f p).keypairCurrent=some kid → p.keypairCurrent=some kid)
    (tx : ∀p,(f p).txQueue.all=p.txQueue.all)
    (owned : ∀p,peerOwnership (f p)=peerOwnership p) :
    Preserves (HolderDrain.Ready original carriers loans temporary)
      (getPeer pid >>= fun p => setPeer pid (f p)) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  obtain ⟨holders,remainder,funded,stable⟩ := before.1
  have kept := (hoare_iff_run_ambient _ _ _).mp
    ((pinned_const _private.Leanux.Proofs.WG.Queues.HolderTimers.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderTimers.modify_peer)
      pid f stamp count rx napi current tx) w a result v b ⟨funded,stable⟩ run
  have pointFrame : SameView ownershipPointView (getPeer pid >>= fun p => setPeer pid (f p)) := by
    intro initial
    apply hoare_bind _ _ (ownership_getPeer (· = initial) pid)
    intro p
    apply hoare_consequence (ownership_setPeer (· = initial) pid (f p))
    · intro state entry
      exact ⟨entry.1,by simpa only [owned] using entry.2⟩
    · exact fun _ _ h => h
  have points := (ProjectedAction.iff_run_ambient _ _ _).mp pointFrame w a result v b run
  exact ⟨⟨holders,remainder,kept⟩,before.2.1.points points,
    before.2.2.transport ((ProjectedAction.iff_run_ambient _ _ _).mp
      (HolderConsume.peers_update pid f stamp count rx) w a result v b run) points (List.Perm.refl _)⟩

theorem reset (pid : PeerId) :
    Preserves (HolderDrain.Ready original carriers loans temporary) (resetLastSentHandshake pid) := by
  unfold resetLastSentHandshake
  apply preserves_bind (hoare_liftAmbient (AmbientM.hiddenClock64 .resetLastSent) _)
  intro now
  exact update pid (fun p => {p with lastSentHandshake := now-(REKEY_TIMEOUT+1 : Nat).toInt64*NSEC_PER_SEC64})
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ _ h => h)
    (fun _ => rfl) (fun _ => rfl)

end Leanux.Proofs.WG.RetirementSecurity.HolderShutdown
