import Leanux.Proofs.WG.RetirementSecurity.HolderEncryptKeys

/-! All actual scheduler atoms retain the joint account. Ambient trials keep
the copied-state semantics of the original scheduler; the sole native queue
edit changes work selection, never a key-holder occurrence. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HolderScheduled
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues Queues.RxCredits

def Extra (temporary : Credits.Ledger) (locals : List TxLocalBatch) (active : List (List SkbId)) (w : World) :=
  HolderAccount temporary w.wg ∧ OccurrenceStack.Ready locals active w.wg ∧
    BaseCoherence.Inv w.wg ∧ KeySlotLiveness.Inv w.wg

theorem extra_store (entry : Extra temporary locals active w)
    (same : productStoreView v=productStoreView w) : Extra temporary locals active v := by
  have fields := congrArg (fun s:ProductStore43=>s.2.2.2) same
  have device : v.wg.dev=w.wg.dev := congrArg WGStoreView.dev fields
  refine ⟨HolderPoll.keys_store entry.1 fields,OccurrenceStack.ready_store fields entry.2.1,?_,?_⟩
  · exact BaseCoherence.transport entry.2.2.1 (by simp only [BaseCoherence.view,BaseCoherence.slots,BaseCoherence.rows,device])
  · apply KeySlotLiveness.transport entry.2.2.2
    funext pid
    simp only [KeySlotLiveness.view,peerAt,device]

theorem store (entry : Inv initial loans before temporary locals active h w)
    (same : productStoreView v=productStoreView w) : Inv initial loans before temporary locals active h v :=
  ⟨HolderAuxiliary.store entry.1 same,extra_store entry.2 same⟩

theorem extra_product {action : Leanux.M α} (same : SameProductStore action) :
    Preserves (Extra temporary locals active) action := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v entry run
  exact extra_store entry ((ProjectedAction.iff_run _ _ _).mp same w result v run)

theorem join_native {action : RxHistory.Obs α} {native : Leanux.M α}
    (old : PrefixPreserves (HolderAuxiliary.Inv initial loans before) OwnerChecks.Safe action)
    (erases : ErasesPrefix action native) (extra : Preserves (Extra temporary locals active) native) :
    PrefixPreserves (Inv initial loans before temporary locals active) OwnerChecks.Safe action := by
  intro w h entry
  obtain ⟨suffix,history,safe,post⟩ := old w h entry.1
  refine ⟨suffix,history,safe,?_⟩
  cases run:(runPrefix action w h).1 with
  | error e=>trivial
  | ok out=>
    rw [run] at post
    exact ⟨post,(hoare_iff_run _ _ _).mp extra w out.1 out.2 entry.2 ((erases w h).symm.trans run)⟩

theorem work_queue (f : List PeerId→List PeerId) : Preserves (Extra temporary locals active)
    (liftWG (modifyDev fun d=>{d with txWorkQueue:=f d.txWorkQueue})) := by
  apply PublicationPoll.native_product
    (fun w=>HolderAccount temporary w ∧ OccurrenceStack.Ready locals active w ∧ BaseCoherence.Inv w ∧ KeySlotLiveness.Inv w)
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b entry run
  have points := (ProjectedAction.iff_run_ambient _ _ _).mp
    (ownership_modifyDev (fun d=>{d with txWorkQueue:=f d.txWorkQueue})
      (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl)) w a result v b run
  refine ⟨entry.1.points points,
    (hoare_iff_run_ambient _ _ _).mp (OccurrenceScheduler.work_queue f) w a result v b entry.2.1 run,?_,
    (hoare_iff_run_ambient _ _ _).mp (KeySlotScheduler.work_queue f) w a result v b entry.2.2.2 run⟩
  cases run
  apply BaseCoherence.transport entry.2.2.1
  simp only [BaseCoherence.view,BaseCoherence.slots,BaseCoherence.rows,Option.map_map,Function.comp_def]

theorem atoms : RxHistory.SchedulerSource.AtomContracts
    (Inv initial loans before temporary locals active) OwnerChecks.Safe (fun {_} g=>g) := by
  have old := HolderAuxScheduler.atoms initial loans before
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro α action
    exact join_native (old.ambient action) (RxHistory.mixed_erases (erasesPrefix_lift _))
      (extra_product (fun _=>productAmbient_spec action _ (fun _ _ hi=>hi)))
  · intro α stop
    exact join_native (old.stopped stop) (RxHistory.mixed_erases (erasesPrefix_throw stop))
      (extra_product (fun _=>hoare_throw stop))
  · intro pid
    apply join_native (old.peer pid) (RxHistory.mixed_erases (liftWGObserver_erases (getPeerMixed_erases pid)))
    apply extra_product
    apply liftWG_sameProductStore
    apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w a p v b run
    exact congrArg wgStoreView (getPeer_normal pid w v p a b run).1
  · intro skb
    apply join_native (old.packet skb) (RxHistory.mixed_erases (liftWGObserver_erases (getTxSkbPrefix_erases skb)))
    apply extra_product
    apply liftWG_sameProductStore
    apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w a p v b run
    exact congrArg wgStoreView (Packets.getTxSkb_current skb w v p a b run).1
  · intro f
    exact join_native (old.work f) (RxHistory.mixed_erases (liftWGObserver_erases (erasesStatePrefix_lift _))) (work_queue f)
  · intro activation
    exact join_native (old.occupancy activation) (RxHistory.mixed_erases (activationOccupancyPrefix_erases activation))
      (extra_product (activationOccupancy_sameKernel activation))
  · exact join_native old.refills (RxHistory.mixed_erases activationRefillsPrefix_erases)
      (extra_product activationRefills_sameKernel)
  · intro next
    exact join_native (old.pending next) (RxHistory.mixed_erases (pendingNapiPrefix_erases next))
      (extra_product (SourceScheduler.pendingNapi_kernel next))
  · intro activation
    exact join_native (old.hasWork activation) (RxHistory.mixed_erases (activationHasWorkPrefix_erases activation))
      (extra_product (activationHasWork_sameKernel activation))
  · apply join_native old.trial (RxHistory.audit_erases consistentFilterAudit_erases)
    apply extra_product
    exact (show SameProductStore getAmbient from fun _=>
      productAmbient_spec (get:AmbientM Ambient) _ (fun _ _ hi=>hi)).bind
      (fun w=>filterM_sameKernel productStoreView _ activationConsistent_sameKernel w.suspended)

end Leanux.Proofs.WG.RetirementSecurity.HolderScheduled
