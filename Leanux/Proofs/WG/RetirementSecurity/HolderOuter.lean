import Leanux.Proofs.WG.RetirementSecurity.HolderScheduledTimers
import Leanux.Proofs.WG.Queues.HolderEntryDeferred

/-! Outer source cuts join the existing initialized peer ledger with exact
key credit and physical TX occurrences. Present-device scheduler entries and
the absent-device branch are derived separately from the actual same run. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HolderOuter
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues Queues.RxCredits
open DurableHolders

def Inv (carriers : Ledger) (loans : Reservations) (temporary : Credits.Ledger)
    (locals : List TxLocalBatch) (active : List (List SkbId)) (h : List RxHistory.Event) (w : World) : Prop :=
  HolderEntry.Inv carriers loans h w ∧ HolderScheduled.Extra temporary locals active w

theorem initial (net bare : Bool) (w : World)
    (same : wgStoreView w.wg=wgStoreView (Runner.initialWG net bare)) : Inv [] [] [] [] [] [] w := by
  have owner := HolderEntry.initialized net bare w same
  exact ⟨owner,HolderPoll.keys_store (initial_holder_account net bare) same,
    OccurrenceStack.ready_store same (OccurrenceLifecycle.initial net bare),
    owner.1.1.2.1,KeySlotLiveness.store_transport same (KeySlotLiveness.initial net bare)⟩

theorem store (entry : Inv carriers loans temporary locals active h w)
    (same : productStoreView v=productStoreView w) : Inv carriers loans temporary locals active h v :=
  ⟨HolderEntry.store entry.1 same,HolderScheduled.extra_store entry.2 same⟩

theorem to_scheduled (entry : Inv carriers loans temporary locals active h w)
    (present : w.wg.dev.isSome=true) :
    HolderScheduled.Inv carriers loans h temporary locals active h w :=
  ⟨HolderEntry.to_aux entry.1 present,entry.2⟩

theorem of_scheduled (entry : HolderScheduled.Inv carriers loans before temporary locals active h w) :
    ∃suffix,h=before++suffix ∧ Inv (remaining carriers (NapiCarrier.removedPackets suffix)) loans temporary locals active h w := by
  obtain ⟨suffix,history,owner⟩ := HolderEntry.of_aux entry.1 entry.2.2.2.1
  exact ⟨suffix,history,owner,entry.2⟩

private abbrev Absent :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.HolderEntryDeferred.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderEntryDeferred.Absent)

theorem deferred_normal {action : RxHistory.Obs α}
    (present : ∀initial loans before,PrefixPreserves
      (HolderScheduled.Inv initial loans before temporary locals active) OwnerChecks.Safe action)
    (absent : ∀initial before,PrefixPreserves (Absent initial before) (fun _=>True) action)
    (entry : Inv carriers loans temporary locals active h w)
    (run : runPrefix action w h=(.ok (result,v),k)) :
    ∃suffix,k=h++suffix ∧ Inv (remaining carriers (NapiCarrier.removedPackets suffix)) loans temporary locals active k v := by
  cases device:w.wg.dev with
  | some d=>
    have post := (present carriers loans h w h (to_scheduled entry (by simp only [device,Option.isSome_some]))).choose_spec.2.2
    rw [run] at post
    exact of_scheduled post
  | none=>
    have post := (absent (productStoreView w) h w h ⟨rfl,device,rfl⟩).choose_spec.2.2
    rw [run] at post
    have history : k=h := post.2.2
    have kept := store entry post.1
    have empty : remaining carriers (NapiCarrier.removedPackets [])=carriers :=
      List.filter_eq_self.mpr (fun _ _=>rfl)
    refine ⟨[],by simpa only [List.append_nil] using history,?_⟩
    simpa only [empty,history] using kept

theorem send_normal (entry : Inv carriers loans temporary locals active h w)
    (run : runPrefix RxHistory.runSendWorkers w h=(.ok (result,v),k)) :
    ∃suffix,k=h++suffix ∧ Inv (remaining carriers (NapiCarrier.removedPackets suffix)) loans temporary locals active k v :=
  deferred_normal (fun _ _ _=>HolderScheduled.send_all)
    (fun _ _=>(pinned_const _private.Leanux.Proofs.WG.Queues.HolderEntryDeferred.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderEntryDeferred.absent_send)) entry run

theorem idle_normal (entry : Inv carriers loans temporary locals active h w)
    (run : runPrefix RxHistory.idleTimers w h=(.ok (result,v),k)) :
    ∃suffix,k=h++suffix ∧ Inv (remaining carriers (NapiCarrier.removedPackets suffix)) loans temporary locals active k v :=
  deferred_normal HolderScheduled.idleTimers
    (fun _ _=>(pinned_const _private.Leanux.Proofs.WG.Queues.HolderEntryDeferred.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderEntryDeferred.absent_idle)) entry run

theorem after_xmit_normal (entry : Inv carriers loans temporary locals active h w)
    (run : runPrefix RxHistory.afterXmit w h=(.ok (result,v),k)) :
    ∃suffix,k=h++suffix ∧ Inv (remaining carriers (NapiCarrier.removedPackets suffix)) loans temporary locals active k v :=
  deferred_normal (fun _ _ _=>HolderScheduled.after_xmit)
    (fun _ _=>(pinned_const _private.Leanux.Proofs.WG.Queues.HolderEntryDeferred.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderEntryDeferred.absent_xmit)) entry run

theorem after_advance_normal (entry : Inv carriers loans temporary locals active h w)
    (run : runPrefix RxHistory.afterAdvance w h=(.ok (result,v),k)) :
    ∃suffix,k=h++suffix ∧ Inv (remaining carriers (NapiCarrier.removedPackets suffix)) loans temporary locals active k v :=
  deferred_normal HolderScheduled.afterAdvance
    (fun _ _=>(pinned_const _private.Leanux.Proofs.WG.Queues.HolderEntryDeferred.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderEntryDeferred.absent_afterAdvance)) entry run

end Leanux.Proofs.WG.RetirementSecurity.HolderOuter
