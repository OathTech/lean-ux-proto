import Leanux.Proofs.WG.RetirementSecurity.HolderOuter

/-! Actual traffic admissions choose their new peer ledger from source.
The separate exact key account follows the same admission and NAPI cuts;
rebasing only consumes the actual reached removal suffix. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HolderScheduled
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues Queues.RxCredits

theorem inline_poll : PrefixPreserves (Inv initial loans before temporary locals active)
    OwnerChecks.Safe RxHistory.pollScheduledInline := by
  intro w h entry
  obtain ⟨suffix,history,safe,post⟩ := HolderAfterBatch.inlinePoll initial loans before w h entry.1
  have after := (HolderNapiKeys.inline w h (napi_entry entry)).choose_spec.2.2
  refine ⟨suffix,history,safe,?_⟩
  cases run:(runPrefix RxHistory.pollScheduledInline w h).1 with
  | error e=>trivial
  | ok out=>
    rw [run] at post after
    exact ⟨post,after.2.1,after.2.2.1,after.2.2.2.2.1,after.2.2.2.2.2⟩

theorem after_batch : PrefixPreserves (Inv initial loans before temporary locals active)
    OwnerChecks.Safe RxHistory.afterBatch := by
  rw [TrafficSource.afterBatch_factor]
  exact TrafficSource.afterBatch_preserves (I:=Inv initial loans before temporary locals active)
    (fun _ _ entry=>entry.1.2.1.safe) (fun _ _ _ same entry=>store entry same)
    _ _ _ _ _ crypt send_all send_one schedule drained

def Dynamic (loans : Reservations) (temporary : Credits.Ledger)
    (locals : List TxLocalBatch) (active : List (List SkbId)) (h : List RxHistory.Event) (w : World) : Prop :=
  ∃carriers,Inv carriers loans h temporary locals active h w

theorem rebase (entry : Inv initial loans before temporary locals active h w) :
    Dynamic loans temporary locals active h w := by
  obtain ⟨suffix,history,peer⟩ := HolderInitial.rebase entry.1
  exact ⟨_,peer,entry.2⟩

theorem dynamic_store (entry : Dynamic loans temporary locals active h w)
    (same : productStoreView v=productStoreView w) : Dynamic loans temporary locals active h v := by
  obtain ⟨carriers,entry⟩ := entry
  exact ⟨carriers,store entry same⟩

theorem dynamic_safe (entry : Dynamic loans temporary locals active h w) : OwnerChecks.Safe h :=
  entry.choose_spec.1.2.1.safe

theorem dynamic_fixed {action : RxHistory.Obs α}
    (keeps : ∀initial before,PrefixPreserves (Inv initial loans before temporary locals active) OwnerChecks.Safe action) :
    PrefixPreserves (Dynamic loans temporary locals active) OwnerChecks.Safe action := by
  intro w h entry
  obtain ⟨carriers,entry⟩ := entry
  obtain ⟨suffix,history,safe,post⟩ := keeps carriers h w h entry
  refine ⟨suffix,history,safe,?_⟩
  cases run:(runPrefix action w h).1 with
  | error e=>trivial
  | ok out=>rw [run] at post; exact rebase post

theorem receive_extra (msg : List UInt8) (src : SkbSource) :
    Preserves (Extra temporary locals active) (liftWG (wgReceive msg src)) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v entry run
  have native := HolderPoll.native_receipt run
  have kept := (hoare_iff_run_ambient _ _ _).mp (ReceiveEntry.receive msg src)
    w.wg w.ambient result v.wg v.ambient ⟨entry.1,entry.2.1.1⟩ native
  exact ⟨kept.1,⟨kept.2,(hoare_iff_run_ambient _ _ _).mp (ReceiveOccurrences.receive msg src)
      w.wg w.ambient result v.wg v.ambient entry.2.1.2 native⟩,
    BaseCoherence.transport entry.2.2.1 ((ProjectedAction.iff_run_ambient _ _ _).mp
      (BaseCoherence.wgReceive_view msg src) w.wg w.ambient result v.wg v.ambient native),
    (hoare_iff_run_ambient _ _ _).mp (KeySlotLiveness.receive (pending:=[]) msg src)
      w.wg w.ambient result v.wg v.ambient entry.2.2.2 native⟩

theorem receive_dynamic (msg : List UInt8) (src : SkbSource) : PrefixPreserves
    (Dynamic loans temporary locals active) OwnerChecks.Safe (AdmissionCaller.receive msg src) := by
  intro w h entry
  obtain ⟨carriers,entry⟩ := entry
  obtain ⟨suffix,history,safe,_⟩ := OwnerReceive.wgReceive_checked msg src w h entry.1.2.1
  refine ⟨suffix,history,safe,?_⟩
  cases run:(runPrefix (AdmissionCaller.receive msg src) w h).1 with
  | error e=>trivial
  | ok out=>
    rcases out with ⟨⟨⟩,v⟩
    have actual : runPrefix (AdmissionCaller.receive msg src) w h=(.ok ((),v),
        (runPrefix (AdmissionCaller.receive msg src) w h).2) := Prod.ext run rfl
    obtain ⟨prior,next,hist,receipt,after⟩ := AdmissionAuxiliary.receive_rebase entry.1 actual
    have extra := (hoare_iff_run _ _ _).mp (receive_extra msg src) w () v entry.2
      ((AdmissionCaller.receive_erases msg src w h).symm.trans (congrArg Prod.fst actual))
    exact ⟨next,after,extra⟩

end Leanux.Proofs.WG.RetirementSecurity.HolderScheduled
