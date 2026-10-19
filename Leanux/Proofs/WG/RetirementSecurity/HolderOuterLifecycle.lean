import Leanux.Proofs.WG.RetirementSecurity.HolderLifecycleKeys

/-! Configuration and device lifetime joins use the same original observer
run for peer ownership, exact key credit and physical packet ownership. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HolderOuter
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues Queues.RxCredits

theorem configure (attrs : DeviceAttrs) : PrefixPreserves
    (Inv carriers loans temporary locals active) OwnerChecks.Safe
    (RxHistory.mixed (liftWGObserver (wgSetDevicePrefix attrs))) := by
  intro w h entry
  obtain ⟨suffix,history,safe,post⟩ := HolderEntry.configure attrs w h entry.1
  refine ⟨suffix,history,safe,?_⟩
  cases run : (runPrefix (RxHistory.mixed (liftWGObserver (wgSetDevicePrefix attrs))) w h).1 with
  | error e=>trivial
  | ok out=>
    rw [run] at post
    have actual := ((RxHistory.mixed_erases (liftWGObserver_erases (wgSetDevicePrefix_erases attrs))) w h).symm.trans run
    have native := HolderPoll.native_receipt actual
    have boundary := (hoare_iff_run_ambient _ _ _).mp (HolderBoundary.device attrs)
      w.wg w.ambient out.1 out.2.wg out.2.ambient
      (HolderBoundary.of_owner entry.2.1 entry.1 entry.2.2.2.2) native
    exact ⟨post,boundary.1.1,(hoare_iff_run_ambient _ _ _).mp
      (OccurrenceConfiguration.set_device attrs) w.wg w.ambient out.1 out.2.wg out.2.ambient entry.2.2.1 native,
      post.1.1.2.1,boundary.2.2⟩

theorem create : PrefixPreserves (Inv carriers loans [] [] []) OwnerChecks.Safe
    (RxHistory.mixed (liftWGObserver wgCreatePrefix)) := by
  intro w h entry
  obtain ⟨suffix,history,safe,post⟩ := HolderEntry.create w h entry.1
  refine ⟨suffix,history,safe,?_⟩
  cases run : (runPrefix (RxHistory.mixed (liftWGObserver wgCreatePrefix)) w h).1 with
  | error e=>trivial
  | ok out=>
    rw [run] at post
    have actual := ((RxHistory.mixed_erases (liftWGObserver_erases wgCreatePrefix_erases)) w h).symm.trans run
    have native := HolderPoll.native_receipt actual
    exact ⟨post,(hoare_iff_run_ambient _ _ _).mp HolderLifecycle.create
      w.wg w.ambient out.1 out.2.wg out.2.ambient entry.2.1 native,
      (hoare_iff_run_ambient _ _ _).mp OccurrenceLifecycle.create
        w.wg w.ambient out.1 out.2.wg out.2.ambient entry.2.2.1 native,
      post.1.1.2.1,(hoare_iff_run_ambient _ _ _).mp (KeySlotLiveness.create_device (pending:=[]))
        w.wg w.ambient out.1 out.2.wg out.2.ambient entry.2.2.2.2 native⟩

theorem delete_normal (entry : Inv carriers [] [] [] [] h w)
    (run : runPrefix (RxHistory.audit envWgDeleteAudit) w h=(.ok (result,v),k)) :
    carriers=[] ∧ v.wg.dev=none ∧ Inv carriers [] [] [] [] k v := by
  obtain ⟨empty,absent,post⟩ := HolderEntry.delete_normal entry.1 run
  have actual := ((RxHistory.audit_erases envWgDeleteAudit_erases) w h).symm.trans (congrArg Prod.fst run)
  exact ⟨empty,absent,post,HolderLifecycle.absent v.wg absent,
    (hoare_iff_run _ _ _).mp OccurrenceControls.env_delete w result v entry.2.2.1 actual,
    post.1.1.2.1,KeySlotLiveness.no_device v.wg absent⟩

theorem delete : PrefixPreserves (Inv carriers [] [] [] []) OwnerChecks.Safe
    (RxHistory.audit envWgDeleteAudit) := by
  intro w h entry
  obtain ⟨suffix,history,safe,_⟩ := HolderEntry.delete w h entry.1
  refine ⟨suffix,history,safe,?_⟩
  cases run : (runPrefix (RxHistory.audit envWgDeleteAudit) w h).1 with
  | error e=>trivial
  | ok out=>exact (delete_normal entry (Prod.ext run rfl)).2.2

end Leanux.Proofs.WG.RetirementSecurity.HolderOuter
