import Leanux.Proofs.WG.RetirementSecurity.HolderTrafficComposition

/-! Complete native fixture ingress uses its actual present-device guard,
admission ledger, finite occurrence list and final waits. The old source
certificate and exact key account refer to the identical original execution. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HolderOuter
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues Queues.RxCredits

theorem to_dynamic (entry : Inv carriers loans temporary locals active h w)
    (present : w.wg.dev.isSome=true) : HolderScheduled.Dynamic loans temporary locals active h w :=
  ⟨carriers,to_scheduled entry present⟩

theorem inject_finish (msg : List UInt8) : PrefixPreserves
    (HolderScheduled.Dynamic loans temporary locals active) OwnerChecks.Safe (InjectAccount.finish msg) := by
  have safe : ∀h w,HolderScheduled.Dynamic loans temporary locals active h w→OwnerChecks.Safe h :=
    fun _ _ entry=>HolderScheduled.dynamic_safe entry
  have store : ∀h w v,productStoreView v=productStoreView w→HolderScheduled.Dynamic loans temporary locals active h w→
      HolderScheduled.Dynamic loans temporary locals active h v := fun _ _ _ same entry=>HolderScheduled.dynamic_store entry same
  unfold InjectAccount.finish
  repeat' first
    | (scheduler_preserve_at RxHistory.runCryptWorkers; exact HolderScheduled.dynamic_fixed (fun _ _=>HolderScheduled.crypt))
    | (scheduler_preserve_at requireDrainedPrefix; exact HolderScheduled.dynamic_fixed (fun _ _=>HolderScheduled.drained _ _))
    | traffic_preserve_source safe using store

theorem flood_finish : PrefixPreserves
    (HolderScheduled.Dynamic loans temporary locals active) OwnerChecks.Safe FloodAccount.finish := by
  have safe : ∀h w,HolderScheduled.Dynamic loans temporary locals active h w→OwnerChecks.Safe h :=
    fun _ _ entry=>HolderScheduled.dynamic_safe entry
  have store : ∀h w v,productStoreView v=productStoreView w→HolderScheduled.Dynamic loans temporary locals active h w→
      HolderScheduled.Dynamic loans temporary locals active h v := fun _ _ _ same entry=>HolderScheduled.dynamic_store entry same
  unfold FloodAccount.finish
  repeat' first
    | (scheduler_preserve_at RxHistory.afterBatch; exact HolderScheduled.dynamic_fixed (fun _ _=>HolderScheduled.after_batch))
    | (scheduler_preserve_at requireDrainedPrefix; exact HolderScheduled.dynamic_fixed (fun _ _=>HolderScheduled.drained _ _))
    | traffic_preserve_source safe using store

theorem batch_finish (entries : List BatchItem) (cqes : List Int) : PrefixPreserves
    (HolderScheduled.Dynamic loans temporary locals active) OwnerChecks.Safe (BatchAccount.finish entries cqes) := by
  have safe : ∀h w,HolderScheduled.Dynamic loans temporary locals active h w→OwnerChecks.Safe h :=
    fun _ _ entry=>HolderScheduled.dynamic_safe entry
  have store : ∀h w v,productStoreView v=productStoreView w→HolderScheduled.Dynamic loans temporary locals active h w→
      HolderScheduled.Dynamic loans temporary locals active h v := fun _ _ _ same entry=>HolderScheduled.dynamic_store entry same
  unfold BatchAccount.finish
  repeat' first
    | (scheduler_preserve_at RxHistory.afterBatch; exact HolderScheduled.dynamic_fixed (fun _ _=>HolderScheduled.after_batch))
    | traffic_preserve_source safe using store

theorem inject_extra (entry : Inv carriers loans temporary locals active h w)
    (run : runPrefix (RxHistory.inject family port msg tos ll dest) w h=(.ok (result,v),k)) :
    HolderScheduled.Extra temporary locals active v := by
  rw [InjectAccount.source_factor] at run
  obtain ⟨src,u,j,start,tail⟩ := DecryptIteration.bind_normal run
  have history : j=h := by simpa only [start] using InjectAccount.front_history (family:=family) (port:=port) (tos:=tos) (ll:=ll) (dest:=dest) w h
  subst j
  have ready := to_dynamic (store entry (InjectAccount.front_store start)) (InjectAccount.front_present start)
  obtain ⟨x,t,l,receive,finish⟩ := DecryptIteration.bind_normal tail
  have receiving : PrefixPreserves (HolderScheduled.Dynamic loans temporary locals active) OwnerChecks.Safe
      (runWorkerPrefix .netRx (AdmissionCaller.receive msg src)) :=
    runWorkerPrefix_preserves (fun _ _ before=>HolderScheduled.dynamic_safe before)
      (fun _ _ _ same before=>HolderScheduled.dynamic_store before same) _ (HolderScheduled.receive_dynamic msg src)
  have after := (receiving u h ready).choose_spec.2.2
  rw [receive] at after
  have final := (inject_finish msg t l after).choose_spec.2.2
  rw [finish] at final
  exact final.choose_spec.2

theorem flood_extra (entry : Inv carriers loans temporary locals active h w)
    (run : runPrefix (RxHistory.flood count port family messages) w h=(.ok (result,v),k)) :
    HolderScheduled.Extra temporary locals active v := by
  rw [FloodAccount.source_factor] at run
  obtain ⟨src,u,j,start,tail⟩ := DecryptIteration.bind_normal run
  have history : j=h := by simpa only [start] using FloodAccount.front_history (family:=family) (port:=port) w h
  subst j
  have ready := to_dynamic (store entry (FloodAccount.front_store start)) (FloodAccount.front_present start)
  obtain ⟨x,t,l,loop,finish⟩ := DecryptIteration.bind_normal tail
  have after := (HolderScheduled.flood_loop family src (FloodAccount.messages count messages) u h ready).choose_spec.2.2
  rw [loop] at after
  have final := (flood_finish t l after).choose_spec.2.2
  rw [finish] at final
  exact final.choose_spec.2

theorem batch_extra (entries : List BatchItem) (entry : Inv carriers loans temporary locals active h w)
    (run : runPrefix (RxHistory.batch entries) w h=(.ok (result,v),k)) :
    HolderScheduled.Extra temporary locals active v := by
  rw [BatchAccount.source_factor] at run
  obtain ⟨d,u,j,start,tail⟩ := DecryptIteration.bind_normal run
  have history : j=h := by simpa only [start] using BatchAccount.front_history w h
  subst j
  have ready := to_dynamic (store entry (BatchAccount.front_store start)) (BatchAccount.front_present start)
  obtain ⟨cqes,t,l,loop,finish⟩ := DecryptIteration.bind_normal tail
  have after := (HolderScheduled.batch_loop d entries [] u h ready).choose_spec.2.2
  rw [loop] at after
  have final := (batch_finish entries cqes t l after).choose_spec.2.2
  rw [finish] at final
  exact final.choose_spec.2

theorem inject_normal (entry : Inv carriers loans temporary locals active h w)
    (run : runPrefix (RxHistory.inject family port msg tos ll dest) w h=(.ok (result,v),k)) :
    Inv [] loans temporary locals active k v :=
  ⟨(HolderTrafficEntry.inject_normal entry.1 run).choose_spec.2.1,inject_extra entry run⟩

theorem flood_normal (entry : Inv carriers loans temporary locals active h w)
    (run : runPrefix (RxHistory.flood count port family messages) w h=(.ok (result,v),k)) :
    ∃next,FloodAccount.Outcome carriers next count port family messages w v h k result ∧
      Inv next loans temporary locals active k v := by
  obtain ⟨next,source,peer⟩ := HolderTrafficEntry.flood_normal entry.1 run
  exact ⟨next,source,peer,flood_extra entry run⟩

theorem batch_normal (entries : List BatchItem) (entry : Inv carriers loans temporary locals active h w)
    (run : runPrefix (RxHistory.batch entries) w h=(.ok (result,v),k)) :
    ∃next,BatchAccount.Outcome carriers next entries w v h k result ∧ Inv next loans temporary locals active k v := by
  obtain ⟨next,source,peer⟩ := HolderTrafficEntry.batch_normal entries entry.1 run
  exact ⟨next,source,peer,batch_extra entries entry run⟩

end Leanux.Proofs.WG.RetirementSecurity.HolderOuter
