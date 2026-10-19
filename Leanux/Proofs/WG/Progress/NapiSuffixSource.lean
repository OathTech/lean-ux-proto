import Leanux.Proofs.WG.Progress.PollSuffixSource
import Leanux.Proofs.WG.Progress.RecordSuffixSource
import Leanux.Proofs.WG.Queues.RxNapiHistory
import Leanux.Proofs.WG.Queues.RxWaitAppends

/-! Leaf-sensitive local variants of the original NAPI and section-wrapper preservation rules. Original factories and RX observers are unchanged. Ambient hidden/peek reads and exact administrative writes retain supplied-record suffixes; kernel-store equality alone is not used. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues

theorem pendingScan_retains (records : List HiddenRecord) :
    NativeKeeps records RxNapi.pendingSource := by
  unfold RxNapi.pendingSource
  exact native_bind records _ _ (native_getDev records) (fun _=>native_pure records _)

theorem scheduledScan_retains (records : List HiddenRecord) :
    NativeKeeps records RxNapi.scheduledSource := by
  unfold RxNapi.scheduledSource
  exact native_bind records _ _ (native_getDev records) (fun _=>native_pure records _)

theorem product_hidden_retains (records : List HiddenRecord) (site : HiddenSite) :
    Preserves (fun w : World=>Tail records w.ambient.hidden) (hidden site : Leanux.M (List UInt8)) :=
  hoare_consequence (hidden_after_product_tail site records) (fun _ hi=>hi)
    (fun _ _ hi=>strict_tail hi)

theorem runWorkerPrefix_retains {E : Type} (records : List HiddenRecord)
    (worker : Worker) (body : PrefixM E Unit)
    (keep : PrefixPreserves (fun _ (w : World)=>Tail records w.ambient.hidden) (fun _=>True) body) :
    PrefixPreserves (fun _ (w : World)=>Tail records w.ambient.hidden) (fun _=>True)
      (runWorkerPrefix worker body) := by
  unfold runWorkerPrefix
  repeat' first
    | exact keep
    | with_reducible exact product_lift_retains records _ (product_hidden_retains records _)
    | with_reducible exact product_lift_retains records _ (modifyAmbient_hidden records _ (fun _=>rfl))
    | with_reducible exact PrefixPreserves.pure (fun _ _ _=>True.intro) _
    | with_reducible apply PrefixPreserves.bind
    | split
    | (with_reducible intro x; try dsimp only)

/-- Leaf-sensitive local variant of RxNapi.softirq_preserves. -/

theorem softirq_preserves_suffix_variant {E : Type} (records : List HiddenRecord)
    (scan : PrefixM E (List PeerId)) (poll : PeerId→Nat→PrefixM E Nat)
    (hs : PrefixPreserves (fun _ (w : World)=>Tail records w.ambient.hidden) (fun _=>True) scan)
    (hp : ∀pid budget,PrefixPreserves (fun _ (w : World)=>Tail records w.ambient.hidden)
      (fun _=>True) (poll pid budget)) :
    PrefixPreserves (fun _ (w : World)=>Tail records w.ambient.hidden) (fun _=>True)
      (RxNapi.softirqWith scan poll) := by
  unfold RxNapi.softirqWith
  simp only [discard,map_const,Function.comp_def,map_eq_pure_bind]
  repeat' first
    | exact hs
    | with_reducible exact hp _ _
    | with_reducible apply runWorkerPrefix_retains records
    | with_reducible exact product_lift_retains records _ (getAmbient_retains records)
    | with_reducible exact product_lift_retains records _ (peek_retains records)
    | with_reducible exact RxJoint.PollSource.unsupported_preserves (fun _ _ _=>True.intro) _
    | with_reducible exact PrefixPreserves.pure (fun _ _ _=>True.intro) _
    | with_reducible apply PrefixPreserves.forIn _ _ _ (fun _ _ _=>True.intro)
    | with_reducible apply PrefixPreserves.bind
    | split
    | (with_reducible intro x; try dsimp only)

/-- Leaf-sensitive local variant of RxNapi.inline_preserves. -/

theorem inline_preserves_suffix_variant {E : Type} (records : List HiddenRecord)
    (scan : PrefixM E (List PeerId)) (poll : PeerId→Nat→PrefixM E Nat)
    (hs : PrefixPreserves (fun _ (w : World)=>Tail records w.ambient.hidden) (fun _=>True) scan)
    (hp : ∀pid budget,PrefixPreserves (fun _ (w : World)=>Tail records w.ambient.hidden)
      (fun _=>True) (poll pid budget)) :
    PrefixPreserves (fun _ (w : World)=>Tail records w.ambient.hidden) (fun _=>True)
      (RxNapi.inlineWith scan poll) := by
  unfold RxNapi.inlineWith
  simp only [discard,map_const,Function.comp_def,map_eq_pure_bind]
  repeat' first
    | exact hs
    | with_reducible exact hp _ _
    | with_reducible exact RxJoint.PollSource.unsupported_preserves (fun _ _ _=>True.intro) _
    | with_reducible exact PrefixPreserves.pure (fun _ _ _=>True.intro) _
    | with_reducible apply PrefixPreserves.forIn _ _ _ (fun _ _ _=>True.intro)
    | with_reducible apply PrefixPreserves.bind
    | split
    | (with_reducible intro x; try dsimp only)

/-- Leaf-sensitive local variant of RxNapi.irqExit_preserves. -/

theorem irqExit_preserves_suffix_variant {E : Type} (records : List HiddenRecord)
    (scan : PrefixM E Bool) (softirq : PrefixM E Unit)
    (hs : PrefixPreserves (fun _ (w : World)=>Tail records w.ambient.hidden) (fun _=>True) scan)
    (hp : PrefixPreserves (fun _ (w : World)=>Tail records w.ambient.hidden) (fun _=>True) softirq) :
    PrefixPreserves (fun _ (w : World)=>Tail records w.ambient.hidden) (fun _=>True)
      (RxNapi.irqExitWith scan softirq) := by
  unfold RxNapi.irqExitWith
  repeat' first
    | exact hs
    | exact hp
    | with_reducible exact product_lift_retains records _ (getAmbient_retains records)
    | with_reducible exact product_lift_retains records _ (peek_retains records)
    | with_reducible exact product_lift_retains records _ (chooseNapiHere_retains records)
    | with_reducible exact PrefixPreserves.pure (fun _ _ _=>True.intro) _
    | with_reducible apply PrefixPreserves.bind
    | split
    | (with_reducible intro x; try dsimp only)

theorem observePoll_retains_of_stack (records : List HiddenRecord)
    (stack : ∀ bytes,Preserves (fun w : World=>Tail records w.ambient.hidden) (Env.deliverInner bytes))
    (pid : PeerId) (budget : Nat) :
    PrefixPreserves (fun _ (w : World)=>Tail records w.ambient.hidden) (fun _=>True)
      (RxHistory.observePoll pid budget) :=
  product_observed records _ _ (RxHistory.observePoll_appends pid budget)
    (RxHistory.observePoll_erases pid budget) (rxPoll_retains_of_stack records stack pid budget)

theorem napiSoftirq_observed_retains_of_stack (records : List HiddenRecord)
    (stack : ∀ bytes,Preserves (fun w : World=>Tail records w.ambient.hidden) (Env.deliverInner bytes)) :
    PrefixPreserves (fun _ (w : World)=>Tail records w.ambient.hidden) (fun _=>True) RxHistory.napiSoftirq := by
  apply softirq_preserves_suffix_variant records
  · exact product_observed records _ _ (Appends.focus _ _ _)
      (RxHistory.audit_erases (auditFocus_erases (liftWGObserver_erases RxNapi.pending_erases)))
      (native_product records _ (pendingScan_retains records))
  · exact observePoll_retains_of_stack records stack

theorem pollScheduledInline_observed_retains_of_stack (records : List HiddenRecord)
    (stack : ∀ bytes,Preserves (fun w : World=>Tail records w.ambient.hidden) (Env.deliverInner bytes)) :
    PrefixPreserves (fun _ (w : World)=>Tail records w.ambient.hidden) (fun _=>True) RxHistory.pollScheduledInline := by
  apply inline_preserves_suffix_variant records
  · exact product_observed records _ _ (Appends.focus _ _ _)
      (RxHistory.audit_erases (auditFocus_erases (liftWGObserver_erases RxNapi.pending_erases)))
      (native_product records _ (pendingScan_retains records))
  · exact observePoll_retains_of_stack records stack

theorem napiIrqExit_observed_retains_of_stack (records : List HiddenRecord)
    (stack : ∀ bytes,Preserves (fun w : World=>Tail records w.ambient.hidden) (Env.deliverInner bytes)) :
    PrefixPreserves (fun _ (w : World)=>Tail records w.ambient.hidden) (fun _=>True) RxHistory.napiIrqExit := by
  apply irqExit_preserves_suffix_variant records
  · exact product_observed records _ _ (Appends.focus _ _ _)
      (RxHistory.audit_erases (auditFocus_erases (liftWGObserver_erases RxNapi.scheduled_erases)))
      (native_product records _ (scheduledScan_retains records))
  · exact napiSoftirq_observed_retains_of_stack records stack

theorem softirq_retains_of_stack (records : List HiddenRecord)
    (stack : ∀ bytes,Preserves (fun w : World=>Tail records w.ambient.hidden) (Env.deliverInner bytes)) :
    Preserves (fun w : World=>Tail records w.ambient.hidden) Env.napiSoftirq :=
  observed_product records _ _ RxHistory.napiSoftirq_erases (napiSoftirq_observed_retains_of_stack records stack)

theorem inline_retains_of_stack (records : List HiddenRecord)
    (stack : ∀ bytes,Preserves (fun w : World=>Tail records w.ambient.hidden) (Env.deliverInner bytes)) :
    Preserves (fun w : World=>Tail records w.ambient.hidden) Env.pollScheduledInline :=
  observed_product records _ _ RxHistory.pollScheduledInline_erases (pollScheduledInline_observed_retains_of_stack records stack)

theorem irqExit_retains_of_stack (records : List HiddenRecord)
    (stack : ∀ bytes,Preserves (fun w : World=>Tail records w.ambient.hidden) (Env.deliverInner bytes)) :
    Preserves (fun w : World=>Tail records w.ambient.hidden) Env.napiIrqExit :=
  observed_product records _ _ RxHistory.napiIrqExit_erases (napiIrqExit_observed_retains_of_stack records stack)
end Leanux.Proofs.WG.Progress.RecordSuffix
