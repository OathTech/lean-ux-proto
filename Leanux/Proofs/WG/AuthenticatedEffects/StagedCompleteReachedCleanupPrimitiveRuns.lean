import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCleanupPrimitiveFrames

/-! The original observed free and its fixed native sub-prefixes have the
same getter and erase results. This is a source-specific run calculation,
including the exact lifetime suffix, rather than an arbitrary factorization. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CleanupPrimitive
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation HandshakeSecurity.StagedConservation

theorem cleanup_run (skb : SkbId) (w v : World) (history : List CausalJournal.Event)
    (native : (liftWG (freeTxSkb skb)).run w = .ok ((),v)) :
    runPrefix (FirstTerminal.cleanupFree skb) w history =
      (.ok ((),v),history ++ [readEvent w.wg skb,releaseEvent w.wg skb]) := by
  obtain ⟨packet,read,_,_,_⟩ := native_parts skb w v native
  have observed := TxDisposition.free_run skb w (history.filterMap CausalJournal.txEvent?)
  rw [read,native] at observed
  have focused := focusPrefix_suffix CausalJournal.txEvent CausalJournal.txEvent?
    (TxDisposition.nativeAccess (freeTxSkbPrefix skb)) w history (.ok ((),v))
    [.access (.packet (.read (.inl skb) (packetStamp w.wg skb))),
      .access (.packet (.release (.inl skb) (packetStamp w.wg skb)))] observed
  simpa only [FirstTerminal.cleanupFree,HandshakeSecurity.StagedDisposal.TxSource.observed,
    HandshakeSecurity.StagedDisposal.TxSource.Ops.focus,HandshakeSecurity.StagedDisposal.TxSource.native,
    List.map_cons,List.map_nil,readEvent,releaseEvent] using focused

theorem read_prefix_run (skb : SkbId) (w v : World) (history : List CausalJournal.Event)
    (native : (liftWG (freeTxSkb skb)).run w = .ok ((),v)) :
    runPrefix (readPrefix w skb) w history = (.ok ((),w),history ++ [readEvent w.wg skb]) := by
  obtain ⟨packet,read,_,_,_⟩ := native_parts skb w v native
  rw [readPrefix,runPrefix_bind,runPrefix_lift,read]
  rfl

theorem mutation_prefix_run (skb : SkbId) (w v : World) (history : List CausalJournal.Event)
    (native : (liftWG (freeTxSkb skb)).run w = .ok ((),v)) :
    runPrefix (mutationPrefix w skb) w history = (.ok ((),v),current .mutated w skb history) := by
  obtain ⟨_,_,mutation,_,_⟩ := native_parts skb w v native
  rw [mutationPrefix,runPrefix_bind,read_prefix_run skb w v history native]
  change ((liftWG (modifyDev (erasePacketDevice (.inl skb)))).run w,_) = _
  rw [mutation]
  rfl

theorem prefix_run (phase : Phase) (skb : SkbId) (w v : World) (history : List CausalJournal.Event)
    (native : (liftWG (freeTxSkb skb)).run w = .ok ((),v)) :
    runPrefix (atPhase phase w skb) w history = (.ok ((),v),current phase w skb history) := by
  cases phase with
  | mutated => exact mutation_prefix_run skb w v history native
  | released =>
    change runPrefix (releasedPrefix w skb) w history = _
    rw [releasedPrefix,runPrefix_bind,mutation_prefix_run skb w v history native]
    simp only [runPrefix_emit,current,List.append_assoc,List.cons_append,List.nil_append]

theorem labelled_run (reason : Terminal.Reason) (skb : SkbId) (w v : World)
    (history : List CausalJournal.Event)
    (native : (liftWG (freeTxSkb skb)).run w = .ok ((),v)) :
    runPrefix (CreateDisposal.free reason skb) w history = (.ok ((),v),finished reason skb w v history) := by
  have result := (FirstTerminal.labelled_cut reason skb w v history _ (cleanup_run skb w v history native)).2
  simpa only [finished,receipt,List.append_assoc,List.cons_append,List.nil_append] using result

/-- The concrete post-erase suffix emits its two actual remaining records
without another native operation or Stop; it matches the original wrapper. -/
theorem original_suffix (phase : Phase) (reason : Terminal.Reason) (skb : SkbId) (w v : World)
    (history : List CausalJournal.Event)
    (native : (liftWG (freeTxSkb skb)).run w = .ok ((),v)) :
    runPrefix (CreateDisposal.free reason skb) w history =
      runPrefix (due phase reason skb w v) v (current phase w skb history) := by
  rw [labelled_run reason skb w v history native,due_run]

/-- The getter, actual erase, and fixed pending emissions split the original
labelled cleanup at the native mutation, with the same completed run. -/
theorem source_split (phase : Phase) (reason : Terminal.Reason) (skb : SkbId) (w v : World)
    (history : List CausalJournal.Event)
    (native : (liftWG (freeTxSkb skb)).run w = .ok ((),v)) :
    runPrefix (CreateDisposal.free reason skb) w history =
      runPrefix (do atPhase phase w skb; due phase reason skb w v) w history := by
  rw [runPrefix_bind,prefix_run phase skb w v history native]
  exact original_suffix phase reason skb w v history native

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CleanupPrimitive
