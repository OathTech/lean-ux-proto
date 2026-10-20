import Leanux.Proofs.WG.Progress.DeferredOuterSuffixFrames
import Leanux.Proofs.WG.Progress.DeferredOuterFactors
import Leanux.Proofs.WG.Progress.AdvanceWaitSource
import Leanux.Proofs.WG.Progress.SendLoopRecordSource

/-! Normal record-suffix effects for the actual deferred wait tails. The
supplied-record precondition selects the real recorded branches; no callback
termination, accepted-run or successful-service hypothesis is assumed. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Framing

theorem hiddenJiffies_retains (records : List HiddenRecord) (site : HiddenSite) :
    Preserves (fun w : World => Tail records w.ambient.hidden)
      (hiddenJiffies site : Leanux.M UInt64) := by
  apply liftAmbient_contract (AmbientM.hiddenJiffies site)
    (fun a => Tail records a.hidden) (fun _ a => Tail records a.hidden)
  unfold AmbientM.hiddenJiffies
  apply preserves_bind (hoare_consequence (hidden_after_tail site records)
    (fun _ h => h) (fun _ _ h => strict_tail h))
  intro bytes
  exact preserves_pure _

theorem timerWaitFinish_retains (records : List HiddenRecord) (pass endpoint : UInt64) :
    Preserves (fun w : World => Tail records w.ambient.hidden)
      (timerWaitFinish pass endpoint) := by
  unfold timerWaitFinish
  apply preserves_bind (requireNothingDue_retains records pass)
  intro _
  apply preserves_bind (hiddenJiffies_retains records .jiffiesEnd)
  intro j
  dsimp only
  split
  · apply preserves_bind (product_invariant_retains records _)
    intro _
    exact native_product records _
      (native_modify records (fun g => {g with jiffiesLast := some j}))
  · exact native_product records _
      (native_modify records (fun g => {g with jiffiesLast := some j}))

theorem idleTimers_retains (records : List HiddenRecord) :
    Preserves (fun w : World => Tail records w.ambient.hidden) Env.idleTimers := by
  have body : Preserves (fun w : World => Tail records w.ambient.hidden) (do
      let some endpoint ← peekSiteU64 .jiffiesEnd
        | throw (.hidden "no end-of-wait jiffies record (kind 310) in this operation")
      discard <| runTimers endpoint
      timerWaitFinish endpoint endpoint : Leanux.M Unit) := by
    apply preserves_bind (peekSiteU64_retains records .jiffiesEnd)
    intro endpoint
    cases endpoint with
    | none => exact hoare_throw _
    | some endpoint =>
      apply preserves_bind
      · exact discard_view_spec (fun w : World => w.ambient.hidden) (Tail records)
          _ (runTimers_retains records endpoint)
      intro _
      exact timerWaitFinish_retains records endpoint endpoint
  apply (hoare_iff_run _ _ _).mpr
  intro before value after pre run
  obtain ⟨rest,present,suffix⟩ := pre
  rw [idleTimers_recorded_source before (by simp [present])] at run
  exact (hoare_iff_run _ _ _).mp body before value after ⟨rest,present,suffix⟩ run

theorem afterAdvance_retains (records : List HiddenRecord) :
    Preserves (fun w : World => Tail records w.ambient.hidden) Env.afterAdvance := by
  rw [afterAdvance_source]
  apply preserves_bind
  · apply (hoare_iff_run _ _ _).mpr
    intro before value after pre run
    obtain ⟨rest,present,suffix⟩ := pre
    obtain ⟨receipt,_,_,_,same⟩ := afterAdvancePrefix_recorded_provenance
      before after value (by simp [present]) run
    subst after
    exact ⟨rest,present,suffix⟩
  intro receipt
  cases receipt with
  | none => exact preserves_pure _
  | some receipt =>
    unfold afterAdvanceSuffix afterAdvanceSuffixWith
    apply preserves_bind
    · exact discard_view_spec (fun w : World => w.ambient.hidden) (Tail records)
        _ (runTimers_retains records receipt.pass)
    intro _
    exact timerWaitFinish_retains records receipt.pass receipt.jEnd

theorem afterXmit_retains (records : List HiddenRecord) :
    Preserves (fun w : World => Tail records w.ambient.hidden) Env.afterXmit := by
  have fail {α : Type} (message : String) :
      Preserves (fun w : World => Tail records w.ambient.hidden)
        (unsupported message : Leanux.M α) := by
    apply (hoare_iff_run _ _ _).mpr
    intro before value after pre run
    cases run
  have dev : Preserves (fun w : World => Tail records w.ambient.hidden)
      (getDev : Leanux.M Device) := native_product records _ (native_getDev records)
  have clear : Preserves (fun w : World => Tail records w.ambient.hidden)
      (modifyWG (fun g => {g with queuedThisCall := []}) : Leanux.M Unit) := native_product records _
    (native_modify records (fun g => {g with queuedThisCall := []}))
  rw [DeferredOuter.afterXmit_source]
  unfold DeferredOuter.afterXmitWith
  repeat' first
    | env_operation_fact stack_getWG_retains
    | env_operation_fact fail
    | env_operation_fact dev
    | env_operation_fact clear
    | env_operation_fact runCryptWorkers_retains
    | env_operation_fact runSendWorkers_retains
    | env_operation_fact requireDrained_retains
    | with_reducible exact preserves_pure _
    | with_reducible apply preserves_bind
    | split
    | (with_reducible intro x; try dsimp only)

end Leanux.Proofs.WG.Progress.RecordSuffix
