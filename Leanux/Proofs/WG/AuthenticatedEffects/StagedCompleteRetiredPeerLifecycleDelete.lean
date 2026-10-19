import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerLifecycleDestruct

/-! Actual environment deletion preserves the exact reference account. The
native idle and cursor guards discharge RX obligations before any reset; the
original absence branch and notification order are unchanged. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Lifecycle
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes
open Queues Queues.RxCredits DurableHolders HolderDeviceCreate
set_option maxHeartbeats 600000

private theorem lift_spec {action : WG.M α} {P : WGWorld→Prop} {Q : α→WGWorld→Prop}
    (rule : Hoare action P Q) : Hoare (liftWG action) (fun w=>P w.wg) (fun x w=>Q x w.wg) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w x v before run
  exact (hoare_iff_run_ambient _ _ _).mp rule w.wg w.ambient x v.wg v.ambient before
    ((pinned_const _private.Leanux.Proofs.WG.Queues.RxPollCarrier.«0».Leanux.Proofs.WG.Queues.RxCredits.native_receipt) action w v x run)

theorem product_clear (action : Leanux.M α) (frame : SameProductStore action) :
    Preserves (fun w : World=>Clear cs loans w.wg) action := by
  apply (hoare_iff_run _ _ _).mpr
  intro w x v before run
  have fields := congrArg (fun s : ProductStore43=>s.2.2.2)
    ((ProjectedAction.iff_run _ _ _).mp frame w x v run)
  obtain ⟨account,c7,c8⟩ := before
  obtain ⟨h,account⟩ := account
  exact ⟨⟨h,account.store fields⟩,
    (congrArg (fun s : WGStoreView=>activeCursor s.nlSock7) fields).trans c7,
    (congrArg (fun s : WGStoreView=>activeCursor s.nlSock8) fields).trans c8⟩

private theorem routing_clear (action : Net.M α) :
    Preserves (fun w : World=>Clear cs loans w.wg)
      (MonadLift.monadLift (MonadLift.monadLift action : WG.M α) : Leanux.M α) :=
  product_clear _ (liftWG_sameProductStore _ (liftRouting_sameWGStore action))

private abbrev notifyDown : Leanux.M Unit :=
  pinned_const _private.Leanux.Proofs.WG.Queues.HolderDeviceDelete.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderDeviceDelete.notifyDown
private abbrev notifyUnregister : Leanux.M Unit :=
  pinned_const _private.Leanux.Proofs.WG.Queues.HolderDeviceDelete.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderDeviceDelete.notifyUnregister

private theorem notify_down : Preserves (fun w : World=>Clear cs loans w.wg) notifyDown := by
  unfold notifyDown
  index_unfold _private.Leanux.Proofs.WG.Queues.HolderDeviceDelete.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderDeviceDelete.notifyDown
  unfold modifyRouting
  repeat' first
    | (allocation_release_lift_from WG.M; exact routing_clear _)
    | (allocation_release_lift_from Net.M; exact routing_clear _)
    | rx_retention_step

private theorem notify_unregister : Preserves (fun w : World=>Clear cs loans w.wg) notifyUnregister := by
  unfold notifyUnregister
  index_unfold _private.Leanux.Proofs.WG.Queues.HolderDeviceDelete.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderDeviceDelete.notifyUnregister
  unfold modifyRouting
  apply preserves_bind (product_clear _
    (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerControlCalls.«0».Leanux.Proofs.WG.OwnerControlCalls.inetdevDestroy_store))
  intro _
  repeat' first
    | (allocation_release_lift_from WG.M; exact routing_clear _)
    | (allocation_release_lift_from Net.M; exact routing_clear _)
    | rx_retention_step

/-- Original notifications and optional shutdown before the native destructor. -/
def deletePrefix : Leanux.M Unit := do
  if (←getDev).running then
    WG.wgDown
    notifyDown
  skipCut allocCuts
  notifyUnregister
  mayHaveSlept

theorem delete_prefix : Preserves (fun w : World=>Clear cs loans w.wg) deletePrefix := by
  let P := fun w : World=>Clear cs loans w.wg
  unfold deletePrefix
  simp (config := {zeta := false}) only [skipCut]
  repeat' first
    | exact notify_down
    | exact notify_unregister
    | (allocation_release_lift_from WG.M; first
        | exact lift_spec clear_read
        | exact lift_spec down_clear
        | exact product_clear _ (liftWG_sameProductStore _ mayHaveSlept_sameWGStore))
    | (allocation_release_lift_from AmbientM; exact productAmbient_spec _ P (fun _ _ h=>h))
    | rx_retention_step

/-- Literal normal and error semantics, including the guards before ENODEV. -/
theorem delete_factor : Env.wgDelete = (do
    HolderDeviceDelete.guards
    if (←getWG).dev.isNone then return -ENODEV
    deletePrefix
    liftWG wgDestruct
    pure 0) := by
  rw [HolderDeviceDelete.source_factor]
  change (do
    HolderDeviceDelete.guards
    if (←getWG).dev.isNone then return -ENODEV
    (pinned_const _private.Leanux.Proofs.WG.Queues.HolderDeviceDelete.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderDeviceDelete.deleteBody) notifyDown notifyUnregister) = _
  index_unfold _private.Leanux.Proofs.WG.Queues.HolderDeviceDelete.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderDeviceDelete.deleteBody
  simp only [deletePrefix,bind_assoc,bind_if_source]
  rfl

/-- The actual deletion guards establish an empty RX ledger and inactive
cursors while retaining exactly the input account on the unchanged state. -/
theorem delete_guards (before : ExactBoundary cs loans w.wg)
    (physical : OptionalPhysical w.wg)
    (run : HolderDeviceDelete.guards.run w=.ok ((),v)) :
    v=w ∧ cs=[] ∧ Clear cs loans v.wg := by
  obtain ⟨same,empty,c7,c8⟩ := HolderDeviceDelete.guards_normal w v before.lower physical run
  subst v
  exact ⟨rfl,empty,before,c7,c8⟩

theorem delete_normal (w v : World) (before : ExactBoundary cs [] w.wg)
    (physical : OptionalPhysical w.wg) (run : Env.wgDelete.run w=.ok (result,v)) :
    cs=[] ∧ v.wg.dev=none ∧ ExactBoundary cs [] v.wg ∧ OptionalPhysical v.wg := by
  rw [delete_factor,MaterialOrigin.bind_ok] at run
  obtain ⟨ignored,middle,guard,rest⟩ := run
  cases ignored
  obtain ⟨same,empty,ready⟩ := delete_guards before physical guard
  subst middle
  subst cs
  simp only [StateT.run_bind,
    show (getWG : Leanux.M WGWorld).run w=.ok (w.wg,w) from rfl,
    CounterWindow.except_ok_bind] at rest
  split at rest
  · rename_i absent
    have noDev : w.wg.dev=none := Option.isNone_iff_eq_none.mp absent
    cases rest
    exact ⟨rfl,noDev,before,Or.inl noDev⟩
  · rw [MaterialOrigin.bind_ok] at rest
    obtain ⟨ignored,u,frontRun,rest⟩ := rest
    cases ignored
    have atDrop := (hoare_iff_run _ _ _).mp delete_prefix w () u ready frontRun
    rw [MaterialOrigin.bind_ok] at rest
    obtain ⟨ignored,z,dropped,returned⟩ := rest
    cases ignored
    cases returned
    have out := (hoare_iff_run _ _ _).mp (lift_spec destruct) u () v atDrop dropped
    exact ⟨rfl,out.1,out.2.1.1,out.2.2⟩

theorem delete : Preserves (fun w : World=>ExactBoundary cs [] w.wg ∧ OptionalPhysical w.wg)
    Env.wgDelete := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v before run
  have out := delete_normal w v before.1 before.2 run
  exact ⟨out.2.2.1,out.2.2.2⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Lifecycle
