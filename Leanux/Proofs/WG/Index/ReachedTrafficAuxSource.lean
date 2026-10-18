import Leanux.Proofs.WG.Index.ReachedTrafficFrames
import Leanux.Proofs.WG.Index.ReachedDeferredSource
import Leanux.Proofs.WG.Index.ReachedSchedulerSource
import Leanux.Proofs.WG.Queues.HolderTrafficEntry
import Leanux.Proofs.WG.Queues.HolderTrafficDispatch
import Leanux.Proofs.WG.Lifetimes.TrafficPreservation

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.ReachedTraffic
open Leanux Leanux.WG Noise Std.Do Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues Queues.RxCredits Queues.RxCredits.DurableHolders

theorem any_fixed {α : Type} (loans : Reservations) (action : RxHistory.Obs α)
    (keeps : ∀ initial before,
      PrefixPreserves (Reached.Aux initial loans before) OwnerChecks.Safe action) :
    PrefixPreserves (Reached.AnyAux loans) OwnerChecks.Safe action := by
  intro w h pre
  obtain ⟨cs,pre⟩ := pre
  obtain ⟨suffix,history,safe,post⟩ := keeps cs h w h pre
  refine ⟨suffix,history,safe,?_⟩
  cases run:(runPrefix action w h).1 with
  | error stop=>trivial
  | ok out=>
    rw [run] at post
    exact Reached.aux_any post

theorem inline_aux (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event) :
    PrefixPreserves (Reached.Aux initial loans before) OwnerChecks.Safe RxHistory.pollScheduledInline := by
  apply Reached.aux_pair _ initial loans before (HolderAfterBatch.inlinePoll initial loans before)
  intro w h pre result v run
  have base := (BaseCoherence.inline_structure (BaseCoherence.view w.wg) w h rfl).choose_spec.2.2
  simp only [run] at base
  have kept := (hoare_iff_run _ _ _).mp PollCore.inline_ready w result v
    ⟨pre.1.2.2,pre.2.2⟩ ((RxHistory.pollScheduledInline_erases w h).symm.trans run)
  exact ⟨BaseCoherence.transport pre.2.1 base,kept.2⟩

theorem transmit_aux (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event)
    (family addr : Nat) (packets : List WG.Packet) (mtu : Nat) :
    PrefixPreserves (Reached.Aux initial loans before) OwnerChecks.Safe
      (RxHistory.mixed (liftWGObserver (wgXmitPrefix family addr packets mtu))) := by
  apply Reached.aux_pair _ initial loans before (HolderXmit.mixed initial loans before family addr packets mtu)
  intro w h pre result v run
  have native := DecryptIteration.native_normal
    (RxHistory.mixed_erases (liftWGObserver_erases (wgXmitPrefix_erases family addr packets mtu)))
    (Prod.ext run rfl)
  have base := (ProjectedAction.iff_run_ambient _ _ _).mp
    (BaseCoherence.wgXmit_view family addr packets mtu)
    w.wg w.ambient result v.wg v.ambient native
  have kept := (hoare_iff_run_ambient _ _ _).mp (TransmitCore.wgXmit_ready family addr packets mtu)
    w.wg w.ambient result v.wg v.ambient ⟨pre.1.2.2,pre.2.2⟩ native
  exact ⟨BaseCoherence.transport pre.2.1 base,kept.2⟩

theorem multicast_aux (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event)
    (family addr : Nat) :
    PrefixPreserves (Reached.Aux initial loans before) OwnerChecks.Safe
      (RxHistory.audit (xmitMulticastLoopAudit family addr)) :=
  ReachedScheduler.observed_store initial loans before _ _
    (BatchAccount.multicast initial loans before family addr)
    (RxHistory.audit_erases (xmitMulticastLoopAudit_erases family addr))
    ((pinned_const _private.Leanux.Proofs.WG.Queues.BatchAccount.«0».Leanux.Proofs.WG.Queues.RxCredits.BatchAccount.multicast_store) family addr)

theorem afterBatch_aux (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event) :
    PrefixPreserves (Reached.Aux initial loans before) OwnerChecks.Safe RxHistory.afterBatch := by
  rw [TrafficSource.afterBatch_factor]
  exact TrafficSource.afterBatch_preserves (I:=Reached.Aux initial loans before) (S:=OwnerChecks.Safe) (fun _ _ pre=>pre.1.2.1.safe)
    (fun _ _ _ same pre=>Reached.aux_store same pre) _ _ _ _ _
    (ReachedDeferred.crypt initial loans before) (ReachedDeferred.sendAll initial loans before)
    (ReachedWorkers.send_observed initial loans before)
    (ReachedScheduler.schedule_preserves initial loans before)
    (ReachedDeferred.drained initial loans before)

theorem inject_finish (loans : Reservations) (msg : List UInt8) :
    PrefixPreserves (Reached.AnyAux loans) OwnerChecks.Safe (InjectAccount.finish msg) := by
  unfold InjectAccount.finish
  repeat' first
    | (traffic_head RxHistory.runCryptWorkers
       exact any_fixed loans _ (fun cs before=>ReachedDeferred.crypt cs loans before))
    | (traffic_head RxHistory.mixed
       exact any_fixed loans _ (fun cs before=>ReachedDeferred.drained cs loans before _ _))
    | traffic_preserve_source (any_safe loans) using (any_product_store loans)

theorem flood_finish (loans : Reservations) :
    PrefixPreserves (Reached.AnyAux loans) OwnerChecks.Safe FloodAccount.finish := by
  unfold FloodAccount.finish
  repeat' first
    | (traffic_head RxHistory.afterBatch
       exact any_fixed loans _ (fun cs before=>afterBatch_aux cs loans before))
    | (traffic_head RxHistory.mixed
       exact any_fixed loans _ (fun cs before=>ReachedDeferred.drained cs loans before _ _))
    | traffic_preserve_source (any_safe loans) using (any_product_store loans)

theorem batch_finish (loans : Reservations) (items : List Env.BatchItem) (cqes : List Int) :
    PrefixPreserves (Reached.AnyAux loans) OwnerChecks.Safe (BatchAccount.finish items cqes) := by
  unfold BatchAccount.finish
  repeat' first
    | (traffic_head RxHistory.afterBatch
       exact any_fixed loans _ (fun cs before=>afterBatch_aux cs loans before))
    | traffic_preserve_source (any_safe loans) using (any_product_store loans)

end Leanux.Proofs.WG.Index.ReachedTraffic
