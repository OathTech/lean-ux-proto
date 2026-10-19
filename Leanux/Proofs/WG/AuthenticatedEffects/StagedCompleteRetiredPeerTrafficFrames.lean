import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerRxAuxiliaryFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerTransmit
import Leanux.Proofs.WG.Queues.BatchAccount

/-! The original traffic callbacks retain paired auxiliary and exact-account
facts on one journal. Callback arguments name actual scheduler actors; the
closed source endpoints instantiate them. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Traffic
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes
open Queues Queues.RxCredits DurableHolders
open Auxiliary (Inv)

theorem inline (initial : RxCredits.Ledger) (loans : Reservations) (before : List RxHistory.Event) :
    PrefixPreserves (Inv initial loans before) OwnerChecks.Safe RxHistory.pollScheduledInline :=
  Auxiliary.pair_preserves _ (HolderAfterBatch.inlinePoll initial loans before)
    (ExactAt.inline_preserves initial loans before)

theorem after_batch (actors : Scheduler.Actors initial loans before) :
    PrefixPreserves (Inv initial loans before) OwnerChecks.Safe RxHistory.afterBatch := by
  rw [TrafficSource.afterBatch_factor]
  exact TrafficSource.afterBatch_preserves
    (I:=Inv initial loans before) (S:=OwnerChecks.Safe)
    (fun _ _ hi=>hi.safe) (fun _ _ _ same hi=>Auxiliary.store hi same)
    _ _ _ _ _ (Deferred.crypt actors) (Deferred.runSendWorkers actors) Deferred.sendOne
    (Scheduler.schedule_preserves initial loans before actors) Deferred.drained

theorem route : PrefixPreserves (Inv initial loans before) OwnerChecks.Safe (FloodLoop.route family src) := by
  have safe : ∀ h w,Inv initial loans before h w→OwnerChecks.Safe h := fun _ _ hi=>hi.safe
  have store : ∀ h w v,productStoreView v=productStoreView w→Inv initial loans before h w→Inv initial loans before h v := fun _ _ _ same hi=>Auxiliary.store hi same
  unfold FloodLoop.route
  repeat' traffic_preserve_source safe using store

theorem batch_inject_front : PrefixPreserves (Inv initial loans before) OwnerChecks.Safe
    (BatchAccount.injectFront d family port) := by
  have safe : ∀ h w,Inv initial loans before h w→OwnerChecks.Safe h := fun _ _ hi=>hi.safe
  have store : ∀ h w v,productStoreView v=productStoreView w→Inv initial loans before h w→Inv initial loans before h v := fun _ _ _ same hi=>Auxiliary.store hi same
  unfold BatchAccount.injectFront
  repeat' traffic_preserve_source safe using store

theorem multicast (family addr : Nat) : PrefixPreserves (Inv initial loans before) OwnerChecks.Safe
    (RxHistory.audit (xmitMulticastLoopAudit family addr)) := by
  have frame : SameProductStore (Env.xmitMulticastLoop family addr) :=
    (pinned_const _private.Leanux.Proofs.WG.Queues.BatchAccount.«0».Leanux.Proofs.WG.Queues.RxCredits.BatchAccount.multicast_store) family addr
  exact Auxiliary.pair_preserves _ (BatchAccount.multicast initial loans before family addr)
    (ExactAt.audit_frame _ _ (xmitMulticastLoopAudit_erases family addr) frame)

theorem transmit (family addr : Nat) (packets : List WG.Packet) (mtu : Nat) :
    PrefixPreserves (Inv initial loans before) OwnerChecks.Safe
      (RxHistory.mixed (liftWGObserver (wgXmitPrefix family addr packets mtu))) :=
  Auxiliary.pair_preserves _ (HolderXmit.mixed initial loans before family addr packets mtu)
    (ExactAt.transmit (initial:=initial) (loans:=loans) (before:=before) family addr packets mtu)

theorem batch_xmit (d : Device) (cqes : List Int) (family addr : Nat)
    (payload : List UInt8) (opts : Env.XmitOpts) :
    PrefixPreserves (Inv initial loans before) OwnerChecks.Safe
      (RxHistory.batchItem d cqes (.xmit family addr payload opts)) := by
  have safe : ∀ h w,Inv initial loans before h w→OwnerChecks.Safe h := fun _ _ hi=>hi.safe
  have store : ∀ h w v,productStoreView v=productStoreView w→Inv initial loans before h w→Inv initial loans before h v := fun _ _ _ same hi=>Auxiliary.store hi same
  unfold RxHistory.batchItem
  repeat' first
    | (environment_at "xmitMulticastLoopAudit"; exact multicast _ _)
    | (current_env_at wgXmitPrefix; exact transmit _ _ _ _)
    | (traffic_head xmitPackets; exact viewLiftPrefix_preserves productStoreView safe store (xmitPackets_sameKernel _ _ _ _))
    | traffic_preserve_source safe using store

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Traffic
