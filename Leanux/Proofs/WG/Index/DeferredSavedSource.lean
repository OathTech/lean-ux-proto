import Leanux.Proofs.WG.Queues.HolderAuxTimers

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.DeferredRules
open Leanux Leanux.WG Queues Queues.RxCredits
open Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
variable {I : List RxHistory.Event→World→Prop} {S : List RxHistory.Event→Prop}

macro "deferred_saved_drop " inv:term : tactic => `(tactic|
  (timer_audit_saved_pre; refine PrefixEnsures.consequence
    (P := $inv) (Q := fun _=>$inv) ?_ (fun _ _ pre=>pre.1) (fun _ _ _ pre=>pre)))

macro "deferred_saved_calls " inv:ident safe:ident stored:ident timer:ident complete:ident send:ident clear:ident crypt:ident : tactic =>
  `(tactic| first
    | (rx_timer_head timerDispatchAudit; exact $timer _ _ _ _ _)
    | (rx_timer_head requireStepCompleteAudit; exact $complete _)
    | (rx_timer_head runOneSendWorkerAudit; exact $send)
    | (rx_timer_head runOneClearWorkerAudit; exact $clear)
    | (rx_timer_head RxHistory.runCryptWorkers; exact $crypt)
    | (rx_timer_head getWG; exact $stored _ (fun initial=>productGetWG_spec (fun s=>s=initial)))
    | (rx_timer_head modifyWG; exact $stored _ (fun initial=>productModifyWG_spec (fun s=>s=initial) _ (fun _=>rfl)))
    | (rx_timer_head Env.peekNextSite; exact $stored _ peekNextSite_sameKernel)
    | (rx_timer_head Env.deliverSent; exact $stored _ deliverSent_sameKernel)
    | (rx_timer_head throw; exact $stored _ (fun _=>hoare_throw _))
    | (audit_contract_head liftPrefix; exact $stored _ (fun initial=>productAmbient_spec _ _ (fun _ _ pre=>pre)))
    | (rx_timer_head Pure.pure; exact PrefixEnsures.pure $safe (fun _ _ pre=>pre))
    | (rx_timer_head ForIn.forIn; apply PrefixEnsures.rangeInvariant (State:=World)
        (I:=fun _ h w=>$inv h w) (hs:=fun _ h w pre=>$safe h w pre)))

/-- Local saved-aware variant of HolderAuxTimers.runTimers. The body is the
original observer; only the actual saved getter authorizes its wheel scan.
All account and identity leaf proofs are supplied separately. -/
theorem runTimers_preserves_saved_variant
    (safe : ∀ h w,I h w→S h)
    (store : ∀ h w v,productStoreView v=productStoreView w→I h w→I h v)
    (saved : PrefixEnsures I S (RxHistory.audit getDevSavedAudit)
      (fun d h w=>I h w ∧ SavedPeers d.peers.toList (identityView w.wg)))
    (wheel : ∀ d j,PrefixEnsures
      (fun h w=>I h w ∧ SavedPeers d.peers.toList (identityView w.wg))
      S (RxHistory.audit (wheelNextDueAudit d j)) (fun _=>I))
    (timer : ∀ worker pid kind entry prior,PrefixPreserves I S
      (RxHistory.audit (timerDispatchAudit worker pid kind entry prior)))
    (complete : ∀ bucket,PrefixPreserves I S (RxHistory.audit (requireStepCompleteAudit bucket)))
    (send : PrefixPreserves I S (RxHistory.audit runOneSendWorkerAudit))
    (clear : PrefixPreserves I S (RxHistory.audit runOneClearWorkerAudit))
    (crypt : PrefixPreserves I S RxHistory.runCryptWorkers)
    (j : UInt64) : PrefixPreserves I S (RxHistory.runTimers j) := by
  have stored {α : Type} (action : Leanux.M α) (frame : SameProductStore action) :
      PrefixPreserves I S (liftPrefix action) :=
    viewLiftPrefix_preserves productStoreView safe store frame
  apply PrefixEnsures.preserves
  unfold RxHistory.runTimers
  repeat' first
    | contradiction
    | timer_audit_stopped
    | (rx_timer_bound getDevSavedAudit; first
        | (deferred_saved_drop I; apply PrefixEnsures.bind saved)
        | apply PrefixEnsures.bind saved)
    | (rx_timer_bound wheelNextDueAudit; apply PrefixEnsures.bind (wheel _ _))
    | (deferred_saved_drop I; deferred_saved_calls I safe stored timer complete send clear crypt)
    | deferred_saved_calls I safe stored timer complete send clear crypt
    | (audit_contract_head Bind.bind; apply PrefixEnsures.bind (Q:=fun _=>I))
    | (deferred_saved_drop I; maintenance_join_let)
    | maintenance_join_let
    | (deferred_saved_drop I; maintenance_join_use)
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | (with_reducible split)
    | maintenance_intro

end Leanux.Proofs.WG.Index.DeferredRules
