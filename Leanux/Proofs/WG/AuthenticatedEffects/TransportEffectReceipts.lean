import Leanux.Proofs.WG.AuthenticatedEffects.TransportCarrierEffects
import Leanux.Proofs.WG.AuthenticatedEffects.CausalScopeContracts
import Leanux.Proofs.WG.AuthenticatedEffects.CausalEffectsFrames

/-! Concrete causal receipts and lexical markers preserve the initialized RX
carrier. The extra history predicate must accept exactly the added event;
there is no blanket assumption about arbitrary native state changes. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TransportCarrier
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues
variable {E Cause : Type} {extra : List E → Prop}
  {origin : E → Option TransportDriver.OriginEvent} {replay : E → Option TransportDriver.Replay}

private theorem quiet_append {h : List E} {w : WGWorld}
    (event : E) (ho : origin event = none) (hr : replay event = none)
    (he : ∀ h, extra h → extra (h ++ [event]))
    (hi : TransportPublication.Inv (h.filterMap origin) w ∧
      (TransportReplay.Safe origin replay h ∧ extra h)) :
    TransportPublication.Inv ((h ++ [event]).filterMap origin) w ∧
      (TransportReplay.Safe origin replay (h ++ [event]) ∧ extra (h ++ [event])) := by
  refine ⟨?_,hi.2.1.quiet (by simp only [List.filterMap_cons,List.filterMap_nil,hr]),he h hi.2.2⟩
  simpa only [List.filterMap_append,List.filterMap_cons,List.filterMap_nil,ho,List.append_nil] using hi.1

theorem causal_scope (record : CausalScope.Event Cause → E) (cause : Cause)
    (ho : ∀ event, origin (record event) = none)
    (hr : ∀ event, replay (record event) = none)
    (he : ∀ event h, extra h → extra (h ++ [record event]))
    (body : WGPrefix E α) (safe : StateSafe extra origin replay body) :
    StateSafe extra origin replay (CausalScope.scope record cause body) :=
  CausalScope.scope_preserves record cause body (fun _ _ _ hi => hi.2)
    (fun event _ _ _ hi => quiet_append (record event) (ho event) (hr event) (he event) hi) safe

theorem causal_current (decode : E → Option (CausalScope.Event Cause))
    (body : CausalEffects.Context Cause → WGPrefix E α)
    (safe : ∀ context, StateSafe extra origin replay (body context)) :
    StateSafe extra origin replay (CausalEffects.atCurrent decode body) :=
  fun w a h hi => safe (CausalScope.current decode h) w a h hi

theorem native_receipt (native : WG.M α) (frame : SameView RxDisposition.nativeRxStore native)
    (record : WGRunWitness α → E)
    (ho : ∀ r, origin (record r) = none) (hr : ∀ r, replay (record r) = none)
    (he : ∀ r h, extra h → extra (h ++ [record r])) :
    StateSafe extra origin replay (receiptWGObserved (liftWGPrefix native) record) := by
  unfold receiptWGObserved
  apply StatePrefixEnsures.bind (StatePrefixPreserves.captureWGObserved (state_rx native frame))
  intro r
  have emitted : StateSafe extra origin replay (emitStatePrefix (record r)) :=
    StatePrefixEnsures.emit (record r)
      (fun _ _ _ hi => (quiet_append (record r) (ho r) (hr r) (he r) hi).2)
      (fun _ _ _ hi => quiet_append (record r) (ho r) (hr r) (he r) hi)
  exact StatePrefixEnsures.bind emitted (fun _ => state_pure r.value)

theorem causal_arm (decode : E → Option (CausalScope.Event Cause))
    (record : TimerEffects.Arm (CausalEffects.Context Cause) → E)
    (ho : ∀ r, origin (record r) = none) (hr : ∀ r, replay (record r) = none)
    (he : ∀ r h, extra h → extra (h ++ [record r]))
    (pid : PeerId) (timer : PeerTimer) (delay : Nat) (caller : Option UInt64) :
    StateSafe extra origin replay
      (CausalEffects.atCurrent decode fun context => TimerEffects.armReceipt record context pid timer delay caller) :=
  causal_current decode _ (fun context => native_receipt _ (effect_arm_rx pid timer delay caller)
    (fun r => record ⟨context,pid,timer,delay,caller,r⟩) (fun _ => ho _) (fun _ => hr _) (fun _ => he _))

private theorem queue_rx (pid : PeerId) :
    SameView RxDisposition.nativeRxStore
      (modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]}) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a x v b run
  cases run
  simp only [RxDisposition.nativeRxStore,Option.map_map,Function.comp_def]
  cases w.dev <;> rfl

theorem causal_queue (decode : E → Option (CausalScope.Event Cause))
    (record : TimerEffects.Queued (CausalEffects.Context Cause) → E)
    (ho : ∀ r, origin (record r) = none) (hr : ∀ r, replay (record r) = none)
    (he : ∀ r h, extra h → extra (h ++ [record r])) (pid : PeerId) :
    StateSafe extra origin replay
      (CausalEffects.atCurrent decode fun context => TimerEffects.queueReceipt record context pid) :=
  causal_current decode _ (fun context => native_receipt _ (queue_rx pid)
    (fun r => record ⟨context,pid,r⟩) (fun _ => ho _) (fun _ => hr _) (fun _ => he _))

end Leanux.Proofs.WG.AuthenticatedEffects.TransportCarrier
