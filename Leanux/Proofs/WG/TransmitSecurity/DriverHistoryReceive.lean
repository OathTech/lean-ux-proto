import Leanux.Proofs.WG.TransmitSecurity.DriverHistoryStaging

namespace Leanux.Proofs.WG.TransmitSecurity.Driver
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open HandshakeSecurity.Confirmation.Poll
variable {E : Type} {Safe : List E → Prop} {g : Hooks E}
set_option maxHeartbeats 600000
set_option pp.structureInstances false

private theorem normalList (cb : List (List UInt8) → PrefixM E Unit)
    (hc : ∀ ps, ProductHistorySafe Safe (cb ps)) (gro : GroState) :
    ProductHistorySafe Safe (groNormalListPrefix cb gro) := by
  unfold groNormalListPrefix
  repeat' first | exact hc _ | driver_product_history_step

private theorem normalOne (cb : List (List UInt8) → PrefixM E Unit)
    (hc : ∀ ps, ProductHistorySafe Safe (cb ps)) (gro : GroState) (pkt : List UInt8) (segs : Nat) :
    ProductHistorySafe Safe (groNormalOnePrefix cb gro pkt segs) := by
  unfold groNormalOnePrefix
  repeat' first
    | (driver_history_head groNormalListPrefix; exact normalList cb hc _)
    | driver_product_history_step

private theorem groReceive (cb : List (List UInt8) → PrefixM E Unit)
    (hc : ∀ ps, ProductHistorySafe Safe (cb ps)) (gro : GroState) (pkt : List UInt8) :
    ProductHistorySafe Safe (napiGroReceivePrefix cb gro pkt) := by
  unfold napiGroReceivePrefix
  repeat' first
    | (driver_history_head groNormalOnePrefix; exact normalOne cb hc _ _ _)
    | driver_product_history_step

private theorem groFlush (cb : List (List UInt8) → PrefixM E Unit)
    (hc : ∀ ps, ProductHistorySafe Safe (cb ps)) (gro : GroState) :
    ProductHistorySafe Safe (napiGroFlushAllPrefix cb gro) := by
  unfold napiGroFlushAllPrefix
  repeat' first
    | (driver_history_head groNormalOnePrefix; exact normalOne cb hc _ _ _)
    | (driver_history_head groNormalListPrefix; exact normalList cb hc _)
    | driver_product_history_step

theorem poll_history (h : ActorHistorySafe Safe g) (pid : PeerId) (budget : Nat)
    (cb : List (List UInt8) → PrefixM E Unit)
    (hc : ∀ ps, ProductHistorySafe Safe (cb ps)) :
    ProductHistorySafe Safe (pollObserved g pid budget cb) := by
  unfold pollObserved AuthenticatedEffects.CandidatePoll.sourceWith
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | (driver_history_head Hooks.candidateEnter; exact h.candidateEnter _ _)
    | (driver_history_head Hooks.candidateLeave; exact h.candidateLeave _)
    | (driver_history_head Hooks.counterCheck; exact h.counterCheck _ _)
    | (driver_history_head consumeObserved; exact (consume_history h _ _ _).liftWGObserver)
    | (driver_history_head liftWGPrefix; exact (History.state_lift _).liftWGObserver)
    | (driver_history_head napiGroReceivePrefix; exact groReceive cb hc _ _)
    | (driver_history_head napiGroFlushAllPrefix; exact groFlush cb hc _)
    | driver_product_history_step

private theorem reply_history (h : ActorHistorySafe Safe g) (dst : Nat) (bytes : List UInt8) :
    ProductHistorySafe Safe (reply4With (fun family addr packets mtu => liftWGObserver (transmitObserved g family addr packets mtu)) dst bytes) := by
  unfold reply4With
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (driver_history_head transmitObserved; exact (transmit_history h _ _ _ _).liftWGObserver)
    | driver_product_history_step

private theorem receive4_history (h : ActorHistorySafe Safe g) (bytes : List UInt8) :
    ProductHistorySafe Safe (receive4With (reply4With (fun family addr packets mtu => liftWGObserver (transmitObserved g family addr packets mtu))) bytes) :=
  receive4With_preserves (I := fun h _ => Safe h) (S := Safe) (fun _ _ hi => hi) (fun _ _ _ _ hi => hi) _ (reply_history h) bytes

theorem stack_history (h : ActorHistorySafe Safe g) (bytes : List UInt8) :
    ProductHistorySafe Safe (stackObserved g bytes) := by
  unfold stackObserved stackReceiveWith
  repeat' first
    | (driver_history_head receive4With; exact receive4_history h _)
    | driver_product_history_step

theorem flush_actor_history (h : ActorHistorySafe Safe g) (ps : List (List UInt8)) :
    ProductHistorySafe Safe (stackFlushObserved g ps) := by
  induction ps with
  | nil => exact History.product_pure _
  | cons p ps ih =>
    simp only [stackFlushObserved,List.forM_eq_forM,List.forM_cons] at ih ⊢
    exact History.product_bind (stack_history h p) (fun _ => ih)

theorem nativePoll_history (h : ActorHistorySafe Safe g) (pid : PeerId) (budget : Nat) :
    ProductHistorySafe Safe (nativePollObserved g pid budget) :=
  poll_history h pid budget _ (flush_actor_history h)

theorem softirq_history (h : ActorHistorySafe Safe g) :
    ProductHistorySafe Safe (softirqObserved g) := by
  unfold softirqObserved RxNapi.softirqWith runWorkerPrefix
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (driver_history_head nativePollObserved; exact nativePoll_history h _ _)
    | (driver_history_head liftWGPrefix; exact (History.state_lift _).liftWGObserver)
    | driver_product_history_step

theorem inline_history (h : ActorHistorySafe Safe g) :
    ProductHistorySafe Safe (inlinePollObserved g) := by
  unfold inlinePollObserved RxNapi.inlineWith
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (driver_history_head nativePollObserved; exact nativePoll_history h _ _)
    | (driver_history_head liftWGPrefix; exact (History.state_lift _).liftWGObserver)
    | driver_product_history_step

theorem irqExit_history (h : ActorHistorySafe Safe g) :
    ProductHistorySafe Safe (irqExitObserved g) := by
  unfold irqExitObserved RxNapi.irqExitWith
  repeat' first
    | (driver_history_head softirqObserved; exact softirq_history h)
    | (driver_history_head liftWGPrefix; exact (History.state_lift _).liftWGObserver)
    | driver_product_history_step

theorem flush_history (h : HooksHistorySafe Safe g) (ps : List (List UInt8)) :
    ProductHistorySafe Safe (stackFlushObserved g ps) := flush_actor_history h.actors ps

end Leanux.Proofs.WG.TransmitSecurity.Driver
