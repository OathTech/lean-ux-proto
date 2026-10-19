import Leanux.Proofs.WG.AuthenticatedEffects.ReplayEntryControl
import Leanux.Proofs.WG.TransmitSecurity.DriverGroNeutral

/-! Replay-entry coherence at the actual poll callback and its stack/NAPI
callers. A stopped consumer retains the completed counter-entry receipt. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.ReplayEntry
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues Keypairs TransmitSecurity.Driver
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

theorem stack (bytes : List UInt8) : ProductSafe (stackObserved hooks bytes) :=
  product_observed _ _ (stack_erases bytes)
    (stack_history (quiet_history Safe).core bytes) (EnvFrames.receive_ordinary bytes)

theorem flush (packets : List (List UInt8)) : ProductSafe (stackFlushObserved hooks packets) := by
  induction packets with
  | nil => exact product_pure _
  | cons packet rest ih =>
    simp only [stackFlushObserved,List.forM_eq_forM,List.forM_cons] at ih ⊢
    exact product_bind (stack packet) (fun _ => ih)

theorem gro_receive (callback : List (List UInt8) → PrefixM Event Unit)
    (safe : ∀ packets, ProductSafe (callback packets)) (gro : GroState) (bytes : List UInt8) :
    ProductSafe (napiGroReceivePrefix callback gro bytes) :=
  napiGroReceivePrefix_preserves callback (fun _ _ hi => hi.2) safe gro bytes

theorem gro_flush (callback : List (List UInt8) → PrefixM Event Unit)
    (safe : ∀ packets, ProductSafe (callback packets)) (gro : GroState) :
    ProductSafe (napiGroFlushAllPrefix callback gro) :=
  napiGroFlushAllPrefix_preserves callback (fun _ _ hi => hi.2) safe gro

theorem poll (pid : PeerId) (budget : Nat) (callback : List (List UInt8) → PrefixM Event Unit)
    (safe : ∀ packets, ProductSafe (callback packets)) : ProductSafe (pollObserved hooks pid budget callback) := by
  unfold pollObserved CandidatePoll.sourceWith
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | (replay_entry_head Hooks.candidateEnter; exact product_pure _)
    | (replay_entry_head Hooks.candidateLeave; exact product_pure _)
    | (replay_entry_head Hooks.counterCheck; exact counter _ _)
    | (replay_entry_head consumeObserved; exact product_state (consume _ _ _))
    | (replay_entry_head napiGroReceivePrefix; exact gro_receive callback safe _ _)
    | (replay_entry_head napiGroFlushAllPrefix; exact gro_flush callback safe _)
    | replay_entry_native_step
    | replay_entry_product_step

theorem native_poll (pid : PeerId) (budget : Nat) : ProductSafe (nativePollObserved hooks pid budget) := by
  rw [nativePoll_neutral hooks rfl rfl]
  exact poll pid budget _ flush

private theorem pending : SameSnapshot RxNapi.pendingSource := by
  unfold RxNapi.pendingSource
  apply SameView.bind WGFrames.getDev_sameSnapshot
  intro d
  exact SameView.pure _ _

private theorem scheduled : SameSnapshot RxNapi.scheduledSource := by
  unfold RxNapi.scheduledSource
  apply SameView.bind WGFrames.getDev_sameSnapshot
  intro d
  exact SameView.pure _ _

theorem softirq : ProductSafe (softirqObserved hooks) :=
  RxNapi.softirq_preserves (fun _ _ hi => hi.2) product_store
    (product_state (state_same _ pending)) native_poll

theorem inline_poll : ProductSafe (inlinePollObserved hooks) :=
  RxNapi.inline_preserves (fun _ _ hi => hi.2) product_store
    (product_state (state_same _ pending)) native_poll

theorem irq_exit : ProductSafe (irqExitObserved hooks) :=
  RxNapi.irqExit_preserves (fun _ _ hi => hi.2) product_store
    (product_state (state_same _ scheduled)) softirq

end Leanux.Proofs.WG.AuthenticatedEffects.ReplayEntry
