import Leanux.Proofs.WG.AuthenticatedEffects.CausalScopePoll
import Leanux.Proofs.WG.AuthenticatedEffects.CausalScopeHandshake
import Leanux.Proofs.WG.AuthenticatedEffects.CausalScopeCompletion
import Leanux.Proofs.WG.Queues.SourceScheduler

/-! Actual worker iterations and the committed scheduler preserve normal scope
balance, including both NAPI entry paths and an interrupted consumer prefix. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.ScopeBalance
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity Lifetimes Queues
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

theorem softirq : ProductSafe (Driver.softirqObserved hooks) := by
  intro frames
  exact RxNapi.softirq_preserves
    (I := fun h _ => CausalScope.stack (h.filterMap scope?) = .ok frames)
    (S := CausalScope.WellFormed scope?) (fun _ _ ready => ⟨frames,ready⟩)
    (fun _ _ _ _ ready => ready) (product_state _ (state_lift _) frames)
    (fun pid budget => native_poll pid budget frames)

theorem inline_poll : ProductSafe (Driver.inlinePollObserved hooks) := by
  intro frames
  exact RxNapi.inline_preserves
    (I := fun h _ => CausalScope.stack (h.filterMap scope?) = .ok frames)
    (S := CausalScope.WellFormed scope?) (fun _ _ ready => ⟨frames,ready⟩)
    (fun _ _ _ _ ready => ready) (product_state _ (state_lift _) frames)
    (fun pid budget => native_poll pid budget frames)

theorem irq_exit : ProductSafe (Driver.irqExitObserved hooks) := by
  intro frames
  exact RxNapi.irqExit_preserves
    (I := fun h _ => CausalScope.stack (h.filterMap scope?) = .ok frames)
    (S := CausalScope.WellFormed scope?) (fun _ _ ready => ⟨frames,ready⟩)
    (fun _ _ _ _ ready => ready) (product_state _ (state_lift _) frames) (softirq frames)

theorem resched (worker : Worker) (site : Decision) : ProductSafe (Driver.reschedObserved worker site) :=
  product_bind (product_lift _) (fun _ => product_lift _)

theorem encrypt_tail (item : Option (List SkbId)) : ProductSafe (Driver.encryptTailObserved hooks item) := by
  intro frames
  exact workerIterPrefix_preserves .encryptWorker none (fun _ _ ready => ⟨frames,ready⟩)
    (old_product _ frames) (resched .encryptWorker .encWorkerNeedResched frames)

theorem encrypt_iter : ProductSafe (Driver.encryptIterObserved hooks) :=
  product_bind (old_product _) (fun item => product_bind softirq (fun _ => encrypt_tail item))

theorem tx_iter (pid : PeerId) : ProductSafe (Driver.txIterObserved hooks pid) := by
  intro frames
  exact workerIterPrefix_preserves .txWorker (some pid) (fun _ _ ready => ⟨frames,ready⟩)
    (transmit pid frames) (resched .txWorker .txNeedResched frames)

theorem decrypt_step : ProductSafe (Driver.decryptStepObserved hooks) := by
  unfold Driver.decryptStepObserved RxWorkers.decryptWith
  repeat' first
    | (scope_balance_head Driver.Hooks.prepare; exact old_product _)
    | (scope_balance_head Driver.softirqObserved; exact softirq)
    | (scope_balance_head Driver.irqExitObserved; exact irq_exit)
    | scope_product_step

theorem decrypt_iter : ProductSafe (Driver.decryptIterObserved hooks) := by
  intro frames
  exact workerIterPrefix_preserves .decryptWorker none (fun _ _ ready => ⟨frames,ready⟩)
    (decrypt_step frames) (resched .decryptWorker .decWorkerNeedResched frames)

theorem receive_iter : ProductSafe (Driver.receiveIterObserved hooks) := by
  intro frames
  exact workerIterPrefix_preserves .receiveWorker none (fun _ _ ready => ⟨frames,ready⟩)
    (product_state _ handshake_worker frames) (product_lift _ frames)

theorem crypt_ahead (pid : PeerId) : ProductSafe (Driver.cryptAheadObserved hooks pid) := by
  unfold Driver.cryptAheadObserved
  repeat' first
    | (scope_balance_head Driver.encryptIterObserved; exact encrypt_iter)
    | scope_product_step

theorem iteration (activation : Activation) : ProductSafe (Driver.iterationObserved hooks activation) := by
  unfold Driver.iterationObserved
  repeat' first
    | (scope_balance_head Driver.encryptIterObserved; exact encrypt_iter)
    | (scope_balance_head Driver.decryptIterObserved; exact decrypt_iter)
    | (scope_balance_head Driver.receiveIterObserved; exact receive_iter)
    | (scope_balance_head Driver.txIterObserved; exact tx_iter _)
    | (scope_balance_head Driver.cryptAheadObserved; exact crypt_ahead _)
    | scope_product_step

theorem schedule (stack : Option Worker) : ProductSafe (Driver.scheduleObserved hooks stack) := by
  intro frames
  apply SourceScheduler.schedule_preserves
    (I := fun h _ => CausalScope.stack (h.filterMap scope?) = .ok frames)
    (S := CausalScope.WellFormed scope?) (fun _ _ ready => ⟨frames,ready⟩)
    (fun _ _ _ _ ready => ready)
  · intro pid; exact product_lift _ frames
  · intro activation; exact iteration activation frames
  · exact softirq frames

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.ScopeBalance
