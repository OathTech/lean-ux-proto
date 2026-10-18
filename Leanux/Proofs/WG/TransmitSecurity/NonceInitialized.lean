import Leanux.Proofs.WG.TransmitSecurity.NonceSyscalls
import Leanux.Proofs.WG.Origins.RunnerInvariant

/-! Sending-counter reservations on every typed execution of the original
initialized Runner. Counter allocation is distinct from AEAD execution. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Nonce
open Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

def executeObserved (trace : Trace) (placeholders : Bool) : PrefixOuter Allocation Lean.Json :=
  RxHistory.executeTraceWith syscallObserved trace placeholders

theorem initialized_safe (trace : Trace) (placeholders : Bool) :
    List.Nodup (runPrefixOuter (executeObserved trace placeholders) []).2 := by
  apply RunnerInvariant.executeTraceWith (fun h w => Inv (view w.wg) h) List.Nodup
    (fun _ _ hi => hi.nodup) Frames.wg_store syscallObserved syscallObserved_safe trace placeholders
  intro w same
  apply Frames.wg_store [] {w with wg := initialWG trace.net trace.bare} w same
  change Inv (view (initialWG trace.net trace.bare)) []
  rw [initial_view]
  exact initial 0

macro "nonce_pinned_unfold " n:ident : tactic => do
  pure (← `(tactic| unfold $(Lean.mkCIdent (normalizePinnedName n.getId))))

private theorem tail_erases (trace : Trace) (w : World) :
    ErasesOuter (RxHistory.runnerTail syscallObserved trace w)
      ((pinned_const _private.Leanux.Proofs.WG.Queues.RxRunnerHistory.«0».Leanux.Proofs.WG.Queues.RxHistory.runnerHistorySourceTail) trace w) := by
  unfold RxHistory.runnerTail
  nonce_pinned_unfold _private.Leanux.Proofs.WG.Queues.RxRunnerHistory.«0».Leanux.Proofs.WG.Queues.RxHistory.runnerHistorySourceTail
  repeat' first
    | (maintenance_head syscallObserved; exact syscallObserved_erases _)
    | audit_runner_erasure_step

macro "nonce_native_runner" : term => do
  let n := Lean.mkCIdent (normalizePinnedName
    `_private.Leanux.Proofs.WG.Queues.RxRunnerHistory.«0».Leanux.Proofs.WG.Queues.RxHistory.runnerHistorySource)
  `(@$n)

private def nativeRunner : Trace → Bool → Except (Nat × Stop) Lean.Json := nonce_native_runner

/-- Exact JSON and indexed Stop, for arbitrary input history as well as the
initialized empty journal. The source contains no observer-driven branches. -/
theorem executeObserved_erases (trace : Trace) (placeholders : Bool) :
    ErasesOuter (executeObserved trace placeholders) (Runner.executeTrace trace placeholders) := by
  change ErasesOuter (executeObserved trace placeholders)
    (nativeRunner trace placeholders)
  unfold executeObserved RxHistory.executeTraceWith nativeRunner
  nonce_pinned_unfold _private.Leanux.Proofs.WG.Queues.RxRunnerHistory.«0».Leanux.Proofs.WG.Queues.RxHistory.runnerHistorySource
  by_cases hp : trace.seccompPrefill > 0
  all_goals simp only [hp, ↓reduceIte]
  all_goals cases (Env.seccompPrefill trace.seccompPrefill ({} : SeccompWorld)
    (initialTasks trace.rlimit trace.foreign trace.stepped trace.seccompChild))
  all_goals repeat' first
    | (maintenance_head RxHistory.runnerTail; exact tail_erases _ _)
    | audit_runner_erasure_step

end Leanux.Proofs.WG.TransmitSecurity.Nonce
