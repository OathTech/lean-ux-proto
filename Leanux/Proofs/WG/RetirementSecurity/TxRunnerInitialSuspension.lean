import Leanux.Proofs.WG.RetirementSecurity.TxSuspensionFibFrontend
import Leanux.Proofs.WG.RetirementSecurity.TxWorkDeviceLifetime

/-! Original fixture, prefill and FIB boot establish the first operation's
empty suspended list. Later entries use the actual completed-operation guard.
No invariant of an arbitrary routing action is assumed. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxWork.RunnerBoundary
open Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues Queues.RxCredits

theorem prefill_suspended {E : Type} (count : Nat) (w v : World) {h : List E}
    (run : runPrefixOuter (ConservationRunner.prefillWith count w
      (pure : World→PrefixOuter E World)) h=(.ok v,h)) :
    v.ambient.suspended=w.ambient.suspended := by
  unfold ConservationRunner.prefillWith at run
  split at run
  · split at run
    · cases run; rfl
    · cases run
  · cases run; rfl

theorem boot_suspended {E : Type} (net foreign : Bool) (w v : World) {h : List E}
    (run : runPrefixOuter (ConservationRunner.bootWith net foreign w
      (pure : World→PrefixOuter E World)) h=(.ok v,h)) :
    v.ambient.suspended=w.ambient.suspended := by
  unfold ConservationRunner.bootWith at run
  split at run
  · split at run
    · rename_i result actual
      cases run
      exact (ProjectedAction.iff_run _ _ _).mp (TxSuspension.Fib.boot_product foreign)
        w _ result actual
    · cases run
  · cases run; rfl

theorem initial_idle {E : Type} (trace : Trace) (placeholders : Bool) {u v : World} {h : List E}
    (prefill : runPrefixOuter (ConservationRunner.prefillWith trace.seccompPrefill
      (ConservationRunner.fixture trace placeholders) (pure : World→PrefixOuter E World)) h=(.ok u,h))
    (boot : runPrefixOuter (ConservationRunner.bootWith trace.net trace.foreign u
      (pure : World→PrefixOuter E World)) h=(.ok v,h)) : v.ambient.suspended=[] :=
  (boot_suspended trace.net trace.foreign u v boot).trans
    (prefill_suspended trace.seccompPrefill (ConservationRunner.fixture trace placeholders) u prefill)

theorem initialized_prefix_idle {E : Type} (call : Syscall→PrefixM E Int)
    (trace : Trace) (placeholders : Bool) (ops : List Operation)
    {u v : World} {h k : List E} {out : RunnerOperation.State}
    (prefill : runPrefixOuter (ConservationRunner.prefillWith trace.seccompPrefill
      (ConservationRunner.fixture trace placeholders) (pure : World→PrefixOuter E World)) h=(.ok u,h))
    (boot : runPrefixOuter (ConservationRunner.bootWith trace.net trace.foreign u
      (pure : World→PrefixOuter E World)) h=(.ok v,h))
    (prior : runPrefixOuter (forIn ops (v,#[],#[],#[],#[],#[])
      (RunnerOperation.operation call trace)) h=(.ok out,k)) :
    (RunnerOperation.prepare trace out).ambient.suspended=[] :=
  list call trace ops (v,#[],#[],#[],#[],#[]) (initial_idle trace placeholders prefill boot) prior

/-- Every actual operation entry in a normal initialized run has an empty
suspended list, including operation zero. The existential records its actual
prefill, boot and preceding operation prefix, rather than a fresh execution. -/
theorem normal_entries (trace : Trace) (placeholders : Bool)
    (run : runPrefixOuter (RunnerAccount.observed trace placeholders) []=(.ok (result,w),h))
    (index : Nat) (bound : index<trace.ops.size) :
    ∃u v op before j,
      runPrefixOuter (ConservationRunner.prefillWith trace.seccompPrefill
        (ConservationRunner.fixture trace placeholders) (pure : World→PrefixOuter RxHistory.Event World)) []=(.ok u,[]) ∧
      runPrefixOuter (ConservationRunner.bootWith trace.net trace.foreign u
        (pure : World→PrefixOuter RxHistory.Event World)) []=(.ok v,[]) ∧
      trace.ops.toList[index]?=some op ∧ before.2.1.size=index ∧
      runPrefixOuter (forIn (trace.ops.toList.take index) (v,#[],#[],#[],#[],#[])
        (RunnerOperation.operation RxHistory.syscall trace)) []=(.ok before,j) ∧
      (RunnerOperation.prepare trace before).ambient.suspended=[] := by
  obtain ⟨final,source,_⟩:=RunnerAccount.normal trace placeholders run
  obtain ⟨u,v,op,before,j,incoming,ret,returned,received,admitted,
    prefill,boot,position,indexEq,prior,_,_⟩:=
      RunnerInitializedCuts.account_cut trace placeholders source bound
  exact ⟨u,v,op,before,j,prefill,boot,position,indexEq,prior,
    initialized_prefix_idle RxHistory.syscall trace placeholders _ prefill boot prior⟩

end Leanux.Proofs.WG.RetirementSecurity.TxWork.RunnerBoundary
