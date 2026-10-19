import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixRunnerClosed
import Leanux.Proofs.WG.Queues.RunnerOperationCuts

/-! Fixed initialized operation prefixes retain the actual accumulator and
history produced by prefill, boot and the original take-prefix loop. The
certificate applies even when a later operation stops. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.RunnerSource
open Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues Queues.RxCredits RetirementSecurity TransmitSecurity
open CompleteRunner

/-- This is the exact initialization and ordered operation prefix, with the
original trace still supplying hidden inputs and descriptor conversion. -/
def operationPrefix (trace : Trace) (placeholders : Bool) (count : Nat) :
    PrefixOuter CausalJournal.Event RunnerOperation.State :=
  ConservationRunner.prefillWith trace.seccompPrefill
    (ConservationRunner.fixture trace placeholders) (fun w=>
      ConservationRunner.bootWith trace.net trace.foreign w (fun v=>
        forIn (trace.ops.toList.take count) (v,#[],#[],#[],#[],#[])
          (RunnerOperation.operation (Driver.syscallObserved CausalJournal.hooks) trace)))

/-- Successful prefixes keep their actual native state; stopped prefixes
retain every logical journal certificate without inventing a failed state. -/
theorem operation_prefix (trace : Trace) (placeholders : Bool) (count : Nat) :
    match runPrefixOuter (operationPrefix trace placeholders count) [] with
    | (.ok state,h)=>CompletePrefix.Runner.Entry h state.1
    | (.error _,h)=>CompletePrefix.All CompleteProduct.Safe h := by
  unfold operationPrefix
  rw [prefill_factor,runPrefixOuter_bind]
  have prequiet := prefill_quiet (E:=CausalJournal.Event) trace.seccompPrefill
    (ConservationRunner.fixture trace placeholders) []
  cases pref : runPrefixOuter (ConservationRunner.prefillWith trace.seccompPrefill
      (ConservationRunner.fixture trace placeholders)
      (pure : World→PrefixOuter CausalJournal.Event World)) [] with
  | mk outcome h=>
    rw [pref] at prequiet
    change h=[] at prequiet
    subst h
    cases outcome with
    | error reason=>exact CompletePrefix.All.nil empty_safe
    | ok u=>
      dsimp only
      rw [boot_factor,runPrefixOuter_bind]
      have bootquiet := boot_quiet (E:=CausalJournal.Event) trace.net trace.foreign u []
      cases boot : runPrefixOuter (ConservationRunner.bootWith trace.net trace.foreign u
          (pure : World→PrefixOuter CausalJournal.Event World)) [] with
      | mk result h=>
        rw [boot] at bootquiet
        change h=[] at bootquiet
        subst h
        cases result with
        | error reason=>exact CompletePrefix.All.nil empty_safe
        | ok v=>
          dsimp only
          have store := (boot_store trace.net trace.foreign u v boot).trans
            (prefill_store trace.seccompPrefill (ConservationRunner.fixture trace placeholders) u pref)
          have before := CompletePrefix.Runner.initial trace.net trace.bare v store
            (TxWork.RunnerBoundary.initial_idle trace placeholders pref boot)
          have checked := (prefixOuter_wp_iff _ _ _ _).mp
            (operations CompletePrefix.Runner.Entry CompletePrefix.Runner.Exit
              (CompletePrefix.All CompleteProduct.Safe) CompletePrefix.Runner.prepare
              CompletePrefix.Runner.close (Driver.syscallObserved CausalJournal.hooks)
              CompletePrefix.Runner.syscall trace (trace.ops.toList.take count)
              (v,#[],#[],#[],#[],#[])) [] before
          cases source : runPrefixOuter
              (forIn (trace.ops.toList.take count) (v,#[],#[],#[],#[],#[])
                (RunnerOperation.operation (Driver.syscallObserved CausalJournal.hooks) trace)) [] with
          | mk outcome h=>
            rw [source] at checked
            cases outcome <;> exact checked

/-- The next syscall entry is obtained from the actual completed operation
prefix; its ledger and native companions are derived from initialization. -/
theorem prepared_entry (trace : Trace) (placeholders : Bool) (count : Nat)
    (run : runPrefixOuter (operationPrefix trace placeholders count) []=(.ok state,history)) :
    CompletePrefix.Runner.Entry history (RunnerOperation.prepare trace state) := by
  have before := operation_prefix trace placeholders count
  rw [run] at before
  exact CompletePrefix.Runner.prepare trace state history before

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.RunnerSource
