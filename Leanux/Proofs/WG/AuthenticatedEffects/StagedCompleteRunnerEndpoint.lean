import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRunnerEndpointFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRunnerInitialFrames

/-! A normal initialized execution retains its invariant on the actual
returned World. Stop retains only the specified history predicate; this
module supplies no unrecorded state for a failed computation. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteRunner
open Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues Queues.RxCredits RetirementSecurity
variable {E : Type}

theorem initialized_endpoint (I J : List E → World → Prop) (S : List E → Prop)
    (empty : S []) (safe : ∀ h w, I h w → S h)
    (prepare : ∀ trace state h, I h state.1 → I h (RunnerOperation.prepare trace state))
    (close : ∀ h w v, v.wg=w.wg → v.ambient.suspended=[] → w.ambient.suspended=[] →
      J h w → I h v)
    (call : Syscall → PrefixM E Int)
    (calls : ∀ c, PrefixEnsures I S (call c) (fun _ => J))
    (trace : Trace) (placeholders : Bool)
    (initial : ∀ w, wgStoreView w.wg=wgStoreView (initialWG trace.net trace.bare) →
      w.ambient.suspended=[] → I [] w) :
    (match runPrefixOuter (RoutingJoint.executeTraceWith call (fun j v => (j,v)) trace placeholders) [] with
    | (.ok out,h) => I h out.2
    | (.error _,h) => S h) := by
  change (match runPrefixOuter (ConservationRunner.prefillWith trace.seccompPrefill
    (ConservationRunner.fixture trace placeholders) (fun w =>
      ConservationRunner.bootWith trace.net trace.foreign w
        (RoutingJoint.runnerTailWith call (fun j v => (j,v)) trace))) [] with
    | (.ok out,h) => I h out.2
    | (.error _,h) => S h)
  rw [prefill_factor,runPrefixOuter_bind]
  have prequiet := prefill_quiet (E:=E) trace.seccompPrefill (ConservationRunner.fixture trace placeholders) []
  cases pref : runPrefixOuter (ConservationRunner.prefillWith trace.seccompPrefill
      (ConservationRunner.fixture trace placeholders) (pure : World → PrefixOuter E World)) [] with
  | mk outcome h =>
    rw [pref] at prequiet
    change h=[] at prequiet
    subst h
    cases outcome with
    | error reason => exact empty
    | ok u =>
      dsimp only
      rw [boot_factor,runPrefixOuter_bind]
      have bootquiet := boot_quiet (E:=E) trace.net trace.foreign u []
      cases boot : runPrefixOuter (ConservationRunner.bootWith trace.net trace.foreign u
          (pure : World → PrefixOuter E World)) [] with
      | mk result h =>
        rw [boot] at bootquiet
        change h=[] at bootquiet
        subst h
        cases result with
        | error reason => exact empty
        | ok v =>
          dsimp only
          have store := (boot_store trace.net trace.foreign u v boot).trans
            (prefill_store trace.seccompPrefill (ConservationRunner.fixture trace placeholders) u pref)
          have before := initial v store (TxWork.RunnerBoundary.initial_idle trace placeholders pref boot)
          have checked := (prefixOuter_wp_iff _ _ _ _).mp
            (tail_endpoint I J S safe prepare close call calls trace v) [] before
          cases source : runPrefixOuter (RoutingJoint.runnerTailWith call (fun j v => (j,v)) trace v) [] with
          | mk outcome h =>
            rw [source] at checked
            cases outcome <;> exact checked

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteRunner
