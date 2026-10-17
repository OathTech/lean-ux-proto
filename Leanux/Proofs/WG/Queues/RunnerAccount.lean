import Leanux.Proofs.WG.Queues.ConservationRunner
import Leanux.Proofs.WG.Queues.ConservationSyscall
import Leanux.Proofs.WG.Queues.JointRunnerProjection
import Leanux.Proofs.WG.Origins.OwnerRunner

/-! Initialized source-selected receive accounts for the original runner.
This endpoint claim retains residual carriers. Packet-fate classification and
global multiplicity are separate claims, not consequences of funding alone. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.RunnerAccount
open Lean Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged

/-- The existing factored runner with its actual returned World retained. -/
def observed (trace : Trace) (placeholders : Bool) : PrefixOuter RxHistory.Event (Json × World) :=
  RoutingJoint.executeTraceWith RxHistory.syscall (fun j w=>(j,w)) trace placeholders

def certified (trace : Trace) (placeholders : Bool) :
    ConservationCertified.Certified (observed trace placeholders)
      (fun cs h=>cs=[] ∧ h=[]) (fun out cs h=>HolderEntry.Inv cs [] h out.2) :=
  ConservationRunner.initialized RxHistory.syscall ConservationSyscall.rule
    ConservationSyscall.established trace placeholders

def rule (trace : Trace) (placeholders : Bool) : ConservationOuter.Rule (observed trace placeholders) :=
  (certified trace placeholders).rule

/-- Dropping the returned World gives exactly the existing RX history
observer, including indexed errors and every retained journal event. -/
theorem correspondence (trace : Trace) (placeholders : Bool) (h : List RxHistory.Event) :
    runPrefixOuter (RxHistory.executeTraceHistory trace placeholders) h =
      ((runPrefixOuter (observed trace placeholders) h).1.map Prod.fst,
        (runPrefixOuter (observed trace placeholders) h).2) := by
  have self (c : Syscall) : ProjectsPrefix some id (RxHistory.syscall c) (RxHistory.syscall c) := by
    intro w h
    simp only [List.filterMap_some]
    cases actual : runPrefix (RxHistory.syscall c) w h with
    | mk result journal=>cases result <;> rfl
  have proof := RoutingJoint.executeTraceWith_projects some Prod.fst
    RxHistory.syscall RxHistory.syscall (fun j w=>(j,w)) (fun j _=>j)
    self (fun _ _=>rfl) trace placeholders h
  simpa only [List.filterMap_some,RxHistory.executeTraceHistory,
    RoutingJoint.executeTrace_rx_factor,observed] using proof

/-- The executable runner has the identical JSON or indexed Stop. -/
theorem json (trace : Trace) (placeholders : Bool) (h : List RxHistory.Event) :
    (runPrefixOuter (observed trace placeholders) h).1.map Prod.fst=
      Runner.executeTrace trace placeholders :=
  (congrArg Prod.fst (correspondence trace placeholders h)).symm.trans
    (RxHistory.executeTraceHistory_erases trace placeholders h)

/-- Every normal initialized return derives its concrete source certificate
and funded residual entry. Neither is an input premise. -/
theorem normal (trace : Trace) (placeholders : Bool)
    (run : runPrefixOuter (observed trace placeholders) []=(.ok (result,v),h)) :
    ∃next,(rule trace placeholders).relation [] [] (result,v) h next ∧ HolderEntry.Inv next [] h v :=
  (certified trace placeholders).establishes ⟨rfl,rfl⟩ run

theorem unique (trace : Trace) (placeholders : Bool)
    (left : (rule trace placeholders).relation [] [] out h cs)
    (right : (rule trace placeholders).relation [] [] out h next) : cs=next :=
  (rule trace placeholders).unique left right

/-- A successful original history observer has the same actual endpoint
World and source-selected account; the endpoint is recovered from its run. -/
theorem history_normal (trace : Trace) (placeholders : Bool)
    (run : runPrefixOuter (RxHistory.executeTraceHistory trace placeholders) []=(.ok result,h)) :
    ∃v next,runPrefixOuter (observed trace placeholders) []=(.ok (result,v),h) ∧
      (rule trace placeholders).relation [] [] (result,v) h next ∧ HolderEntry.Inv next [] h v := by
  have source := (correspondence trace placeholders []).symm.trans run
  cases actual : runPrefixOuter (observed trace placeholders) [] with
  | mk outcome journal=>
    rw [actual] at source
    cases outcome with
    | error reason=>cases source
    | ok out=>
      cases source
      obtain ⟨next,certificate,entry⟩ := normal trace placeholders actual
      exact ⟨out.2,next,rfl,certificate,entry⟩

/-- Acceptance by the executable runner supplies the same original history
and returned World. This states a residual account, not empty completion. -/
theorem accepted (trace : Trace) (placeholders : Bool)
    (run : Runner.executeTrace trace placeholders=.ok result) :
    ∃v h next,runPrefixOuter (observed trace placeholders) []=(.ok (result,v),h) ∧
      (rule trace placeholders).relation [] [] (result,v) h next ∧ HolderEntry.Inv next [] h v := by
  have source := (json trace placeholders []).trans run
  cases actual : runPrefixOuter (observed trace placeholders) [] with
  | mk outcome journal=>
    rw [actual] at source
    cases outcome with
    | error reason=>cases source
    | ok out=>
      cases source
      obtain ⟨next,certificate,entry⟩ := normal trace placeholders actual
      exact ⟨out.2,journal,next,rfl,certificate,entry⟩

/-- Stopped executions retain the actual owner-safe journal. A failed World
or completed receive ledger is not manufactured. -/
theorem owner_safe (trace : Trace) (placeholders : Bool) :
    OwnerChecks.Safe (runPrefixOuter (observed trace placeholders) []).2 := by
  have same := congrArg Prod.snd (correspondence trace placeholders [])
  rw [←same]
  exact OwnerRunner.executeTrace trace placeholders

end Leanux.Proofs.WG.Queues.RxCredits.RunnerAccount
