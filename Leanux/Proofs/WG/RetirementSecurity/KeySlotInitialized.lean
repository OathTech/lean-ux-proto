import Leanux.Proofs.WG.RetirementSecurity.KeySlotSyscall
import Leanux.Proofs.WG.RetirementSecurity.OccurrenceJournalOuter
import Leanux.Proofs.WG.Origins.NormalRunnerInvariant

/-! Initialized live-slot protection on the original runner and the shared
campaign journal. Retaining the successful World uses the existing generic
runner result projection, not a different schedule or execution spine. -/
namespace Leanux.Proofs.WG.RetirementSecurity.KeySlotInitialized
open Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues Queues.RxCredits TransmitSecurity

/-- Initialization and all actual native syscalls derive slot liveness with
no incoming invariant, funding or source-coverage premise. -/
theorem normal (trace : Trace) (placeholders : Bool)
    (run : runPrefixOuter (RunnerAccount.observed trace placeholders) []=(.ok (result,w),h)) :
    KeySlotLiveness.Inv w.wg := by
  exact RunnerInvariant.Normal.executeTraceWith_normal KeySlotTraffic.Inv (fun _=>True)
    (fun _ _ _=>True.intro) (fun _ _ _ same before=>KeySlotTraffic.wg_store same before)
    RxHistory.syscall KeySlotSyscall.syscall trace placeholders
    (fun _ same=>KeySlotLiveness.store_transport same (KeySlotLiveness.initial trace.net trace.bare)) run

/-- Every actual surviving published slot in a normal initialized execution
has independently funded stamped peer protection. This derives peer funding;
the separate key-reference ledger is not asserted by this theorem. -/
theorem slot_protection (trace : Trace) (placeholders : Bool)
    (run : runPrefixOuter (RunnerAccount.observed trace placeholders) []=(.ok (result,w),h)) :
    ∃carriers holders,holders.Funded carriers [] w.wg ∧ StableRx carriers w.wg ∧
      SlotPeerReferences holders [] w.wg := by
  obtain ⟨carriers,_,entry⟩ := RunnerAccount.normal trace placeholders run
  obtain ⟨holders,funded,stable⟩ := entry.1.1.1
  exact ⟨carriers,holders,funded,stable,
    KeySlotLiveness.references (normal trace placeholders run) funded entry.1.1.2.1 entry.1.1.2.2⟩

def JournalInv (h : List Journal.Event) (w : World) : Prop :=
  OccurrencePollJournal.Inv [] h w ∧ KeySlotLiveness.Inv w.wg

theorem journal_call (call : Syscall) :
    PrefixPreserves JournalInv OccurrencePollJournal.Safe (Driver.syscallObserved Journal.hooks call) := by
  intro w h before
  obtain ⟨suffix,history,safe,post⟩ := OccurrencePollJournal.syscall call w h before.1
  refine ⟨suffix,history,safe,?_⟩
  cases run : (runPrefix (Driver.syscallObserved Journal.hooks call) w h).1 with
  | error reason=>trivial
  | ok out=>
    rw [run] at post
    have projected := Driver.syscall_projects Journal.hooks_projects call
    rw [Driver.nonce_syscallObserved_eq] at projected
    exact ⟨post,(hoare_iff_run _ _ _).mp (KeySlotSyscall.syscall_native call) w out.1 out.2 before.2
      (DriverOwnership.product_native projected (Nonce.syscallObserved_erases call) w out.2 h run)⟩

/-- The same campaign driver derives live slots and physical poll ownership
from actual initialization. Its original successful World is retained solely
by the existing runner's result callback. -/
theorem journal_normal (trace : Trace) (placeholders : Bool)
    (run : runPrefixOuter (RoutingJoint.executeTraceWith (Driver.syscallObserved Journal.hooks)
      (fun j w=>(j,w)) trace placeholders) []=(.ok (result,w),h)) : JournalInv h w := by
  apply RunnerInvariant.Normal.executeTraceWith_normal JournalInv OccurrencePollJournal.Safe
    (fun _ _ before=>before.1.2) _ (Driver.syscallObserved Journal.hooks) journal_call trace placeholders _ run
  · intro _ _ _ same before
    exact ⟨OccurrencePollJournal.product_wg_store _ _ _ same before.1,
      KeySlotLiveness.store_transport same before.2⟩
  · intro w same
    refine ⟨⟨OccurrenceStack.ready_store same (OccurrenceLifecycle.initial trace.net trace.bare),?_⟩,
      KeySlotLiveness.store_transport same (KeySlotLiveness.initial trace.net trace.bare)⟩
    intro receipt member
    cases member

theorem journal_correspondence (trace : Trace) (placeholders : Bool) (h : List Journal.Event) :
    runPrefixOuter (Journal.execute trace placeholders) h =
      ((runPrefixOuter (RoutingJoint.executeTraceWith (Driver.syscallObserved Journal.hooks)
        (fun j w=>(j,w)) trace placeholders) h).1.map Prod.fst,
       (runPrefixOuter (RoutingJoint.executeTraceWith (Driver.syscallObserved Journal.hooks)
        (fun j w=>(j,w)) trace placeholders) h).2) := by
  have self (c : Syscall) : ProjectsPrefix some id
      (Driver.syscallObserved Journal.hooks c) (Driver.syscallObserved Journal.hooks c) := by
    intro w h
    simp only [List.filterMap_some]
    cases actual : runPrefix (Driver.syscallObserved Journal.hooks c) w h with
    | mk result journal=>cases result <;> rfl
  have proof := RoutingJoint.executeTraceWith_projects some Prod.fst
    (Driver.syscallObserved Journal.hooks) (Driver.syscallObserved Journal.hooks)
    (fun j w=>(j,w)) (fun j _=>j) self (fun _ _=>rfl) trace placeholders h
  simpa only [List.filterMap_some,Journal.execute,Driver.executeObserved,
    RoutingJoint.executeTrace_rx_factor] using proof

/-- A normal shared-journal execution supplies its actual endpoint and the
initialized live-slot carrier, with no assumed lifetime or holder invariant. -/
theorem journal_endpoint (trace : Trace) (placeholders : Bool)
    (run : runPrefixOuter (Journal.execute trace placeholders) []=(.ok result,h)) :
    ∃w,runPrefixOuter (RoutingJoint.executeTraceWith (Driver.syscallObserved Journal.hooks)
      (fun j w=>(j,w)) trace placeholders) []=(.ok (result,w),h) ∧ JournalInv h w := by
  have same := journal_correspondence trace placeholders []
  rw [run] at same
  cases actual : runPrefixOuter (RoutingJoint.executeTraceWith (Driver.syscallObserved Journal.hooks)
      (fun j w=>(j,w)) trace placeholders) [] with
  | mk result history=>
    rw [actual] at same
    cases result with
    | error reason=>cases same
    | ok pair=>
      obtain ⟨j,w⟩ := pair
      simp only [Except.map,Prod.mk.injEq,Except.ok.injEq] at same
      obtain ⟨rfl,rfl⟩ := same
      exact ⟨w,rfl,journal_normal trace placeholders actual⟩

end Leanux.Proofs.WG.RetirementSecurity.KeySlotInitialized
