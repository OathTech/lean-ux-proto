import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTransmitStaging
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedXmitContext

/-! The original routed syscall reaches the actual front and staging entry.
Its native WG/Ambient return is written back into the same product World;
fixture exit, descriptor repayment and all runner callbacks remain after it. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.RoutedTransmit
open Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged
open Queues Queues.RxCredits TransmitSecurity CausalJournal RunnerSource

structure Caller (trace : Trace) (placeholders : Bool) (operationIndex : Nat)
    (world : World) (history : List Event) where
  syscall : Xmit.Caller trace placeholders operationIndex world history
  fd : Fd
  acquired : World
  packets : List WG.Packet
  mtu : Nat
  entered : World
  path : Xmit.Path syscall.family syscall.addr syscall.payload syscall.opts
    history world fd acquired packets mtu entered

def Caller.input (caller : Caller trace placeholders operationIndex world history) : Transmit.Input :=
  ⟨caller.syscall.family,caller.syscall.addr,caller.packets,caller.mtu⟩

def Caller.events (caller : Caller trace placeholders operationIndex world history) : List Event :=
  Xmit.entryHistory caller.syscall.family caller.syscall.addr caller.packets caller.mtu history

def Caller.updated (caller : Caller trace placeholders operationIndex world history)
    (wg : WGWorld) (ambient : Ambient) : World := {caller.entered with wg,ambient}

def Caller.finish (caller : Caller trace placeholders operationIndex world history)
    (body : WGPrefix Event Int) : PrefixM Event Int := do
  let ret ← liftWGObserver body
  liftWGObserver (hooks.fixtureLeave history.length)
  liftPrefix (liftFS (fdput caller.fd))
  pure (if ret == 0 then caller.syscall.payload.length else ret)

theorem Caller.entry (caller : Caller trace placeholders operationIndex world history) :
    CompleteProduct.Carrier caller.events caller.entered :=
  caller.syscall.transmit_entry caller.path

theorem Caller.original (caller : Caller trace placeholders operationIndex world history) :
    runPrefixOuter (RoutingJoint.executeTraceWith (Driver.syscallObserved hooks)
      (fun result w=>(result,w)) trace placeholders) [] =
      runPrefixOuter (Xmit.resume trace operationIndex caller.syscall.op caller.syscall.state
        caller.entered (caller.finish (Driver.transmitObserved hooks caller.input.family
          caller.input.address caller.input.packets caller.input.mtu))) caller.events :=
  caller.syscall.transmit_continuation caller.path

theorem Caller.front_run (caller : Caller trace placeholders operationIndex world history)
    (front : Transmit.Path caller.input caller.events caller.entered.wg caller.entered.ambient
      value v b prior) :
    runPrefix (liftWGObserver (CausalJournal.front caller.input.family caller.input.address
      caller.input.packets caller.input.mtu)) caller.entered caller.events =
      (.ok (value,caller.updated v b),
        Transmit.resultHistory caller.input value caller.entered.wg v caller.entered.ambient b prior) := by
  rw [liftWGObserver_run,front.front]
  rfl

theorem Caller.front_accounted (caller : Caller trace placeholders operationIndex world history)
    (front : Transmit.Path caller.input caller.events caller.entered.wg caller.entered.ambient
      value v b prior) :
    ∃ ledger, CompleteCarrier.Accounted
      (Transmit.resultHistory caller.input value caller.entered.wg v caller.entered.ambient b prior)
      ledger [] [] (caller.updated v b).wg := by
  obtain ⟨ledger,before⟩ := caller.entry.1
  obtain ⟨after,accounted,_⟩ := front.accounted before
  exact ⟨after,accounted⟩

theorem Caller.front_continuation (caller : Caller trace placeholders operationIndex world history)
    (front : Transmit.Path caller.input caller.events caller.entered.wg caller.entered.ambient
      value v b prior) :
    runPrefixOuter (RoutingJoint.executeTraceWith (Driver.syscallObserved hooks)
      (fun result w=>(result,w)) trace placeholders) [] =
      runPrefixOuter (Xmit.resume trace operationIndex caller.syscall.op caller.syscall.state
        (caller.updated v b) (caller.finish (Transmit.tail value)))
        (Transmit.resultHistory caller.input value caller.entered.wg v caller.entered.ambient b prior) := by
  rw [caller.original]
  apply Xmit.resume_run_eq
  unfold Caller.finish
  rw [Transmit.factor caller.input,liftWGObserver_bind,bind_assoc,runPrefix_bind,caller.front_run front]

/-- The initialized front derives the very account used to classify staging;
no independent incoming ledger or staging invariant is assumed. -/
theorem Caller.staging_cases (caller : Caller trace placeholders operationIndex world history)
    (front : Transmit.Path caller.input caller.events caller.entered.wg caller.entered.ambient
      (.ok pid) v b prior) :
    ∃ ledger, let events := Transmit.resultHistory caller.input (.ok pid) caller.entered.wg v caller.entered.ambient b prior
      CompleteCarrier.Accounted events ledger [] [] v ∧
      (Staging.TakeStopped events pid v b ∨
        Staging.BorrowStopped events ledger [] [] pid v b ∨
        Staging.GuardStopped events ledger [] [] pid v b ∨
        (∃ lastWorld lastClock lastHistory,
          runWGPrefix (Driver.stagingObserved hooks pid) v b events=
            (.ok (((),lastWorld),lastClock),lastHistory) ∧
          CompleteCarrier.Accounted lastHistory ledger [] [] lastWorld) ∨
        Staging.Callback events ledger [] [] pid v b) := by
  obtain ⟨ledger,before⟩ := caller.entry.1
  exact front.staging_cases before

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.RoutedTransmit
