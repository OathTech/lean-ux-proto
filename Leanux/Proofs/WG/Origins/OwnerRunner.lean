import Leanux.Proofs.WG.Origins.OwnerSyscalls
import Leanux.Proofs.WG.Origins.RunnerInvariant

/-! Initialized owner and current-identity checks on the original RX journal.
Every typed trace and both placeholder modes use the actual fixture and syscall
closure. Stops retain the reached checks without a fictitious final World. -/
namespace Leanux.Proofs.WG.OwnerRunner
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues

theorem executeTrace (trace : Runner.Trace) (placeholders : Bool) :
    OwnerChecks.Safe (runPrefixOuter (RxHistory.executeTraceHistory trace placeholders) []).2 :=
  RunnerInvariant.executeTraceWith OwnerChecks.Inv OwnerChecks.Safe
    (fun _ _ hi => hi.safe) OwnerControlCalls.store RxHistory.syscall OwnerSyscalls.syscall
    trace placeholders (OwnerChecks.initial trace.net trace.bare)

/-- The specified decrypt occurrence uses its actual strict earlier session
prefix and captured owner bounds, now derived from original initialization. -/
theorem decrypt (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List RxHistory.Event) (id : SkbId) (r : WGRunWitness (RxPacket × Option RxPacket))
    (position : (runPrefixOuter (RxHistory.executeTraceHistory trace placeholders) []).2 =
      pre ++ .rx (.decrypt id r) :: post) :
    CurrentLifecycle.Inv (Origins.HistorySupport.sessions pre) r.before ∧ OwnerBounds.Carrier r.before :=
  (executeTrace trace placeholders).decrypt position

/-- A reached copied-trial probe retains its real earlier allocation history
and current/owner facts. This does not turn the copied trial into a committed call. -/
theorem probe (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List RxHistory.Event) (p : ProbeEntry)
    (position : (runPrefixOuter (RxHistory.executeTraceHistory trace placeholders) []).2 =
      pre ++ .audit (.probe p) :: post) :
    p.history = RxHistory.prior pre ∧ CurrentSessionPrefix.StateInv pre p.world ∧
      OwnerBounds.Carrier p.world.wg :=
  (executeTrace trace placeholders).probe position

end Leanux.Proofs.WG.OwnerRunner
