import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteProductSource
import Leanux.Proofs.WG.Origins.RunnerInvariant

/-! Boot and the original operation loop initialize the paired packet account.
The exact observed syscall contract remains visible here until the concrete
scheduler, receive, transmit and lifecycle callers are joined. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteProduct
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal

theorem initial (net bare : Bool) (w : World) :
    Carrier [] {w with wg := Runner.initialWG net bare} :=
  CompleteAllocated.initial net bare

/-- The actual initialized runner supplies its own empty ledger. This local
composition theorem still requires every actual syscall source contract;
that premise is not an initialized conservation claim. -/
theorem initialized_from_syscalls
    (syscalls : ∀ call, Checked (Driver.syscallObserved hooks call))
    (trace : Runner.Trace) (placeholders : Bool) :
    Safe (runPrefixOuter (CausalJournal.execute trace placeholders) []).2 := by
  apply RunnerInvariant.executeTraceWith Carrier Safe carrier_safe store_transport
    (Driver.syscallObserved hooks) syscalls trace placeholders
  intro w same
  exact store_transport [] {w with wg := Runner.initialWG trace.net trace.bare} w same
    (initial trace.net trace.bare w)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteProduct
