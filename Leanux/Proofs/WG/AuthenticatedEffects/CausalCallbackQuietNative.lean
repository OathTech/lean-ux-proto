import Leanux.Proofs.WG.AuthenticatedEffects.CausalCallbackQuiet
import Leanux.Proofs.WG.TransmitSecurity.DriverNestedCallsHistory

/-! Exact source history frames for receive, clear-work and dump callbacks.
Their real peer repayments remain observed; each projected event is explicitly
required to be quiet. Native state preservation is a separate obligation. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.CallbackQuiet
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity

variable {F : Type}

theorem native_release (ρ : Event → Option F)
    (quiet : ∀ event, ρ (.stagedDisposal event) = none) (peer : Option PeerId) :
    StateQuiet ρ (hooks.peerRelease peer) :=
  state_focus ρ Event.stagedDisposal stagedDisposal? quiet _

theorem receive_entry (ρ : Event → Option F)
    (quiet : ∀ event, ρ (.stagedDisposal event) = none) (msg : Key) (src : SkbSource) :
    ProductQuiet ρ (Driver.receiveEntryObserved hooks msg src) := by
  apply product_of_history
  intro before
  exact Driver.receiveEntry_history hooks
    (fun peer => state_history (native_release ρ quiet peer) before) msg src

theorem clear_worker (ρ : Event → Option F)
    (quiet : ∀ event, ρ (.stagedDisposal event) = none) :
    ProductQuiet ρ (Driver.clearWorkerObserved hooks) := by
  apply product_of_history
  intro before
  exact Driver.clearWorker_history hooks
    (fun peer => state_history (native_release ρ quiet peer) before)

theorem dump_dispatch (ρ : Event → Option F)
    (quiet : ∀ event, ρ (.stagedDisposal event) = none) (call : Syscall) :
    ProductQuiet ρ (RetirementSecurity.NestedPeerRelease.dumpDispatch (Driver.nestedOps hooks) call) := by
  apply product_of_history
  intro before
  exact Driver.dumpDispatch_history hooks
    (fun peer => state_history (native_release ρ quiet peer) before) call

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.CallbackQuiet
