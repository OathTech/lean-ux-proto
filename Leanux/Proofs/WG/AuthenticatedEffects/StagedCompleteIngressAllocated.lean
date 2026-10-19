import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteIngressSource
import Leanux.Proofs.WG.RetirementSecurity.ReceiveEntryHolders

/-! The allocation companion is a native endpoint invariant on the very same
UDP execution. It does not supply chronology for the complete ticket journal;
that journal's source contract is proved separately in IngressSource. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteIngress
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal

/-- Hiding the actual nested disposal receipts recovers the original UDP
receive action, including its exact normal result and Stop. -/
theorem erases (msg : Key) (src : SkbSource) :
    ErasesPrefix (Driver.receiveEntryObserved hooks msg src) (liftWG (wgReceive msg src)) := by
  apply liftWGObserver_erases
  exact NestedPeerRelease.receiveObserved_erases Event.stagedDisposal stagedDisposal? msg src

/-- Original UDP ingress transports the independent campaign-1 allocation
invariant. Its witness is used only for native bounds, not journal identity. -/
theorem allocated (msg : Key) (src : SkbSource) :
    Preserves StackOwnership.Allocated (wgReceive msg src) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact RetirementSecurity.Allocated.native (wgReceivePrefix_erases msg src)
    (wgReceivePrefix_preserves allocationAmbient allocationReceiveIngress msg src) before a b run

theorem allocated_product (msg : Key) (src : SkbSource) :
    Preserves (fun w : World => StackOwnership.Allocated w.wg) (liftWG (wgReceive msg src)) :=
  PublicationPoll.native_product _ _ (allocated msg src)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteIngress
