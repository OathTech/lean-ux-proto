import Leanux.Proofs.WG.AuthenticatedEffects.CausalJournalOldProjection
import Leanux.Proofs.WG.RetirementSecurity.OccurrenceTx

/-! The allocation companion is obtained from the native execution of the
same callback; the exact journal projection supplies only native erasure. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteProduct.TxNative
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity

theorem erases (pid : PeerId) : ErasesPrefix (CausalJournal.transmit pid) (liftWG (txStep pid)) := by
  intro w h
  have projected := congrArg Prod.fst (CausalJournal.transmit_projects pid w h)
  have native := focusPrefix_erases Journal.completionEvent Journal.completion?
    (Completion.step_erases pid) w (h.filterMap CausalJournal.old?)
  change (runPrefix (Journal.transmit pid) w (h.filterMap CausalJournal.old?)).1 =
    (runPrefix (CausalJournal.transmit pid) w h).1.map id at projected
  simpa only [Except.map_id,id_eq] using projected.symm.trans native

theorem allocated (pid : PeerId) : Preserves StackOwnership.Allocated (txStep pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact Allocated.native (txStepPrefix_erases pid)
    (txStepPrefix_preserves_ambient allocationAmbient allocationTx allocationSocket pid)
    before a b run

theorem allocated_product (pid : PeerId) :
    Preserves (fun w : World => StackOwnership.Allocated w.wg) (liftWG (txStep pid)) :=
  PublicationPoll.native_product StackOwnership.Allocated _ (allocated pid)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteProduct.TxNative
