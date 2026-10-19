import Leanux.Proofs.WG.Progress.CommittedInitializedReceiptClaims
import Leanux.Proofs.WG.Progress.DispatchRecordSource

/-! Strict supplied-record decrease at each original committed activation
receipt. Earlier receipts remain available if an enclosing operation stops. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.CommittedRuns
open Leanux Leanux.Env Leanux.Proofs.Framing
open Leanux.Proofs.WG.Progress.RecordSuffix

theorem SourceReceipt.record_decrease {receipt : Receipt} (source : SourceReceipt receipt)
    (records : List HiddenRecord) (final : Campaign2.Product.Snapshot)
    (present : receipt.before.ambient.hidden=some records)
    (normal : receipt.exit.erase=.ok ((),final)) :
    StrictTail records final.ambient.hidden := by
  obtain ⟨entry,before,exit⟩:=source
  rw [before] at present
  change entry.ambient.hidden=some records at present
  have erases:=congrArg (fun action:Leanux.M _=>action.run entry)
    (observedActivationExit_source receipt.activation)
  change Except.ok (((activationExitRun receipt.activation entry).map Campaign2.Product.snapshot).erase,entry)=
    Except.ok (Campaign2.Product.observeResult ((Activation.run receipt.activation).run entry),entry) at erases
  have outcome:=congrArg Prod.fst (Except.ok.inj erases)
  dsimp only at outcome
  rw [exit,outcome] at normal
  cases actual:(Activation.run receipt.activation).run entry with
  | error stop=>simp only [actual,Campaign2.Product.observeResult,Except.map] at normal; cases normal
  | ok pair=>
    obtain ⟨value,after⟩:=pair
    cases value
    rw [actual] at normal
    change (Except.ok ((),Campaign2.Product.snapshot after) : Except Stop _)=.ok ((),final) at normal
    have same:=congrArg Prod.snd (Except.ok.inj normal)
    dsimp only at same
    rw [←same]
    exact (hoare_iff_run _ _ _).mp (activation_all_strict receipt.activation records)
      entry () after present actual

theorem Initialized.original_initialized_record_decrease
    (trace : Runner.Trace) (placeholders : Bool) :
    (Initialized.inspection trace placeholders).1.map Prod.fst = Runner.executeTrace trace placeholders ∧
    ∀ receipt ∈ (Initialized.inspection trace placeholders).2,
      ∀ records final, receipt.before.ambient.hidden=some records →
        receipt.exit.erase=.ok ((),final) → StrictTail records final.ambient.hidden := by
  obtain ⟨erases,history⟩:=Initialized.original_initialized_source_receipts trace placeholders
  refine ⟨erases,?_⟩
  intro receipt member records final present normal
  exact (history receipt member).1.record_decrease records final present normal

end Leanux.Proofs.WG.Progress.CommittedRuns
