import Leanux.Proofs.WG.Progress.CommittedRunSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.CommittedRuns
open Leanux Leanux.Proofs.Logged

/-- Hidden native call-entry evidence for the projected fields of this receipt.
The activation is the receipt's own activation. This predicate alone does not
certify an arbitrary origin label or its position in a caller's execution. -/
def SourceReceipt (receipt : Receipt) : Prop :=
  ∃ entry : World, receipt.before = Campaign2.Product.snapshot entry ∧
    receipt.exit = (activationExitRun receipt.activation entry).map Campaign2.Product.snapshot

def SourceHistory (history : List Receipt) : Prop :=
  ∀ receipt ∈ history, SourceReceipt receipt

theorem sourceReceipt_fresh (origin : Origin) (activation : Activation) (entry : World) :
    SourceReceipt ⟨origin,activation,Campaign2.Product.snapshot entry,
      (activationExitRun activation entry).map Campaign2.Product.snapshot⟩ :=
  ⟨entry,rfl,rfl⟩

theorem SourceReceipt.facts {receipt : Receipt} (source : SourceReceipt receipt) :
    ActivationExitFacts receipt.activation receipt.exit := by
  obtain ⟨entry,_,exit⟩:=source
  rw [exit]
  exact activationExitRun_facts receipt.activation entry


end Leanux.Proofs.WG.Progress.CommittedRuns
