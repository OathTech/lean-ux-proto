import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixAdapters
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteProductSource

/-! Product composition keeps every earlier journal certificate. Native
allocation companions come from the same original endpoint execution. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Product
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal

abbrev Checked (body : PrefixM Event α) : Prop :=
  Ensures CompleteProduct.Carrier CompleteProduct.Safe body (fun _=>CompleteProduct.Carrier)

abbrev StateChecked (body : WGPrefix Event α) : Prop :=
  StateEnsures (CompleteAllocated.Carrier [] []) CompleteProduct.Safe body
    (fun _=>CompleteAllocated.Carrier [] [])

theorem state (checked : StateChecked body) : Checked (liftWGObserver body) := checked.liftWG

theorem pair (checked : StateEnsures (CompleteCarrier.Carrier [] []) CompleteProduct.Safe body
      (fun _=>CompleteCarrier.Carrier [] []))
    (endpoint : CompleteProduct.StateChecked body) : StateChecked body :=
  checked.join endpoint (fun _ _ _ before=>before.1)

theorem pair_product (checked : Ensures
      (fun h (w : World)=>CompleteCarrier.Carrier [] [] h w.wg w.ambient)
      CompleteProduct.Safe body
      (fun _ h w=>CompleteCarrier.Carrier [] [] h w.wg w.ambient))
    (endpoint : CompleteProduct.Checked body) : Checked body :=
  checked.join endpoint (fun _ _ before=>before.1)

theorem pure_checked (value : α) : Checked (pure value) :=
  Ensures.pure value (fun _ _ before=>before)

theorem bind_checked (head : Checked body) (tail : ∀ value, Checked (next value)) :
    Checked (body >>= next) := Ensures.bind head tail

theorem conditional (p : Prop) [Decidable p]
    (yes : p→Checked left) (no : ¬p→Checked right) : Checked (if p then left else right) := by
  by_cases test : p <;> simp only [test,↓reduceIte]
  · exact yes test
  · exact no test

theorem list {α β : Type} (xs : List α) (initial : β) (body : α→β→PrefixM Event (ForInStep β))
    (checked : ∀ value acc, Checked (body value acc)) : Checked (forIn xs initial body) :=
  Ensures.forIn xs initial body (fun _=>CompleteProduct.Carrier) checked

theorem native (action : Leanux.M α) (endpoint : CompleteProduct.Checked (liftPrefix action)) :
    Checked (liftPrefix action) := Ensures.quiet endpoint (fun _ _=>rfl)

theorem wg (action : WG.M α) (checked : StateChecked (liftWGPrefix action)) :
    Checked (liftPrefix (liftWG action)) := by
  simpa only [liftWGObserver_lift] using state checked

theorem emit (event : Event) (birth : Staged.Obligations.birthPackets event=[])
    (terminal : StagedTerminalComplete.Quiet event) : Checked (emitPrefix event) :=
  product_emit event birth terminal

theorem capture (checked : Checked body) : Checked (captureObserved body) :=
  PrefixPreserves.captureObserved checked

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Product
