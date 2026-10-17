import Leanux.Proofs.WG.Noise.TagSequenceModel
import Leanux.Proofs.WG.Noise.CreationTagClaims
import Leanux.Proofs.WG.Noise.ResponseTagClaims
import Leanux.Proofs.WG.Noise.InitiationTagClaims
import Leanux.Proofs.WG.Noise.SessionTagClaims

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG

/-- Dispatch only to the seven original native calls, preserving their returns. -/
def runTagOperation : TagOperation → WG.M TagReturn
  | .createInitiation pid => do return .created (← createInitiation pid)
  | .createResponse pid => do return .created (← createResponse pid)
  | .consumeInitiation message => do return .consumed (← consumeInitiation message)
  | .consumeResponse message => do return .consumed (← consumeResponse message)
  | .beginSession pid => do return .begun (← beginSession pid)
  | .handshakeClear pid => do handshakeClear pid; return .cleared
  | .expireCurrentPeerKeypairs pid => do expireCurrentPeerKeypairs pid; return .cleared

/-- Original calls in the given order. Bind propagates the first Stop. -/
def runTagSequence : List TagOperation → WG.M (List TagReturn)
  | [] => pure []
  | operation :: operations => do
    let result ← runTagOperation operation
    let results ← runTagSequence operations
    return result :: results

/-- Observations are actual reads around the original call, without running
an operation on reconstructed state or converting its failures into values. -/
def observedTagOperation (operation : TagOperation) : WG.M TagReceipt := do
  let before ← Campaign2.read
  let result ← runTagOperation operation
  let after ← Campaign2.read
  return ⟨operation,before,result,after⟩

/-- A failed call stops the sequence with its original error; it does not
return the earlier receipts as a successful partial history. -/
def observedTagSequence : List TagOperation → WG.M (List TagReceipt)
  | [] => pure []
  | operation :: operations => do
    let receipt ← observedTagOperation operation
    let receipts ← observedTagSequence operations
    return receipt :: receipts

/-- Equality of the actual nested-state computations, including every Stop
and every concrete final WireGuard and Ambient state. -/
theorem observedTagOperation_erase (operation : TagOperation) :
    (do let receipt ← observedTagOperation operation; pure receipt.result) =
      runTagOperation operation := by
  simp only [observedTagOperation,bind_assoc,pure_bind]
  funext g ambient
  change (runTagOperation operation g ambient >>= fun ((result,after),inputs) =>
    Except.ok ((result,after),inputs)) = runTagOperation operation g ambient
  cases runTagOperation operation g ambient <;> rfl

/-- Erasing receipts preserves every original result, concrete final state
and the exact first Stop. No later operation is substituted for a failure. -/
theorem observedTagSequence_erase (operations : List TagOperation) :
    (do let receipts ← observedTagSequence operations; pure (receipts.map TagReceipt.result)) =
      runTagSequence operations := by
  induction operations with
  | nil => rfl
  | cons operation operations ih =>
    rw [runTagSequence, ← observedTagOperation_erase operation, ← ih]
    simp only [observedTagSequence,bind_assoc,pure_bind,List.map_cons]

/-- One original operation supplies its own all-peer edge certificate. -/
theorem runTagOperation_effect (operation : TagOperation) (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (runTagOperation operation) (fun s => s = entry)
      (fun result after => TagReceiptEffect ⟨operation,entry,result,after⟩) := by
  have mapped {α : Type} (action : WG.M α) (wrap : α → TagReturn)
      (Q : TagReturn → Campaign2.Snapshot → Prop)
      (fact : Campaign2.Ensures action (fun s => s = entry) (fun x s => Q (wrap x) s)) :
      Campaign2.Ensures (do let x ← action; pure (wrap x)) (fun s => s = entry) Q := by
    intro g ambient result final after pre run
    change ((action.run g).run ambient >>= fun ((x,next),inputs) =>
      Except.ok ((wrap x,next),inputs)) = _ at run
    cases actual : (action.run g).run ambient with
    | error stop => rw [actual] at run; cases run
    | ok out =>
      obtain ⟨⟨x,next⟩,inputs⟩ := out
      rw [actual] at run
      cases run
      exact fact g ambient x _ _ pre actual
  cases operation with
  | createInitiation pid =>
    apply mapped
    exact createInitiation_tagMap_projected pid entry
  | createResponse pid =>
    apply mapped
    exact createResponse_tagMap_projected pid entry
  | consumeInitiation message =>
    apply mapped
    exact consumeInitiation_tagMap_projected message entry
  | consumeResponse message =>
    apply mapped
    exact consumeResponse_tagMap_projected message entry
  | beginSession pid =>
    apply mapped
    exact beginSession_tagMap_projected pid entry
  | handshakeClear pid =>
    apply mapped
    exact handshakeClear_tagMap_projected pid entry
  | expireCurrentPeerKeypairs pid =>
    apply mapped
    exact expireCurrentPeerKeypairs_tagMap_projected pid entry

end Leanux.Proofs.WG.Noise
