import MemoryInvariant
import HistoryGuard

namespace Binary.Callback
local instance : Labels := Image.linkedLabels

/-- Retain a store-stable memory predicate without losing the segment guard. -/
theorem guarded_invariant {F : DataMem → Prop} (stable : MemoryInvariant.StoreStable F)
    (fetch : Int64 → Option Decoded) {guard s post}
    (run : Eventually (guardedStep fetch guard) post s) (initial : F s.data.dmem) :
    Eventually (guardedStep fetch guard) (fun t => post t ∧ F t.data.dmem) s := by
  induction run with
  | done s hp => exact .done _ ⟨hp,initial⟩
  | step s mid step later ih =>
    exact .step s _ ⟨step.1,MemoryInvariant.step stable fetch s mid initial step.2⟩
      (fun t h => ih t h.1 h.2)

theorem guarded_mapped (fetch : Int64 → Option Decoded) {guard s post}
    (run : Eventually (guardedStep fetch guard) post s) :
    Eventually (guardedStep fetch guard) (fun t => post t ∧
      ∀ a n, (s.data.dmem.loadInt a n).isSome=true → (t.data.dmem.loadInt a n).isSome=true) s :=
  guarded_invariant (MemoryInvariant.mapped_stable s.data.dmem) fetch run (fun _ _ h => h)

#print axioms guarded_mapped
end Binary.Callback
