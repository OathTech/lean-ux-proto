import Leanux.WG.PtrRing

/-! Guarded production uses the original physical full test and producer.
The ring's logical items exclude consumed slots awaiting batch retirement. -/
namespace Leanux.Proofs.WG.Queues
open Leanux Leanux.WG

/-- The producer choice in enqueue: a full ring rejects without advancing. -/
def tryProduce (r : PtrRing α) (x : α) : Bool × PtrRing α :=
  if r.full then (false, r) else (true, r.produce x)

theorem tryProduce_full (r : PtrRing α) (x : α) (hf : r.full = true) :
    tryProduce r x = (false, r) := by simp [tryProduce, hf]

theorem tryProduce_free (r : PtrRing α) (x : α) (hf : r.full = false) :
    tryProduce r x = (true, r.produce x) := by simp [tryProduce, hf]

theorem tryProduce_rejected_iff (r : PtrRing α) (x : α) :
    (tryProduce r x).1 = false ↔ r.full = true := by
  simp only [tryProduce]
  cases r.full <;> simp

/-- A finite producer-only segment, with each outcome retained in order. -/
def produceMany (r : PtrRing α) : List α → List Bool × PtrRing α
  | [] => ([], r)
  | x :: xs =>
    let (accepted, next) := tryProduce r x
    let (outcomes, final) := produceMany next xs
    (accepted :: outcomes, final)

theorem produceMany_full (r : PtrRing α) (xs : List α) (hf : r.full = true) :
    produceMany r xs = (List.replicate xs.length false, r) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [produceMany, tryProduce_full r x hf, ih, List.replicate_succ]

end Leanux.Proofs.WG.Queues
