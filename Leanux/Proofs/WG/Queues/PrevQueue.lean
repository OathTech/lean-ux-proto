import Leanux.Proofs.Framing.KernelEffects
import Leanux.WG.PrevQueue

set_option maxHeartbeats 800000

/-! Logical FIFO laws for the original prev_queue operations. The logical
contents include the cached peek; the original count excludes it. Normal-return
laws admit malformed queues, whose original Stops are not hidden. -/
namespace Leanux.Proofs.WG.Queues
open Leanux Leanux.WG Leanux.Proofs.Framing Std.Do

theorem prev_enqueue_all (q : PrevQueue α) (x : α) :
    (q.enqueue x).all = q.all ++ [x] := by
  simp [PrevQueue.enqueue, PrevQueue.all, List.append_assoc]

theorem prev_dequeue_normal (q : PrevQueue α) (w v : World)
    (head : Option α) (q' : PrevQueue α)
    (hr : q.dequeue.run w = .ok ((head, q'), v)) :
    head = q.items.head? ∧ q'.items = q.items.tail ∧
      q'.peeked = q.peeked ∧ v.k = w.k := by
  rcases q with ⟨items, stub, peeked⟩
  cases stub <;> cases items with
  | nil => simp [PrevQueue.dequeue, branch, invariant] at hr ⊢ <;> cases hr <;> simp_all
  | cons x xs =>
    cases xs <;>
      simp [PrevQueue.dequeue, branch, invariant, unsupported] at hr ⊢ <;>
      obtain ⟨rfl, rfl, rfl⟩ := hr <;> simp

theorem prev_peek_normal (q : PrevQueue α) (w v : World)
    (head : Option α) (q' : PrevQueue α)
    (hr : q.peek.run w = .ok ((head, q'), v)) :
    head = q.all.head? ∧ q'.all = q.all ∧ q'.peeked = head ∧ v.k = w.k := by
  rcases q with ⟨items, stub, peeked⟩
  cases peeked with
  | some x =>
    simp [PrevQueue.peek, branch] at hr
    obtain ⟨rfl, rfl, rfl⟩ := hr
    simp [PrevQueue.all]
  | none =>
    cases stub <;> cases items with
    | nil => simp [PrevQueue.peek, PrevQueue.dequeue, branch, invariant] at hr ⊢ <;> cases hr <;> simp_all [PrevQueue.all]
    | cons x xs =>
      cases xs <;>
        simp [PrevQueue.peek, PrevQueue.dequeue, branch, invariant, unsupported] at hr ⊢ <;>
        obtain ⟨rfl, rfl, rfl⟩ := hr <;> simp [PrevQueue.all]

theorem prev_peek_then_drop (q : PrevQueue α) (w v : World)
    (x : α) (q' : PrevQueue α)
    (hr : q.peek.run w = .ok ((some x, q'), v)) :
    q.all = x :: q'.dropPeeked.all := by
  obtain ⟨_, ha, hp, _⟩ := prev_peek_normal q w v (some x) q' hr
  rw [← ha]
  simp [PrevQueue.all, PrevQueue.dropPeeked, hp]

/-- A nonstub empty queue with no cached peek fails at the original invariant. -/
theorem prev_peek_malformed (q : PrevQueue α) (w : World)
    (hp : q.peeked = none) (ht : q.tailIsStub = false) (hi : q.items = []) :
    q.peek.run w = .error (.invariant "prev_queue: a tail item without an entry") := by
  simp [PrevQueue.peek, PrevQueue.dequeue, hp, ht, hi, branch, invariant]
  rfl

/-- The only structural obstruction in the sequential queue model is a
nonstub tail with no underlying item. Cached peeks are separate from this tail. -/
def PrevCoherent (q : PrevQueue α) : Prop := q.items = [] → q.tailIsStub = true

theorem prev_dequeue_total (q : PrevQueue α) (w : World) (hc : PrevCoherent q) :
    ∃ head q' v, q.dequeue.run w = .ok ((head, q'), v) := by
  rcases q with ⟨items, stub, peeked⟩
  cases stub <;> cases items with
  | nil => simp_all [PrevCoherent, PrevQueue.dequeue, branch] <;> exact ⟨_, _, _, rfl⟩
  | cons x xs =>
    cases xs <;> simp [PrevQueue.dequeue, branch] <;> exact ⟨_, _, _, rfl⟩

theorem prev_peek_total (q : PrevQueue α) (w : World) (hc : PrevCoherent q) :
    ∃ head q' v, q.peek.run w = .ok ((head, q'), v) := by
  rcases q with ⟨items, stub, peeked⟩
  cases peeked with
  | some x => simp [PrevQueue.peek, branch] <;> exact ⟨_, _, _, rfl⟩
  | none =>
    cases stub <;> cases items with
    | nil => simp_all [PrevCoherent, PrevQueue.peek, PrevQueue.dequeue, branch] <;> exact ⟨_, _, _, rfl⟩
    | cons x xs =>
      cases xs <;> simp [PrevQueue.peek, PrevQueue.dequeue, branch] <;> exact ⟨_, _, _, rfl⟩

end Leanux.Proofs.WG.Queues
