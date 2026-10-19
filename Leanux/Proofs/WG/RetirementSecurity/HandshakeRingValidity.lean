import Leanux.Proofs.WG.Queues.RingMap
import Leanux.Proofs.Framing.WGKernel

/-! Physical slot validity for the native handshake ring. The property includes
consumed entries awaiting batch clearing, so neither well-formed geometry nor a
logical FIFO model is needed to justify the actual worker's next read. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HandshakeLengths
open Leanux Leanux.WG Leanux.Proofs.Framing

/-- Every occupied physical slot satisfies the payload predicate. -/
def Slots (P : α → Prop) (slots : Array (Option α)) : Prop :=
  ∀ (i : Nat) x, slots[i]?=some (some x) → P x

def Ring (P : α → Prop) (r : PtrRing α) : Prop := Slots P r.slots

theorem slots_set (P : α → Prop) (slots : Array (Option α)) (i : Nat)
    (entry : Option α) (before : Slots P slots) (valid : ∀x,entry=some x→P x) :
    Slots P (slots.set! i entry) := by
  intro j x found
  simp only [Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds] at found
  split at found
  · rename_i hit
    split at found
    · exact valid x (Option.some.inj found)
    · cases found
  · exact before j x found

theorem initial (P : α → Prop) (size : Nat) : Ring P (PtrRing.init size) := by
  intro i x found
  simp only [PtrRing.init,Array.getElem?_replicate] at found
  split at found <;> cases found

theorem produce (P : α → Prop) (r : PtrRing α) (x : α)
    (before : Ring P r) (valid : P x) : Ring P (r.produce x) :=
  slots_set P r.slots r.producer (some x) before (fun _ h=>Option.some.inj h ▸ valid)

theorem clear (P : α → Prop) (slots : Array (Option α)) (head tail : Nat)
    (before : Slots P slots) : Slots P (PtrRing.discardOne.clear slots head tail) := by
  unfold PtrRing.discardOne.clear
  generalize List.range (head+1-tail)=indices
  induction indices generalizing slots with
  | nil=> exact before
  | cons i indices ih=>
    simp only [List.foldl_cons]
    exact ih _ (slots_set P slots (head-i) none before (fun _ h=>by cases h))

theorem discard (P : α → Prop) (r : PtrRing α) (before : Ring P r) : Ring P r.discardOne := by
  unfold PtrRing.discardOne
  dsimp only
  split
  all_goals dsimp only
  all_goals split
  all_goals first | exact clear P r.slots r.consumerHead r.consumerTail before | exact before

theorem peek (P : α → Prop) (r : PtrRing α) (before : Ring P r)
    (found : r.peek=some x) : P x := by
  unfold PtrRing.peek at found
  split at found
  · cases found
  · cases entry : r.slots[r.consumerHead]? with
    | none=> simp only [entry,Option.getD_none] at found; cases found
    | some item=>
      simp only [entry,Option.getD_some] at found
      exact before _ x (found ▸ entry)

theorem consumed (P : α → Prop) (r : PtrRing α) (before : Ring P r) :
    Ring P r.consume.2 ∧ ∀x,r.consume.1=some x→P x := by
  unfold PtrRing.consume
  split
  · rename_i x found
    exact ⟨discard P r before,fun _ h=>Option.some.inj h ▸ peek P r before found⟩
  · exact ⟨before,fun _ h=>by cases h⟩

def view (w : WGWorld) : Option (PtrRing (List UInt8 × SkbSource)) := w.dev.map (·.handshakeQueue)

def Inv (Valid : List UInt8 → Prop) (w : WGWorld) : Prop :=
  ∀d,w.dev=some d→Ring (fun entry=>Valid entry.1) d.handshakeQueue

theorem transport (same : view v=view w) (before : Inv Valid w) : Inv Valid v := by
  intro d found
  cases original : w.dev with
  | none=> simp only [view,original,found,Option.map_some,Option.map_none] at same; cases same
  | some old=>
    simp only [view,original,found,Option.map_some,Option.some.injEq] at same
    exact same ▸ before old original

theorem popped (before : Inv Valid w) (device : w.dev=some d)
    (poll : d.handshakeQueue.consume=(some (msg,src),ring)) : Valid msg :=
  (consumed _ _ (before d device)).2 _ (congrArg Prod.fst poll)

end Leanux.Proofs.WG.RetirementSecurity.HandshakeLengths
