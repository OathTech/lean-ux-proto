import Leanux.Proofs.WG.Queues.GroSource

/-! Invariant composition for the original stamped GRO source. The successful
completion event carries exactly the product execution that just returned;
no condition is imposed on a fabricated or unrelated receipt. -/
namespace Leanux.Proofs.WG.Queues.RxJoint.GroSource
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes

variable {E α : Type} {I : List E → World → Prop} {S : List E → Prop}

theorem emit_preserves (safe : ∀ h w, I h w → S h) (event : E)
    (step : ∀ h w, I h w → I (h ++ [event]) w) :
    PrefixPreserves I S (emitPrefix event) := by
  intro w h hi
  exact ⟨[event],rfl,safe _ _ (step h w hi),step h w hi⟩

theorem receipt_preserves (safe : ∀ h w, I h w → S h)
    (a : PrefixM E α) (event : RunWitness α → E)
    (keep : PrefixPreserves I S a)
    (step : ∀ w h x v t, I h w → runPrefix a w h = (.ok (x,v),t) →
      I t v → I (t ++ [event ⟨x,w,v⟩]) v) :
    PrefixPreserves I S (receiptObserved a event) := by
  intro w h hi
  obtain ⟨suffix,append,safety,normal⟩ := keep w h hi
  rw [runPrefix_receiptObserved]
  cases run : runPrefix a w h with
  | mk result t =>
    simp only [run] at append safety normal
    cases result with
    | error stop => exact ⟨suffix,append,safety,True.intro⟩
    | ok result =>
      rcases result with ⟨x,v⟩
      have next := step w h x v t hi run normal
      exact ⟨suffix ++ [event ⟨x,w,v⟩],by simp only [append,List.append_assoc],
        safe _ _ next,next⟩

variable (encode : Event → E) (stack : List UInt8 → PrefixM E Unit)
    (safe : ∀ h w, I h w → S h)
    (entered : ∀ e h w, I h w → I (h ++ [encode (.entered e)]) w)
    (callback : ∀ bytes, PrefixPreserves I S (stack bytes))
    (completed : ∀ e w h x v t, I h w →
      runPrefix (stack e.tag.bytes) w h = (.ok (x,v),t) →
      I t v → I (t ++ [encode (.completed e ⟨x,w,v⟩)]) v)

include safe entered callback completed

theorem enter_preserves (e : Entry) : PrefixPreserves I S (enterWith encode stack e) := by
  unfold enterWith
  exact (emit_preserves safe _ (entered e)).bind (fun _ =>
    receipt_preserves safe _ _ (callback _) (completed e))

theorem flush_preserves (entries : List Entry) :
    PrefixPreserves I S (flushWith encode stack entries) :=
  PrefixPreserves.forM entries _ safe
    (enter_preserves encode stack safe entered callback completed)

theorem normalList_preserves (g : Gro) :
    PrefixPreserves I S (normalListWith encode stack g) := by
  unfold normalListWith
  split
  · exact PrefixPreserves.pure safe _
  · exact (flush_preserves encode stack safe entered callback completed _).bind
      (fun _ => PrefixPreserves.pure safe _)

theorem normalOne_preserves (g : Gro) (e : Entry) (segs : Nat) :
    PrefixPreserves I S (normalOneWith encode stack g e segs) := by
  unfold normalOneWith
  dsimp only
  split
  · exact normalList_preserves encode stack safe entered callback completed _
  · exact PrefixPreserves.pure safe _

theorem receive_preserves (g : Gro) (e : Entry) :
    PrefixPreserves I S (receiveWith encode stack g e) := by
  have stopped {α : Type} (message : String) :
      PrefixPreserves I S (liftPrefix (unsupported message : M α)) := by
    apply PrefixEnsures.preserves
    apply PrefixEnsures.lift _ safe
    intro h w x v hi hr
    change (Except.error _ : Except Stop _) = _ at hr
    cases hr
  unfold receiveWith
  repeat' first
    | with_reducible exact normalOne_preserves encode stack safe entered callback completed _ _ _
    | with_reducible exact PrefixPreserves.pure safe _
    | with_reducible exact stopped _
    | with_reducible apply PrefixPreserves.bind
    | with_reducible apply PrefixPreserves.ite
    | (with_reducible intro x; try dsimp only [id])
    | (with_reducible split <;> try dsimp only [id])

theorem flushAll_preserves (g : Gro) :
    PrefixPreserves I S (flushAllWith encode stack g) := by
  unfold flushAllWith
  apply PrefixPreserves.bind
  · apply PrefixPreserves.forIn _ _ _ safe
    intro e current
    exact (normalOne_preserves encode stack safe entered callback completed current e 1).bind
      (fun _ => PrefixPreserves.pure safe _)
  · intro current
    exact (normalList_preserves encode stack safe entered callback completed {current with held := []}).bind
      (fun _ => PrefixPreserves.pure safe _)

end Leanux.Proofs.WG.Queues.RxJoint.GroSource
