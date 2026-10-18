import Leanux.Proofs.WG.AuthenticatedEffects.TimerRootFacts

/-! The complete original receiver supplies authenticated causes to its actual
session-derived and traversal timer-arm occurrences. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TimerRoot
open Leanux Leanux.WG Leanux.Proofs.Logged

private theorem lookup_position {α : Type} (xs : List α) (index : Nat) (value : α)
    (found : xs[index]? = some value) :
    ∃ pre post, xs = pre ++ value :: post ∧ pre.length = index := by
  induction xs generalizing index with
  | nil => simp at found
  | cons x xs ih =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at found
      subst x
      exact ⟨[],xs,rfl,rfl⟩
    | succ index =>
      obtain ⟨pre,post,position,length⟩ := ih index (by simpa using found)
      exact ⟨x :: pre,post,by simp [position],by simp [length]⟩

def Authenticated (pre : List Event) (r : Arm) : Prop :=
  r.Native ∧ ∃ before after,
    history pre = before ++ .callback r.kind r.peer :: after ∧ before.length = r.origin ∧
      ∃ admission ∈ HandshakeCausal.roots before, admission.Valid ∧ admission.ForPeer r.peer

/-- The index in an arm receipt identifies its actual enclosing callback;
that callback has a strictly earlier authenticated admission in the original
receiver. The receipt and its authentication survive any subsequent Stop. -/
theorem arm_authenticated (msg : Key) (src : SkbSource) (w : WGWorld) (a : Ambient)
    (pre post : List Event) (r : Arm)
    (position : (runWGPrefix (receive msg src) w a []).2 = pre ++ .armed r :: post) :
    Authenticated pre r := by
  have empty : Safe [] := by
    intro before event after pos
    have lengths := congrArg List.length pos
    simp only [List.length_nil,List.length_append,List.length_cons] at lengths
    omega
  obtain ⟨suffix,full,safe,_⟩ := receive_safe msg src w a [] empty
  obtain ⟨seen,native⟩ := safe pre (.armed r) post position
  obtain ⟨before,after,splitHistory,index⟩ := lookup_position (history pre) r.origin
    (.callback r.kind r.peer) seen
  have projected := congrArg Prod.snd (receive_projects msg src w a [])
  rw [position] at projected
  have whole : (runWGPrefix (HandshakeCausal.receive msg src) w a []).2 =
      history pre ++ history post := by
    simpa only [history,List.filterMap_nil,List.filterMap_append,List.filterMap_cons,base] using projected
  have callback : (runWGPrefix (HandshakeCausal.receive msg src) w a []).2 =
      before ++ .callback r.kind r.peer :: (after ++ history post) := by
    rw [whole,splitHistory]
    simp only [List.append_assoc,List.cons_append]
  exact ⟨native,before,after,splitHistory,index,
    HandshakeCausal.callback_cause msg src w a before (after ++ history post) r.kind r.peer callback⟩

end Leanux.Proofs.WG.AuthenticatedEffects.TimerRoot
