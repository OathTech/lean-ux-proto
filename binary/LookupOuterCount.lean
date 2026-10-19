import SourceAdapter
import MirrorPeerPoints

namespace Binary.LookupOuterCount
open Leanux Leanux.WG MirrorHistory

def isOuter : Tag → Bool
  | .returned symbol => symbol == "wg_index_hashtable_lookup"
  | _ => false

def total (points : List Point) : Nat := (points.filter (fun p => isOuter p.tag)).length

@[simp] theorem total_append (xs ys : List Point) : total (xs ++ ys) = total xs + total ys := by
  simp [total, List.filter_append]

def Keeps (a : Logged α) : Prop := ∀ history w x points w',
  (a.run history).run w = .ok ((x,points),w') → total points = total history

theorem keeps_pure (x : α) : Keeps (pure x) := by
  intro history w y points w' run; cases run; rfl

theorem keeps_bind {a : Logged α} {f : α → Logged β}
    (ha : Keeps a) (hf : ∀ x, Keeps (f x)) : Keeps (a >>= f) := by
  intro history w y points w' run
  cases first : (a.run history).run w with
  | error e =>
    simp only [StateT.run_bind, first] at run
    change Except.error e = Except.ok ((y,points),w') at run
    contradiction
  | ok out =>
    obtain ⟨⟨x,middle⟩,intermediate⟩ := out
    simp only [StateT.run_bind, first] at run
    exact (hf x middle intermediate y points w' run).trans (ha history w x middle intermediate first)

theorem keeps_lift (a : M α) : Keeps (StateT.lift a) := by
  intro history w x points w' run
  cases actual : a.run w with
  | error e =>
    simp only [StateT.run_lift, StateT.run_bind, StateT.run_pure, actual] at run
    change Except.error e = Except.ok ((x,points),w') at run
    contradiction
  | ok out =>
    obtain ⟨value,after⟩ := out
    simp only [StateT.run_lift, StateT.run_bind, StateT.run_pure, actual] at run
    change Except.ok ((value,history),after) = Except.ok ((x,points),w') at run
    cases run; rfl

theorem keeps_mark (tag : Tag) (h : isOuter tag = false) : Keeps (mark tag) := by
  intro history w x points w' run
  rw [mark_run] at run; cases run
  simp [total, List.filter_append, h]

theorem keeps_called {a : Logged α} (symbol : String) (h : (symbol == "wg_index_hashtable_lookup") = false)
    (ha : Keeps a) : Keeps (called symbol a) := by
  unfold called
  apply keeps_bind (keeps_mark _ rfl); intro _
  apply keeps_bind ha; intro answer
  apply keeps_bind (keeps_mark (.returned symbol) h); intro _
  exact keeps_pure answer

theorem keeps_forIn (xs : List α) (b : β) (body : α → β → Logged (ForInStep β))
    (hb : ∀ x b, Keeps (body x b)) : Keeps (forIn xs b body) := by
  induction xs generalizing b with
  | nil => simpa only [List.forIn_nil] using keeps_pure b
  | cons x xs ih =>
    rw [List.forIn_cons]
    apply keeps_bind (hb x b); intro step
    cases step with
    | done value => exact keeps_pure value
    | yield value => exact ih value

theorem keeps_branch (d : Decision) (b : Bool) : Keeps (branchLogged d b) := by
  intro history w x points w' run
  rw [branch_run] at run; cases run
  simp [total, List.filter_append, isOuter]

theorem keeps_count (old : Nat) : Keeps (count old) := by
  intro history w answer points w' run
  have erased := count_erases old history w
  rw [run] at erased
  have actual : (refcountIncNotZero old : M Bool).run w = .ok (answer,w') := erased.symm
  have small := PeerMirror.accepted_count_bound old w w' answer actual
  rw [count_run_logged old history w small] at run
  cases run
  by_cases zero : old == 0 <;> simp [total, countPoints, List.filter_append, isOuter, zero]

theorem keeps_peerGet (peer : Option PeerId) : Keeps (peerGet peer) := by
  unfold MirrorHistory.peerGet
  apply keeps_bind (keeps_branch _ _)
  intro null
  cases null with
  | true => exact keeps_pure _
  | false =>
    cases peer with
    | none => exact keeps_lift _
    | some pid =>
      apply keeps_bind (keeps_lift _)
      intro _
      apply keeps_bind (keeps_lift _)
      intro p
      apply keeps_bind (keeps_count p.refcount)
      intro live
      apply keeps_bind (keeps_branch _ _)
      intro dead
      cases dead with
      | true => exact keeps_pure _
      | false =>
        apply keeps_bind (keeps_lift _)
        intro _
        exact keeps_pure _

theorem keeps_body (kinds : List IndexKind) (index : Nat)
    (e : IndexEntry) (a : LookupMirror.Acc) : Keeps (body kinds index e a) := by
  unfold body
  apply keeps_bind (keeps_branch _ _)
  intro _
  apply keeps_bind (keeps_branch _ _)
  intro hit
  cases hit with
  | false => exact keeps_pure _
  | true =>
    apply keeps_bind (keeps_branch _ _)
    intro good
    exact keeps_pure _

theorem keeps_finish (a : LookupMirror.Acc) : Keeps (finish a) := by
  unfold finish
  cases stop : a.2 <;> simp only [ Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  all_goals try (apply keeps_bind (keeps_branch .idxWalk false); intro _)
  all_goals
    apply keeps_bind (keeps_branch _ _)
    intro found
    cases found with
    | false => exact keeps_pure _
    | true =>
      cases h : a.1 with
      | none =>
        apply keeps_bind (keeps_lift _)
        intro _
        exact keeps_pure _
      | some e =>
        apply keeps_bind (keeps_lift _)
        intro word
        apply keeps_bind (keeps_called "wg_peer_get_maybe_zero" rfl (keeps_peerGet word))
        intro peer
        apply keeps_bind (keeps_lift _)
        intro _
        apply keeps_bind (keeps_branch _ _)
        intro alive
        cases alive with
        | false => exact keeps_pure _
        | true =>
          cases peer with
          | none =>
            apply keeps_bind (keeps_lift _)
            intro _
            exact keeps_pure _
          | some pid => exact keeps_pure _

theorem lookup_body_keeps (kinds : List IndexKind) (index : Nat) :
    Keeps (do
      let es ← StateT.lift (Source.indexBucket index)
      let a ← forIn es (none,false) (body kinds index)
      finish a) := by
  apply keeps_bind (keeps_lift _); intro es
  apply keeps_bind (keeps_forIn es (none,false) (body kinds index) (keeps_body kinds index))
  exact keeps_finish

theorem lookup_total (kinds : List IndexKind) (index : Nat)
    (world final : World) (answer : Option (IndexOwner × PeerId)) (points : List Point)
    (accepted : ((lookup kinds index).run []).run world = .ok ((answer,points),final)) :
    total points = 1 := by
  let action : Logged (Option (IndexOwner × PeerId)) := do
    let es ← StateT.lift (Source.indexBucket index)
    let a ← forIn es (none,false) (body kinds index)
    finish a
  change ((called "wg_index_hashtable_lookup" action).run []).run world = _ at accepted
  cases first : (action.run [⟨.call "wg_index_hashtable_lookup", world⟩]).run world with
  | error e =>
    have err : ((called "wg_index_hashtable_lookup" action).run []).run world = .error e := by
      simp [called, mark, StateT.run_bind, first]
      rfl
    rw [err] at accepted
    cases accepted
  | ok out =>
    obtain ⟨⟨value,middle⟩,intermediate⟩ := out
    have kept := lookup_body_keeps kinds index [⟨.call "wg_index_hashtable_lookup", world⟩]
      world value middle intermediate first
    have result : @Except.ok Stop _ ((value, middle ++ [⟨.returned "wg_index_hashtable_lookup", intermediate⟩]), intermediate) =
        Except.ok ((answer, points), final) := by
      change (do
        let out : (Option (IndexOwner × PeerId) × List Point) × World ← (action.run [⟨.call "wg_index_hashtable_lookup", world⟩]).run world
        pure ((out.1.1, out.1.2 ++ [({tag := .returned "wg_index_hashtable_lookup", world := out.2} : Point)]), out.2)) = _ at accepted
      rw [first] at accepted
      exact accepted
    cases result
    simp [total, List.filter_append, isOuter] at kept ⊢
    exact kept

#print axioms lookup_total
end Binary.LookupOuterCount
