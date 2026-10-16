import AllowedipsSourceSelected

namespace Binary.AllowedipsOuterCount
open Leanux Leanux.WG MirrorHistory

def isOuter : Tag → Bool
  | .returned symbol => symbol == "lookup"
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

theorem keeps_called {a : Logged α} (symbol : String) (h : (symbol == "lookup") = false)
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
  have actual : (refcountIncNotZero old).run w = .ok (answer,w') := erased.symm
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


open AllowedipsSource

theorem keeps_swap (bits : Nat) : Keeps (AllowedipsSource.swapEndian bits) := by
  unfold AllowedipsSource.swapEndian
  apply keeps_bind (keeps_branch _ _)
  intro b
  cases b with
  | true => exact keeps_pure _
  | false =>
    apply keeps_bind (keeps_branch _ _)
    intro _
    exact keeps_pure _

theorem keeps_common (node : AipNode) (key bits : Nat) : Keeps (AllowedipsSource.commonBits node key bits) := by
  unfold AllowedipsSource.commonBits
  apply keeps_bind (keeps_branch _ _)
  intro first
  cases first with
  | true => exact keeps_pure _
  | false =>
    apply keeps_bind (keeps_branch _ _)
    intro second
    cases second with
    | false => exact keeps_pure _
    | true =>
      apply keeps_bind (keeps_branch _ _)
      intro high
      cases high <;> simpa using keeps_pure (α := Nat) _

theorem keeps_prefix (node : AipNode) (key bits : Nat) : Keeps (AllowedipsSource.prefixMatches node key bits) := by
  unfold AllowedipsSource.prefixMatches
  apply keeps_bind (keeps_called "common_bits" rfl (keeps_common node key bits))
  intro value
  exact keeps_pure _

theorem keeps_iteration (bits key : Nat) (acc : Acc) : Keeps (iteration bits key acc) := by
  unfold iteration
  cases acc.2.1 with
  | none =>
    apply keeps_bind (keeps_branch _ _)
    intro _
    exact keeps_pure _
  | some id =>
    apply keeps_bind (keeps_branch _ _)
    intro _
    apply keeps_bind (keeps_lift _)
    intro node
    apply keeps_bind (keeps_prefix node key bits)
    intro matching
    apply keeps_bind (keeps_branch _ _)
    intro matching
    cases matching with
    | false => exact keeps_pure _
    | true =>
      apply keeps_bind (keeps_branch _ _)
      intro hasPeer
      cases hasPeer <;> apply keeps_bind (keeps_branch _ _) <;> intro full
      all_goals cases full with
      | true => exact keeps_pure _
      | false =>
        apply keeps_bind (keeps_lift _)
        intro bit
        apply keeps_bind (keeps_lift _)
        intro next
        exact keeps_pure _

theorem keeps_loop (bits key fuel : Nat) (acc : Acc) : Keeps (loop bits key fuel acc) := by
  induction fuel generalizing acc with
  | zero => exact keeps_pure _
  | succ fuel ih =>
    unfold loop
    apply keeps_bind (keeps_iteration bits key acc)
    intro step
    cases step with
    | done answer => exact keeps_pure _
    | yield next => exact ih next

theorem keeps_find (root : Option NodeId) (bits key : Nat) : Keeps (AllowedipsSource.findNode root bits key) := by
  rw [findNode_bounded]
  apply keeps_bind (keeps_loop bits key 130 _)
  intro acc
  unfold AllowedipsSource.finish
  cases acc.1 with
  | none => exact keeps_lift _
  | some answer => exact keeps_pure _

theorem keeps_search (root : Option NodeId) (bits key : Nat) : Keeps (searchPrefix root bits key) := by
  unfold searchPrefix
  apply keeps_bind (keeps_swap bits)
  intro _
  apply keeps_bind (keeps_find root bits key)
  intro node
  apply keeps_bind (keeps_branch _ _)
  intro _
  exact keeps_pure _

theorem keeps_suffix (node : Option NodeId) : Keeps (searchSuffix node) := by
  cases node with
  | none => exact keeps_pure _
  | some id =>
    unfold searchSuffix
    apply keeps_bind (keeps_lift _)
    intro node
    apply keeps_bind (keeps_called "wg_peer_get_maybe_zero" rfl (keeps_peerGet node.peer))
    intro peer
    unfold afterPeer
    apply keeps_bind (keeps_branch _ _)
    intro gone
    cases gone with
    | false => exact keeps_pure _
    | true =>
      apply keeps_bind (keeps_lift _)
      intro _
      exact keeps_pure _

theorem lookup_total (root : Option NodeId) (bits key : Nat)
    (world final : World) (answer : Option PeerId) (points : List Point)
    (accepted : ((AllowedipsSource.lookup root bits key).run []).run world =
      .ok ((answer,points),final)) : total points = 1 := by
  rw [lookup_split] at accepted
  obtain ⟨middle,run,recorded⟩ := called_accepted accepted
  have kept := keeps_bind (keeps_search root bits key) keeps_suffix
    [⟨.call "lookup",world⟩] world answer middle final run
  rw [recorded]
  simp [total,isOuter,List.filter_append] at kept ⊢
  exact kept

#print axioms lookup_total
end Binary.AllowedipsOuterCount
