import AllowedipsSourceFrames

namespace Binary.AllowedipsSource
open Leanux Leanux.WG MirrorHistory LookupSourceFrame
set_option maxHeartbeats 2000000

def nodeView (w : World) : NodeView :=
  fun id => w.k.wg.bind fun device => device.nodes.get? id

theorem prefixMatches_run (node : AipNode) (key bits : Nat) (history : List Point) (w : World) :
    ((prefixMatches node key bits).run history).run w =
      let final := records w (commonChoices node key bits)
      .ok ((decide (commonValue node key bits ≥ node.cidr),
        history ++ [⟨.call "common_bits",w⟩] ++ choicePoints w (commonChoices node key bits) ++
          [⟨.returned "common_bits",final⟩]),final) := by
  have callRun := called_run "common_bits" (commonBits node key bits) w
    (records w (commonChoices node key bits)) (commonValue node key bits)
    (choicePoints w (commonChoices node key bits)) (commonBits_run node key bits · w) history
  unfold prefixMatches
  simp only [StateT.run_bind, callRun]
  rfl

theorem records_kernel (w : World) (choices : Choices) : (records w choices).k = w.k :=
  by
    have eq := congrArg World.k (records_world w choices)
    exact eq

theorem records_steps (w : World) (choices : Choices) :
    records w choices = {w with steps := w.steps ++
      (choices.map fun (d,b) => ({decision := d, outcome := b, netRx := w.netRxSection} : Step)).toArray} := by
  induction choices generalizing w with
  | nil => simp [records]
  | cons choice rest ih =>
    rcases choice with ⟨d,b⟩
    simp [records, ih, LookupMirror.record]

private theorem except_ok_bind (value : α) (f : α → Except Stop β) :
    (Except.ok value >>= f) = f value := rfl

private theorem except_pure (value : α) : (pure value : Except Stop α) = .ok value := rfl

private theorem except_map (f : α → β) (value : α) :
    f <$> (Except.ok value : Except Stop α) = .ok (f value) := rfl

private theorem throw_run (e : Stop) (w : World) : (throw e : M α).run w = .error e := rfl

private theorem except_error_bind (e : Stop) (f : α → Except Stop β) :
    (Except.error e >>= f) = .error e := rfl

theorem iteration_select (bits key : Nat) (acc : Acc) (history : List Point) (w : World) :
    (((iteration bits key acc).run history).run w).toOption.map (fun r => r.1.1) =
      selectStep (nodeView w) bits key acc := by
  rcases acc with ⟨answer,current,found⟩
  cases current with
  | none => rfl
  | some id =>
    cases device : w.k.wg with
    | none =>
      simp [iteration, selectStep, nodeView, branchLogged, mark, branch,
        getNode, getDev, getK, device, invariant, Except.toOption]
      rfl
    | some dev =>
      cases node : dev.nodes.get? id with
      | none =>
        have absent : dev.nodes[id]? = none := node
        simp [iteration, selectStep, nodeView, branchLogged, mark, branch,
          getNode, getDev, getK, device, absent, invariant, Except.toOption]
        rfl
      | some n =>
        have present : dev.nodes[id]? = some n := node
        by_cases mismatch : commonValue n key bits < n.cidr <;>
          cases hasPeer : n.peer.isSome <;>
          by_cases full : n.cidr = bits <;>
          by_cases invalid : n.cidr ≥ n.bitlen <;>
          cases child : n.bit[key / 2^(n.bitlen-1-n.cidr) % 2]?
        all_goals
          try simp only [full] at mismatch
          simp [-Option.map_eq_some_iff, iteration, StateT.run_lift, StateT.run_bind, StateT.run_pure,
            getNode, getDev, getK, LookupMirror.record, device, present,
            prefixMatches_run, selectStep, nodeView, Except.toOption,
            branchLogged, mark, branch, choose, AipNode.bitAt, invariant,
            records_steps, except_ok_bind, except_pure, except_map, throw_run,
            except_error_bind, mismatch, hasPeer, full, invalid, child]
        all_goals rfl

#print axioms iteration_select

theorem loop_select_accepted (bits key fuel : Nat) (acc result : Acc)
    (history points : List Point) (w final : World)
    (prior : ∀ p ∈ history, p.world.k = w.k)
    (accepted : ((loop bits key fuel acc).run history).run w = .ok ((result,points),final)) :
    selectLoop (nodeView w) bits key fuel acc = some result := by
  induction fuel generalizing acc result history points w final with
  | zero =>
    change Except.ok ((acc,history),w) = Except.ok ((result,points),final) at accepted
    cases accepted
    rfl
  | succ fuel ih =>
    obtain ⟨step,middle,intermediate,first,rest⟩ :=
      loop_succ_accepted bits key fuel acc result history points w final accepted
    have selected := iteration_select bits key acc history w
    rw [first] at selected
    change some step = selectStep (nodeView w) bits key acc at selected
    have framed := frames_iteration id bits key acc w.k history w step middle intermediate
      rfl prior first
    have kernel : intermediate.k = w.k := framed.1
    have viewEq : nodeView intermediate = nodeView w := by
      funext id
      simp only [nodeView, kernel]
    rw [selectLoop, ← selected]
    cases step with
    | done answer =>
      obtain ⟨rfl,rfl,rfl⟩ := rest
      rfl
    | yield next =>
      have nextPrior : ∀ p ∈ middle, p.world.k = intermediate.k := by
        intro p member
        exact (framed.2 p member).trans framed.1.symm
      have recursive := ih next result middle points intermediate final nextPrior rest
      rw [viewEq] at recursive
      exact recursive

/-- Selection follows the actual accepted bounded loop. The only history
    invariant used by induction is discharged by the source frame theorem. -/
theorem findNode_logged_select (trie : Option NodeId) (bits key : Nat)
    (w final : World) (answer : Option NodeId) (points : List Point)
    (accepted : ((findNode trie bits key).run []).run w = .ok ((answer,points),final)) :
    select (nodeView w) trie bits key = some answer ∧ final.k = w.k := by
  have frame := findNode_kernel trie bits key w final answer points accepted
  rw [findNode_bounded] at accepted
  obtain ⟨acc,middle,intermediate,ran,finished⟩ := accepted_bind _ _ _ _ _ accepted
  have selected := loop_select_accepted bits key 130 (none,trie,none) acc [] middle w intermediate
    (by intro p member; cases member) ran
  refine ⟨?_,frame.1⟩
  unfold select
  rw [selected]
  change acc.1 = some answer
  cases returned : acc.1 with
  | none =>
    simp only [finish, returned, StateT.run_lift, invariant] at finished
    cases finished
  | some found =>
    simp only [finish, returned] at finished
    change Except.ok ((found,middle),intermediate) = Except.ok ((answer,points),final) at finished
    have eq := congrArg (fun p => p.1.1) (Except.ok.inj finished)
    exact congrArg some eq

/-- No heap/termination premise is added: accepted execution of the actual
    mirror supplies selection, while the complete Kernel is unchanged. -/
theorem findNode_accepted_select (trie : Option NodeId) (bits key : Nat)
    (w final : World) (answer : Option NodeId)
    (accepted : (WG.findNode trie bits key).run w = .ok (answer,final)) :
    select (nodeView w) trie bits key = some answer ∧ final.k = w.k := by
  obtain ⟨points,logged⟩ := accepted_logged (findNode_erases trie bits key) [] w final answer accepted
  exact findNode_logged_select trie bits key w final answer points logged

#print axioms loop_select_accepted
#print axioms findNode_logged_select
#print axioms findNode_accepted_select
end Binary.AllowedipsSource
