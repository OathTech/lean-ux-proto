import PairTrieFrame
import AllowedipsLoopBody
import AllowedipsSourceSteps
import AllowedipsSourceSelect

namespace Binary.Pair.Trie
open Leanux Leanux.WG AllowedipsRelation
local instance : Labels := Image.linkedLabels

/-- Control state at a header or the common loop exit. Decisions and callback
interiors are not observations of this sequential sibling. -/
def Position (c : AllowedipsRelation.Config) (view : AllowedipsSource.NodeView)
    (acc : AllowedipsSource.Acc) (s : MachineState) : Prop :=
  s.data.regs.rbp.toBitVec = AllowedipsRelation.pointer c.nodes acc.2.2 ∧
  if acc.1.isSome then s.pc = AllowedipsImage.Lookup.entry+0x101
  else match acc.2.1 with
    | none => s.pc = AllowedipsImage.Lookup.entry+0x101
    | some id => s.pc = AllowedipsImage.Lookup.entry+0xd5 ∧
      s.data.regs.rbx.toBitVec = c.nodes id ∧ Reached view c.root c.bits c.key id

structure Invariant (n : Names) (o : AllowedipsProbe.Offsets) (d : Device)
    (base : MachineData) (coverage : CommonBitsCoverage.Context) (c : AllowedipsRelation.Config)
    (acc : AllowedipsSource.Acc) (s : Executed) : Prop where
  position : Position c (fun id => d.nodes.get? id) acc s.machine
  frame : AllowedipsLoop.Frame base coverage s.machine.data
  related : Corresponds n o s.machine.data.dmem d
  observed : ∃ events, observeHistory (AllowedipsObservation.edge c.rxSection) s.history = .ok events
  last : s.history.getLast? = some s.machine

theorem next_position (c : AllowedipsRelation.Config) (view : AllowedipsSource.NodeView)
    (family : c.bits = 32 ∨ c.bits = 128) (id : NodeId) (previous : Option NodeId)
    (node : AipNode) (present : view id = some node)
    (reached : Reached view c.root c.bits c.key id)
    (step : ForInStep AllowedipsSource.Acc)
    (selected : AllowedipsSource.selectStep view c.bits c.key (none,some id,previous) = some step)
    (s : MachineState) (post : AllowedipsLoop.StepPost c.nodes step s) :
    Position c view (match step with | .done a => a | .yield a => a) s := by
  cases step with
  | done acc =>
    have shape := AllowedipsSource.done_shape view c.bits c.key id previous node acc present selected
    exact ⟨post.2, by simp only [shape,Option.isSome_some,↓reduceIte]; exact post.1⟩
  | yield acc =>
    obtain ⟨empty,matching,short,child,remembered⟩ :=
      AllowedipsSource.yield_shape view c.bits c.key id previous node acc present selected
    refine ⟨post.2.2,?_⟩
    simp only [empty,Option.isSome_none,Bool.false_eq_true,↓reduceIte]
    cases current : acc.2.1 with
    | none => simpa only [current,Option.isSome_none,Bool.false_eq_true,↓reduceIte] using post.1
    | some next =>
      have bound := AllowedipsLoop.common_bound c.bits node.bits c.key family
      have less : node.cidr < c.bits := by omega
      refine ⟨?_,?_,.child id node next reached present matching less ?_⟩
      · simpa only [current,Option.isSome_some,↓reduceIte] using post.1
      · simpa only [current,AllowedipsRelation.pointer,Option.map_some,Option.getD_some] using post.2.1
      · simpa only [current] using child

/-- Compose the actual physical node body with the exact tested decoder.
The old physical setup remains explicit: this theorem does not yet derive
its load premises from successful reconstruction. -/
theorem node_effect (fetch : Int64 → Option Decoded)
    (n : Names) (o : AllowedipsProbe.Offsets) (d : Device)
    (base : MachineData) (coverage : CommonBitsCoverage.Context) (c : AllowedipsRelation.Config)
    (setup : AllowedipsLoop.Setup fetch base coverage c (fun id => d.nodes.get? id))
    (related : Corresponds n o base.dmem d)
    (apart : ∀ a, ReadBytes n o a → ¬AllowedipsLoop.writes base.regs.rsp coverage a)
    (id : NodeId) (previous : Option NodeId) (step : ForInStep AllowedipsSource.Acc)
    (selected : AllowedipsSource.selectStep (fun id => d.nodes.get? id) c.bits c.key
      (none,some id,previous) = some step)
    (s : Executed) (initial : Invariant n o d base coverage c (none,some id,previous) s) :
    Eventually (historyStep fetch)
      (Invariant n o d base coverage c (match step with | .done a => a | .yield a => a)) s := by
  obtain ⟨previousAt,pc,cursor,reached⟩ := initial.position
  obtain ⟨events,observed⟩ := initial.observed
  have body := AllowedipsLoop.node_body fetch base s.machine.data coverage c
    (fun id => d.nodes.get? id) setup id previous reached cursor previousAt initial.frame
    s.history events observed (by rw [←pc]; exact initial.last)
  rw [AllowedipsLoop.cursor_eq s _ pc] at body
  apply eventually_weaken (historyStep fetch) _ _ _ _ body
  rintro t ⟨node,actual,delta,present,chosen,post,signature,trace⟩
  have eq : actual = step := Option.some.inj (chosen.symm.trans selected)
  subst actual
  have position := next_position c _ setup.heap.1 id previous node present reached step selected t.machine post
  have reconstructed := (reconstruct_frame n o trace.frame.memory apart).symm.trans related
  cases step <;> exact ⟨position,trace.frame,reconstructed,⟨events++delta,trace.observed⟩,trace.last⟩

/-- New bounded-loop join. All binary successors come from node_effect;
the source supplies only its accepted finite selection. Fuel exhaustion
does not manufacture a return (the finish theorem below requires a result).
Undefined instruction values remain universally quantified by Effects.All. -/
theorem loop_effect (fetch : Int64 → Option Decoded)
    (n : Names) (o : AllowedipsProbe.Offsets) (d : Device)
    (base : MachineData) (coverage : CommonBitsCoverage.Context) (c : AllowedipsRelation.Config)
    (setup : AllowedipsLoop.Setup fetch base coverage c (fun id => d.nodes.get? id))
    (related : Corresponds n o base.dmem d)
    (apart : ∀ a, ReadBytes n o a → ¬AllowedipsLoop.writes base.regs.rsp coverage a)
    (fuel : Nat) (acc result : AllowedipsSource.Acc) (openLoop : acc.1 = none)
    (selected : AllowedipsSource.selectLoop (fun id => d.nodes.get? id) c.bits c.key fuel acc = some result)
    (s : Executed) (initial : Invariant n o d base coverage c acc s) :
    Eventually (historyStep fetch) (Invariant n o d base coverage c result) s := by
  induction fuel generalizing acc result s with
  | zero =>
    have eq : acc = result := Option.some.inj selected
    subst result
    exact .done _ initial
  | succ fuel ih =>
    rcases acc with ⟨answer,current,previous⟩
    change answer = none at openLoop
    subst answer
    cases current with
    | none =>
      have eq : (some previous,none,previous) = result := Option.some.inj selected
      subst result
      exact .done _ {initial with position := ⟨initial.position.1,initial.position.2⟩}
    | some id =>
      cases choice : AllowedipsSource.selectStep (fun id => d.nodes.get? id) c.bits c.key (none,some id,previous) with
      | none =>
        rw [AllowedipsSource.selectLoop,choice] at selected
        cases selected
      | some step =>
        have body := node_effect fetch n o d base coverage c setup related apart id previous step choice s initial
        cases step with
        | done next =>
          rw [AllowedipsSource.selectLoop,choice] at selected
          have eq : next = result := Option.some.inj selected
          subst next
          exact body
        | yield next =>
          rw [AllowedipsSource.selectLoop,choice] at selected
          have rest : AllowedipsSource.selectLoop (fun id => d.nodes.get? id) c.bits c.key fuel next = some result := selected
          have reached := initial.position.2.2.2
          obtain ⟨node,present,_⟩ := setup.heap.2.2 id reached
          have empty := (AllowedipsSource.yield_shape _ c.bits c.key id previous node next present choice).1
          apply eventually_trans (historyStep fetch) _ _ _ body
          intro t invariant
          exact ih next result empty rest t invariant

#print axioms node_effect
#print axioms loop_effect

/-- A successful call of the actual mirror supplies the bounded-loop
selection and successful finish. This theorem starts at the loop boundary,
not at the function ABI entry, and stops before peer-get and BH-enable. -/
theorem findNode_effect (fetch : Int64 → Option Decoded)
    (n : Names) (o : AllowedipsProbe.Offsets) (d : Device)
    (base : MachineData) (coverage : CommonBitsCoverage.Context) (c : AllowedipsRelation.Config)
    (setup : AllowedipsLoop.Setup fetch base coverage c (fun id => d.nodes.get? id))
    (related : Corresponds n o base.dmem d)
    (apart : ∀ a, ReadBytes n o a → ¬AllowedipsLoop.writes base.regs.rsp coverage a)
    (w final : World) (answer : Option NodeId) (device : w.k.wg = some d)
    (accepted : (WG.findNode c.root c.bits c.key).run w = .ok (answer,final))
    (s : Executed) (initial : Invariant n o d base coverage c (none,c.root,none) s) :
    Eventually (historyStep fetch) (fun t =>
      t.machine.pc = AllowedipsImage.Lookup.entry+0x101 ∧
      t.machine.data.regs.rbp.toBitVec = AllowedipsRelation.pointer c.nodes answer ∧
      reconstruct n o t.machine.data.dmem = .ok (target d) ∧
      final.k.wg = some d ∧ AllowedipsLoop.Frame base coverage t.machine.data) s := by
  obtain ⟨selected,frame⟩ := AllowedipsSource.findNode_accepted_select c.root c.bits c.key w final answer accepted
  have view : AllowedipsSource.nodeView w = (fun id => d.nodes.get? id) := by
    funext id
    simp only [AllowedipsSource.nodeView,device,Option.bind_some]
  rw [view] at selected
  unfold AllowedipsSource.select at selected
  cases choice : AllowedipsSource.selectLoop (fun id => d.nodes.get? id) c.bits c.key 130 (none,c.root,none) with
  | none => rw [choice] at selected; cases selected
  | some acc =>
    rw [choice] at selected
    change acc.1 = some answer at selected
    have body := loop_effect fetch n o d base coverage c setup related apart 130
      (none,c.root,none) acc rfl choice s initial
    apply eventually_weaken (historyStep fetch) _ _ _ _ body
    intro t invariant
    -- A done source accumulator contains its remembered node. This also
    -- rules out treating exhausted fuel as a successful findNode return.
    have completed : acc.1 = some acc.2.2 := by
      have shape : ∀ fuel current found result,
          AllowedipsSource.selectLoop (fun id => d.nodes.get? id) c.bits c.key fuel (none,current,found) = some result →
          result.1.isSome → result.1 = some result.2.2 := by
        intro fuel
        induction fuel with
        | zero =>
          intro current found result run finished
          have eq : (none,current,found) = result := Option.some.inj run
          subst result
          cases finished
        | succ fuel ih =>
          intro current found result run finished
          cases current with
          | none =>
            have eq : (some found,none,found) = result := Option.some.inj run
            subst result
            rfl
          | some id =>
            cases present : d.nodes.get? id with
            | none =>
              simp only [AllowedipsSource.selectLoop,AllowedipsSource.selectStep,present] at run
              cases run
            | some node =>
              cases step : AllowedipsSource.selectStep (fun id => d.nodes.get? id) c.bits c.key (none,some id,found) with
              | none => rw [AllowedipsSource.selectLoop,step] at run; cases run
              | some next =>
                rw [AllowedipsSource.selectLoop,step] at run
                cases next with
                | done answer =>
                  have eq : answer = result := Option.some.inj run
                  subst result
                  exact AllowedipsSource.done_shape _ c.bits c.key id found node answer present step
                | yield next =>
                  have empty := (AllowedipsSource.yield_shape _ c.bits c.key id found node next present step).1
                  rcases next with ⟨early,child,previous⟩
                  change early = none at empty
                  subst early
                  exact ih child previous result run finished
      exact shape 130 c.root none acc choice (by simp only [selected,Option.isSome_some])
    have remembered : acc.2.2 = answer := Option.some.inj (completed.symm.trans selected)
    refine ⟨?_,?_,invariant.related,?_,invariant.frame⟩
    · simpa only [Position,selected,Option.isSome_some,↓reduceIte] using invariant.position.2
    · simpa only [remembered] using invariant.position.1
    · rw [frame]
      exact device

#print axioms findNode_effect
end Binary.Pair.Trie
