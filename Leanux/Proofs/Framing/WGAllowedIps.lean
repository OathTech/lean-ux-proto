import Leanux.Proofs.Framing.Tools
import Leanux.Proofs.Framing.WGKernel
import Leanux.Proofs.Framing.Lift
import Leanux.Proofs.WG.AllowedIps.RemovalSource
import Lean

/-! Native trie observations: read-only leaves retain the complete AipStore;
mutating leaves retain its frontier. The WG adapter carries the original
seven-field masked observation through the actual guarded lift. -/
namespace Leanux.Proofs.Framing
open Leanux Leanux.WG Std.Do

def nodeDevice (d : Device) : Device := {d with nodes := {}, peerAllowedips := {}}

def nodeView (g : WGWorld) : WGStoreView := {wgStoreView g with dev := g.dev.map nodeDevice}

abbrev SameNode (a : WG.M α) := SameView nodeView a

theorem modifyDev_node_spec (P : WGStoreView → Prop) (f : Device → Device)
    (hf : ∀ d, nodeDevice (f d) = nodeDevice d) :
    ⦃fun w => ⌜P (nodeView w)⌝⦄ modifyDev f
    ⦃⇓? _ w => ⌜P (nodeView w)⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient x w' ambient' hp hr
  cases hr
  simpa [nodeView, wgStoreView, modifyDev, Option.map_map, Function.comp_def, hf] using hp

theorem getNode_sameAipStore (id : NodeId) :
    SameView (fun s : AipStore => s) (getNode id) := by
  apply SameView.of_wp
  intro initial
  mvcgen [getNode, invariant, AmbientM.invariant]

theorem setNode_sameNextNode (id : NodeId) (n : AipNode) :
    SameView AipStore.nextNode (setNode id n) := by
  apply SameView.of_wp
  intro initial
  mvcgen [setNode]

theorem freeNode_sameNextNode (id : NodeId) :
    SameView AipStore.nextNode (freeNode id) := by
  unfold freeNode
  apply SameView.bind ((getNode_sameAipStore id).factor AipStore.nextNode)
  intro _
  apply SameView.of_wp
  intro initial
  mvcgen

theorem slotGet_sameAipStore (s : Slot) :
    SameView (fun s : AipStore => s) (slotGet s) := by
  apply SameView.of_wp
  intro initial
  have hn := fun id => (getNode_sameAipStore id).wp (fun s => s = initial)
  have ha (α : Type) (a : AmbientM α) :
      ⦃fun s : AipStore => ⌜s = initial⌝⦄ (MonadLift.monadLift a : AipM α)
      ⦃⇓? _ s => ⌜s = initial⌝⦄ := hoare_liftAmbient a _
  mvcgen [-Std.Do.Spec.monadLift_StateT, slotGet, hn, AipNode.bitAt, ha, invariant]

theorem slotSet_sameNextNode (s : Slot) (v : Option NodeId) :
    SameView AipStore.nextNode (slotSet s v) := by
  apply SameView.of_wp
  intro initial
  have hn := fun id => ((getNode_sameAipStore id).factor AipStore.nextNode).wp (fun s => s = initial)
  have hs := fun id n => (setNode_sameNextNode id n).wp (fun s => s = initial)
  mvcgen [slotSet, hn, hs, invariant, AmbientM.invariant]

theorem liftAip_sameNode {a : AipM α} (ha : SameView AipStore.nextNode a) :
    SameNode (liftAip a) := by
  apply (Leanux.Proofs.WG.Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g ambient x g' ambient' hr
  rw [liftAip_run] at hr
  cases hd : g.dev with
  | none => simp [hd] at hr
  | some d =>
    simp only [hd] at hr
    cases he : (a.run {nodes := d.nodes, nextNode := d.nextNode, trie := d.peerAllowedips}).run ambient with
    | error e => simp [he, Except.map] at hr
    | ok out =>
      rcases out with ⟨⟨y, s⟩, b⟩
      simp [he, Except.map] at hr
      rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
      have hn := (Leanux.Proofs.WG.Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mp ha _ _ _ _ _ he
      simp only [nodeView, wgStoreView, hd, Option.map_some, nodeDevice]
      simp only at hn
      rw [hn]

theorem subtree_sameAipStore (nodeId : NodeId) :
    SameView (fun s : AipStore => s) (subtree nodeId) := by
  apply SameView.of_wp
  intro initial
  have hn := fun node => (getNode_sameAipStore node).wp (fun s => s = initial)
  have hl (α β : Type) := list_view_spec (m := AmbientM) (fun s : AipStore => s)
    (α := α) (β := β) (fun s => s = initial)
  mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list,
    subtree, hn, hl, invariant, AmbientM.invariant]
  all_goals try exact ((⇓? _ s => ⌜s = initial⌝) :
    PostCond _ (.arg AipStore (.arg Ambient (.except Stop .pure))))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all

theorem removeParentTail_sameNode (parent : NodeId) (sibling : Option NodeId) :
    SameNode (Leanux.Proofs.WG.AllowedIps.removeParentTail parent sibling) := by
  apply SameView.of_wp
  intro initial
  have hn (node : NodeId) :
      ⦃fun g => ⌜nodeView g = initial⌝⦄ (MonadLift.monadLift (getNode node) : WG.M AipNode)
      ⦃⇓? _ g => ⌜nodeView g = initial⌝⦄ :=
    (liftAip_sameNode ((getNode_sameAipStore node).factor AipStore.nextNode)).wp (fun s => s = initial)
  have hs (node : NodeId) (n : AipNode) :
      ⦃fun g => ⌜nodeView g = initial⌝⦄ (MonadLift.monadLift (setNode node n) : WG.M Unit)
      ⦃⇓? _ g => ⌜nodeView g = initial⌝⦄ :=
    (liftAip_sameNode (setNode_sameNextNode node n)).wp (fun s => s = initial)
  have hslot (s : Slot) (v : Option NodeId) :
      ⦃fun g => ⌜nodeView g = initial⌝⦄ (MonadLift.monadLift (slotSet s v) : WG.M Unit)
      ⦃⇓? _ g => ⌜nodeView g = initial⌝⦄ :=
    (liftAip_sameNode (slotSet_sameNextNode s v)).wp (fun s => s = initial)
  have hf (node : NodeId) :
      ⦃fun g => ⌜nodeView g = initial⌝⦄ (MonadLift.monadLift (freeNode node) : WG.M Unit)
      ⦃⇓? _ g => ⌜nodeView g = initial⌝⦄ :=
    (liftAip_sameNode (freeNode_sameNextNode node)).wp (fun s => s = initial)
  have ha (α : Type) (a : AmbientM α) :
      ⦃fun g : WGWorld => ⌜nodeView g = initial⌝⦄ (MonadLift.monadLift a : WG.M α)
      ⦃⇓? _ g => ⌜nodeView g = initial⌝⦄ := hoare_liftAmbient a _
  mvcgen [-Std.Do.Spec.monadLift_StateT, Leanux.Proofs.WG.AllowedIps.removeParentTail,
    hn, hs, hslot, hf, branch, ha]

/- Head-only composition for the removal suffix. Each actual shared
continuation receives one checked frame proof before its uses are discharged. -/
open Lean Meta Elab Tactic in
elab "frame_node_remove" : tactic => do
  while !(← getGoals).isEmpty do
    withMainContext do
      let goal ← getMainGoal
      let target := (← instantiateMVars (← goal.getType)).consumeMData
      if target.isForall then
        evalTactic (← `(tactic| intro))
        return
      let .app property action := target | throwError "missing node action"
      let action := action.consumeMData
      if let .letE name ty value body _ := action then
        if name.toString.startsWith "__do_jp" then
          let claim ← forallTelescope ty fun args _ =>
            mkForallFVars args (mkApp property (mkAppN value args))
          let proof ← mkFreshExprSyntheticOpaqueMVar claim
          let (continuation, next) ← withLocalDeclD name ty fun f => do
            let claim ← forallTelescope ty fun args _ =>
              mkForallFVars args (mkApp property (mkAppN f args))
            withLocalDeclD `node_join claim fun hf => do
              let next ← mkFreshExprSyntheticOpaqueMVar (mkApp property (body.instantiate1 f))
              return (← mkLambdaFVars #[f, hf] next, next.mvarId!)
          goal.assign (mkApp2 continuation value proof)
          replaceMainGoal [proof.mvarId!, next]
        else
          replaceMainGoal [← goal.replaceTargetDefEq (mkApp property (body.instantiate1 value))]
        return
      if let .letE _ _ value body _ := action.getAppFn.consumeMData then
        let next := mkAppN (body.instantiate1 value) action.getAppArgs
        replaceMainGoal [← goal.replaceTargetDefEq (mkApp property next)]
        return
      let reduced := action.headBeta
      if !Expr.equal action reduced then
        replaceMainGoal [← goal.replaceTargetDefEq (mkApp property reduced)]
        return
      if action.getAppFn.isFVar then
        let mut found := false
        for decl in ← getLCtx do
          if decl.userName == `node_join then
            let proof := mkAppN decl.toExpr action.getAppArgs
            try
              if ← withReducible (isDefEq (← inferType proof) target) then
                goal.assign proof
                replaceMainGoal []
                found := true
                break
            catch _ => pure ()
        unless found do throwError "missing node continuation contract"
        return
      let head := action.getAppFn.constName?
      if head == some ``Bind.bind then
        evalTactic (← `(tactic| refine SameView.bind ?_ ?_))
      else if head == some ``Pure.pure then
        evalTactic (← `(tactic| exact SameView.pure nodeView _))
      else if head == some ``ite then
        evalTactic (← `(tactic| split))
      else if head == some ``Leanux.Proofs.WG.AllowedIps.removeParentTail then
        evalTactic (← `(tactic| exact removeParentTail_sameNode _ _))
      else if head == some ``AipNode.bitAt then
        evalTactic (← `(tactic| unfold AipNode.bitAt))
      else if head == some ``liftM then
        evalTactic (← `(tactic| unfold liftM))
      else if head == some ``MonadLift.monadLift || head == some ``MonadLiftT.monadLift then
        let some lifted := action.getAppArgs.back? | throwError "missing lifted action"
        let liftedHead := lifted.consumeMData.getAppFn.constName?
        if liftedHead == some ``getNode then
          evalTactic (← `(tactic| exact $(mkIdent `hn) _))
        else if liftedHead == some ``setNode then
          evalTactic (← `(tactic| exact $(mkIdent `hs) _ _))
        else if liftedHead == some ``slotSet then
          evalTactic (← `(tactic| exact $(mkIdent `hslot) _ _))
        else if liftedHead == some ``freeNode then
          evalTactic (← `(tactic| exact $(mkIdent `hf) _))
        else
          evalTactic (← `(tactic| exact $(mkIdent `ha) _))
      else if head == some ``branch || head == some ``invariant then
        evalTactic (← `(tactic| exact $(mkIdent `ha) _))
      else if (← Lean.Meta.matchMatcherApp? action).isSome then
        replaceMainGoal (← Lean.Meta.Split.splitMatch goal action)
      else
        throwError "unhandled node action head {head}"

theorem removeNodeBody_sameNode (nodeId : NodeId) :
    SameNode (Leanux.Proofs.WG.AllowedIps.removeNodeBody nodeId) := by
  have hn (node : NodeId) :
      SameNode (MonadLift.monadLift (getNode node) : WG.M AipNode) :=
    liftAip_sameNode ((getNode_sameAipStore node).factor AipStore.nextNode)
  have hs (node : NodeId) (n : AipNode) :
      SameNode (MonadLift.monadLift (setNode node n) : WG.M Unit) :=
    liftAip_sameNode (setNode_sameNextNode node n)
  have hslot (s : Slot) (v : Option NodeId) :
      SameNode (MonadLift.monadLift (slotSet s v) : WG.M Unit) :=
    liftAip_sameNode (slotSet_sameNextNode s v)
  have hf (node : NodeId) :
      SameNode (MonadLift.monadLift (freeNode node) : WG.M Unit) :=
    liftAip_sameNode (freeNode_sameNextNode node)
  have ha {α : Type} (a : AmbientM α) :
      SameNode (MonadLift.monadLift a : WG.M α) :=
    fun initial => hoare_liftAmbient a (fun g => nodeView g = initial)
  unfold Leanux.Proofs.WG.AllowedIps.removeNodeBody
  -- Share actual do-join continuations instead of copying their tails into
  -- every branch. Every generated term is checked by the kernel.
  frame_node_remove

end Leanux.Proofs.Framing
