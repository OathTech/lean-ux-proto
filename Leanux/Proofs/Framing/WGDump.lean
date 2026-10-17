import Leanux.Proofs.Framing.WGAllowedIps
import Leanux.Proofs.Framing.WGKernel
import Leanux.Proofs.WG.NetlinkDump.Source

/-! Native dump frames and projection-parametric composition. The mutable
socket observation masks only the original two socket records. -/
namespace Leanux.Proofs.Framing
open Leanux Leanux.WG Leanux.Proofs.WG.NetlinkDump Std.Do
set_option maxHeartbeats 1000000
set_option pp.structureInstances false

namespace DumpComposition
variable {S σ α β : Type} {m : Type → Type} {ps : PostShape}
  [Monad m] [WPMonad m ps] {view : S → σ}

theorem ite_sameView (p : Prop) [Decidable p] {a b : StateT S m α}
    (ha : p → SameView view a) (hb : ¬p → SameView view b) :
    SameView view (if p then a else b) := by
  by_cases h : p <;> simp only [h, ↓reduceIte]
  · exact ha h
  · exact hb h

theorem map_sameView (f : α → β) {a : StateT S m α} (ha : SameView view a) :
    SameView view (f <$> a) := ha.map f

theorem discard_sameView {a : StateT S m α} (ha : SameView view a) :
    SameView view (discard a) := by
  unfold Functor.discard
  exact map_sameView _ ha

theorem forIn_sameView (xs : List α) (b : β)
    (f : α → β → StateT S m (ForInStep β))
    (hf : ∀ a b, SameView view (f a b)) : SameView view (forIn xs b f) := by
  induction xs generalizing b with
  | nil => simpa only [List.forIn_nil] using SameView.pure view b
  | cons a xs ih =>
    rw [List.forIn_cons]
    apply SameView.bind (hf a b)
    intro step
    cases step with
    | done b => exact SameView.pure view b
    | yield b => exact ih b

theorem andM_sameView (a b : StateT S m Bool)
    (ha : SameView view a) (hb : SameView view b) :
    SameView view (do if ← a then b else pure false) := by
  apply SameView.bind ha
  intro result
  cases result
  · exact SameView.pure view false
  · exact hb

theorem orM_sameView (a b : StateT S m Bool)
    (ha : SameView view a) (hb : SameView view b) :
    SameView view (do if ← a then pure true else b) := by
  apply SameView.bind ha
  intro result
  cases result
  · exact hb
  · exact SameView.pure view true

open Lean Meta Elab Tactic

elab "dump_kernel_head " n:ident : tactic => do
  let t := (← getMainTarget).consumeMData
  unless t.isAppOf ``SameView do throwError "expected SameView"
  let a := t.getAppArgs.back! |>.consumeMData |>.headBeta
  let name ← Lean.Elab.realizeGlobalConstNoOverloadWithInfo n
  unless a.isAppOf name do throwError "different action head"

elab "dump_kernel_intro" : tactic => do
  unless (← getMainTarget).isForall do throwError "expected forall"
  evalTactic (← `(tactic| intro x))


private def kernelHeadBZ : Nat → Expr → Expr
  | 0, e => e
  | n+1, e =>
    let e := e.consumeMData
    match e with
    | .letE _ _ v b _ => kernelHeadBZ n (b.instantiate1 v)
    | _ =>
      match e.getAppFn.consumeMData with
      | .letE _ _ v b _ => kernelHeadBZ n (mkAppN (b.instantiate1 v) e.getAppArgs)
      | .lam .. =>
        let e' := e.headBeta
        if Expr.equal e e' then e else kernelHeadBZ n e'
      | _ => e

elab "dump_dump_kernel_head_reduce" : tactic => withMainContext do
  let g ← getMainGoal
  let t := (← instantiateMVars (← g.getType)).consumeMData
  unless t.isAppOf ``SameView do throwError "not SameView"
  let .app f a := t | throwError "missing action"
  let a' := kernelHeadBZ 64 a
  if Expr.equal a a' then throwError "head unchanged"
  replaceMainGoal [← g.replaceTargetDefEq (.app f a')]

elab "dump_dump_kernel_head_match" : tactic => withMainContext do
  let g ← getMainGoal
  let t := (← instantiateMVars (← g.getType)).consumeMData
  unless t.isAppOf ``SameView do throwError "not SameView"
  let a := t.getAppArgs.back! |>.consumeMData
  let some _ ← Lean.Meta.matchMatcherApp? a | throwError "not a top matcher"
  replaceMainGoal (← Lean.Meta.Split.splitMatch g a)

elab "dump_kernel_join_let" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``SameView do throwError "not SameView"
  let action := target.getAppArgs.back! |>.consumeMData
  let .letE name ty value body _ := action | throwError "not a let"
  unless name.toString.startsWith "__do_jp" do throwError "not a join continuation"
  let property ← forallTelescope ty fun args _ => do
    let result ← mkAppM ``SameView #[target.getAppArgs[target.getAppArgs.size - 2]!, mkAppN value args]
    mkForallFVars args result
  let valueProof ← mkFreshExprSyntheticOpaqueMVar property
  let (continuation, next) ← withLocalDeclD name ty fun f => do
    let contract ← forallTelescope ty fun args _ => do
      let result ← mkAppM ``SameView #[target.getAppArgs[target.getAppArgs.size - 2]!, mkAppN f args]
      mkForallFVars args result
    withLocalDeclD `dump_kernel_join contract fun hf => do
      let bodyProp ← mkAppM ``SameView #[target.getAppArgs[target.getAppArgs.size - 2]!, body.instantiate1 f]
      let next ← mkFreshExprSyntheticOpaqueMVar bodyProp
      let proof ← mkLambdaFVars #[f, hf] next
      pure (proof, next.mvarId!)
  goal.assign (mkApp2 continuation value valueProof)
  replaceMainGoal [valueProof.mvarId!, next]

elab "dump_kernel_join_use" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``SameView do throwError "not SameView"
  let action := target.getAppArgs.back! |>.consumeMData |>.headBeta
  unless action.getAppFn.isFVar do throwError "not a local continuation"
  for decl in ← getLCtx do
    if decl.userName == `dump_kernel_join then
      let proof := mkAppN decl.toExpr action.getAppArgs
      try
        if ← withReducible (isDefEq (← inferType proof) target) then
          goal.assign proof
          replaceMainGoal []
          return
      catch _ => pure ()
  throwError "no continuation contract"

macro "dump_kernel_step" : tactic => `(tactic|
  first
    | contradiction
    | dump_kernel_intro
    | dump_kernel_join_let
    | dump_kernel_join_use
    | (dump_kernel_head Pure.pure; exact SameView.pure _ _)
    | (dump_kernel_head Bind.bind; refine SameView.bind ?_ ?_)
    | (dump_kernel_head ite; refine ite_sameView _ ?_ ?_)
    | (dump_kernel_head Leanux.WG.andM; with_reducible refine andM_sameView _ _ ?_ ?_)
    | (dump_kernel_head Leanux.WG.orM; with_reducible refine orM_sameView _ _ ?_ ?_)
    | (dump_kernel_head Functor.discard; refine discard_sameView ?_)
    | (dump_kernel_head Functor.map; refine map_sameView _ ?_)
    | (dump_kernel_head ForIn.forIn; with_reducible refine forIn_sameView _ _ _ ?_)
    | dump_dump_kernel_head_reduce
    | dump_dump_kernel_head_match)


end DumpComposition
open DumpComposition

def dumpStore (s : WGStoreView) : WGStoreView := {s with nlSock7 := {}, nlSock8 := {}}
def dumpView (g : WGWorld) : WGStoreView := dumpStore (wgStoreView g)
abbrev SameDump (a : WG.M α) := SameView dumpView a

theorem getNlSock_sameWGWorld (fd : Nat) :
    SameView (id : WGWorld → WGWorld) (getNlSock fd) := by
  apply (Leanux.Proofs.WG.Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g ambient x v ambient' run
  cases run
  rfl

theorem setNlSock_sameDump (fd : Nat) (sock : NlSock) :
    SameDump (setNlSock fd sock) := by
  intro initial
  apply hoare_modify
  intro g h
  by_cases hfd : (fd == 8) = true <;>
    simpa [dumpView, dumpStore, wgStoreView, hfd] using h

theorem getAllowedips_sameWGWorld (skb : NlSkb) (family masked cidr : Nat) :
    SameView (id : WGWorld → WGWorld) (getAllowedips skb family masked cidr) := by
  unfold getAllowedips
  repeat' first
    | (dump_kernel_head Leanux.branch;
        intro initial; exact hoare_liftAmbient (AmbientM.branch _ _) (fun g => g = initial))
    | dump_kernel_step

theorem readNode_sameWGWorld (n : AipNode) :
    SameView (id : WGWorld → WGWorld) (readNode n) := by
  unfold readNode swapEndian
  repeat' first
    | (dump_kernel_head Leanux.branch;
        intro initial; exact hoare_liftAmbient (AmbientM.branch _ _) (fun g => g = initial))
    | dump_kernel_step

theorem getPeerDumpAllowed_sameWGWorld (p : Peer) (ctx : DumpCtx) (skb0 skb : NlSkb)
    (pubkey : String) (attrs : List (String × Lean.Json)) (node : Option NodeId) :
    SameView (id : WGWorld → WGWorld) (getPeerDumpAllowedSource p ctx skb0 skb pubkey attrs node) := by
  have hn (n : NodeId) :
      SameView (id : WGWorld → WGWorld) (MonadLift.monadLift (getNode n) : WG.M AipNode) := by
    apply SameView.of_wp
    intro k
    apply hoare_liftAip_of (getNode n)
    intro g d hg hd
    dsimp only [id] at hg
    subst g
    apply hoare_consequence ((getNode_sameAipStore n).wp
      (fun s => s = { nodes := d.nodes, nextNode := d.nextNode, trie := d.peerAllowedips }))
    · intro s hs
      exact hs
    · intro _ s hs
      subst s
      cases k
      simp_all
  have hg : SameView (id : WGWorld → WGWorld) getDev := by
    apply (Leanux.Proofs.WG.Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mpr
    intro g ambient x v ambient' run
    cases hd : g.dev <;> simp [getDev, hd, invariant, AmbientM.invariant] at run
    · cases run
    · cases run
      rfl
  unfold getPeerDumpAllowedSource
  repeat' first
    | (dump_kernel_head liftM; unfold liftM)
    | (dump_kernel_head MonadLift.monadLift; exact hn _)
    | (dump_kernel_head MonadLiftT.monadLift; exact hn _)
    | (dump_kernel_head getDev; exact hg)
    | (dump_kernel_head readNode; with_reducible exact readNode_sameWGWorld _)
    | (dump_kernel_head getAllowedips; with_reducible exact getAllowedips_sameWGWorld _ _ _ _)
    | (dump_kernel_head Leanux.branch;
        intro initial; exact hoare_liftAmbient (AmbientM.branch _ _) (fun s => s = initial))
    | (dump_kernel_head Leanux.invariant;
        intro initial; exact hoare_liftAmbient (AmbientM.invariant _) (fun s => s = initial))
    | dump_kernel_step

theorem getPeerDumpTail_sameWGWorld (p : Peer) (ctx : DumpCtx) (skb : NlSkb) :
    SameView (id : WGWorld → WGWorld) (getPeerDumpTailSource p ctx skb) := by
  unfold getPeerDumpTailSource
  repeat' first
    | (dump_kernel_head getPeerDumpAllowedSource; with_reducible exact getPeerDumpAllowed_sameWGWorld _ _ _ _ _ _ _)
    | (dump_kernel_head Leanux.branch;
        intro initial; exact hoare_liftAmbient (AmbientM.branch _ _) (fun s => s = initial))
    | dump_kernel_step

theorem getPeerDump_sameWGWorld (pid : PeerId) (ctx : DumpCtx) (skb : NlSkb) :
    SameView (id : WGWorld → WGWorld) (getPeerDump pid ctx skb) := by
  have peer : SameView (id : WGWorld → WGWorld) (getPeer pid) := by
    apply (Leanux.Proofs.WG.Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mpr
    intro g ambient x v ambient' run
    cases hd : g.dev <;> simp [getPeer, getDev, hd, invariant, AmbientM.invariant] at run
    · cases run
    · split at run
      · cases run
        rfl
      · cases run
  rw [getPeerDump_source]
  exact SameView.bind peer (fun p => getPeerDumpTail_sameWGWorld p ctx skb)

theorem coalesce_sameWGWorld (messages : List NlMessage) :
    SameView (id : WGWorld → WGWorld) (coalesce messages) := by
  unfold coalesce
  repeat' first
    | (dump_kernel_head Leanux.invariant;
        intro initial; exact hoare_liftAmbient (AmbientM.invariant _) (fun g => g = initial))
    | dump_kernel_step

end Leanux.Proofs.Framing
