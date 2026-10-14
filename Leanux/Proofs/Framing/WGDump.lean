import Leanux.Proofs.Framing.Control
import Leanux.Proofs.Framing.WGAllowedIps
import Leanux.Proofs.Framing.WGConfiguration
import Leanux.Proofs.WG.NetlinkDump.Source

/-! Canonical dump frames. Read-only serialization preserves the complete Kernel.
The socket mask hides only the two netlink socket records, retaining device
presence, every resident object and all allocator frontiers. Internal access
coverage is established separately at the source getters. -/
namespace Leanux.Proofs.Framing
open Leanux Leanux.WG Leanux.Proofs.WG.NetlinkDump Std.Do
set_option maxHeartbeats 1000000
set_option pp.structureInstances false

namespace DumpKernelComposition
open Lean Meta Elab Tactic

theorem dumpKernel_ite (p : Prop) [Decidable p] {a b : M α}
    (ha : p → SameKernel a) (hb : ¬p → SameKernel b) : SameKernel (if p then a else b) := by
  by_cases h : p <;> simp only [h, ↓reduceIte]
  · exact ha h
  · exact hb h

elab "dump_kernel_head " n:ident : tactic => do
  let t := (← getMainTarget).consumeMData
  unless t.isAppOf ``SameKernel do throwError "expected SameKernel"
  let a := t.getAppArgs.back! |>.consumeMData |>.headBeta
  let name ← Lean.Elab.realizeGlobalConstNoOverloadWithInfo n
  unless a.isAppOf name do throwError "different action head"

elab "dump_kernel_intro" : tactic => do
  unless (← getMainTarget).isForall do throwError "expected forall"
  evalTactic (← `(tactic| intro x))


theorem map_sameSnapshot (f : α → β) {a : M α} (ha : SameKernel a) :
    SameKernel (f <$> a) := by
  simpa only [map_eq_pure_bind] using sameKernel_bind ha (fun x => sameKernel_pure (f x))

theorem discard_sameSnapshot {a : M α} (ha : SameKernel a) : SameKernel (discard a) := by
  unfold Functor.discard
  exact map_sameSnapshot _ ha

theorem forIn_sameSnapshot (xs : List α) (b : β) (f : α → β → M (ForInStep β))
    (hf : ∀ a b, SameKernel (f a b)) : SameKernel (forIn xs b f) := by
  induction xs generalizing b with
  | nil => simpa only [List.forIn_nil] using sameKernel_pure b
  | cons a xs ih =>
    rw [List.forIn_cons]
    apply sameKernel_bind (hf a b)
    intro step
    cases step with
    | done b => exact sameKernel_pure b
    | yield b => exact ih b

theorem andM_sameSnapshot (a b : M Bool) (ha : SameKernel a) (hb : SameKernel b) :
    SameKernel (Leanux.WG.andM a b) := by
  unfold Leanux.WG.andM
  apply sameKernel_bind ha
  intro result
  cases result
  · exact sameKernel_pure false
  · exact hb

theorem orM_sameSnapshot (a b : M Bool) (ha : SameKernel a) (hb : SameKernel b) :
    SameKernel (Leanux.WG.orM a b) := by
  unfold Leanux.WG.orM
  apply sameKernel_bind ha
  intro result
  cases result
  · exact hb
  · exact sameKernel_pure true

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
  unless t.isAppOf ``SameKernel do throwError "not SameKernel"
  let .app f a := t | throwError "missing action"
  let a' := kernelHeadBZ 64 a
  if Expr.equal a a' then throwError "head unchanged"
  replaceMainGoal [← g.replaceTargetDefEq (.app f a')]

elab "dump_dump_kernel_head_match" : tactic => withMainContext do
  let g ← getMainGoal
  let t := (← instantiateMVars (← g.getType)).consumeMData
  unless t.isAppOf ``SameKernel do throwError "not SameKernel"
  let a := t.getAppArgs.back! |>.consumeMData
  let some _ ← Lean.Meta.matchMatcherApp? a | throwError "not a top matcher"
  replaceMainGoal (← Lean.Meta.Split.splitMatch g a)

elab "dump_kernel_join_let" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``SameKernel do throwError "not SameKernel"
  let action := target.getAppArgs.back! |>.consumeMData
  let .letE name ty value body _ := action | throwError "not a let"
  unless name.toString.startsWith "__do_jp" do throwError "not a join continuation"
  let property ← forallTelescope ty fun args _ => do
    let result ← mkAppM ``SameKernel #[mkAppN value args]
    mkForallFVars args result
  let valueProof ← mkFreshExprSyntheticOpaqueMVar property
  let (continuation, next) ← withLocalDeclD name ty fun f => do
    let contract ← forallTelescope ty fun args _ => do
      let result ← mkAppM ``SameKernel #[mkAppN f args]
      mkForallFVars args result
    withLocalDeclD `dump_kernel_join contract fun hf => do
      let bodyProp ← mkAppM ``SameKernel #[body.instantiate1 f]
      let next ← mkFreshExprSyntheticOpaqueMVar bodyProp
      let proof ← mkLambdaFVars #[f, hf] next
      pure (proof, next.mvarId!)
  goal.assign (mkApp2 continuation value valueProof)
  replaceMainGoal [valueProof.mvarId!, next]

elab "dump_kernel_join_use" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``SameKernel do throwError "not SameKernel"
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
    | with_reducible assumption
    | dump_kernel_join_let
    | dump_kernel_join_use
    | (dump_kernel_head Pure.pure; exact sameKernel_pure _)
    | (dump_kernel_head Bind.bind; refine sameKernel_bind ?_ ?_)
    | (dump_kernel_head ite; refine dumpKernel_ite _ ?_ ?_)
    | (dump_kernel_head Leanux.WG.andM; refine andM_sameSnapshot _ _ ?_ ?_)
    | (dump_kernel_head Leanux.WG.orM; refine orM_sameSnapshot _ _ ?_ ?_)
    | (dump_kernel_head Functor.discard; refine discard_sameSnapshot ?_)
    | (dump_kernel_head Functor.map; refine map_sameSnapshot _ ?_)
    | (dump_kernel_head ForIn.forIn; with_reducible refine forIn_sameSnapshot _ _ _ ?_)
    | dump_dump_kernel_head_reduce
    | dump_dump_kernel_head_match)

end DumpKernelComposition
open DumpKernelComposition

def dumpKernel (k : Kernel) : Kernel := {k with nlSock7 := {}, nlSock8 := {}}
def dumpView (w : World) : Kernel := dumpKernel w.k
abbrev SameDumpKernel (a : M α) := SameView dumpView a

theorem getNlSock_sameKernel (fd : Nat) : SameKernel (getNlSock fd) := by
  apply sameKernel_of_wp
  intro k
  mvcgen [getNlSock, getK]

theorem setNlSock_sameDumpKernel (fd : Nat) (sock : NlSock) :
    SameDumpKernel (setNlSock fd sock) := by
  by_cases hf : fd == 8
  all_goals simp only [setNlSock, hf, ↓reduceIte]
  all_goals intro w x v hr; cases hr; rfl

theorem getAllowedips_sameKernel (skb : NlSkb) (family masked cidr : Nat) :
    SameKernel (getAllowedips skb family masked cidr) := by
  apply sameKernel_of_wp
  intro k
  mvcgen [getAllowedips, branch]

theorem readNode_sameKernel (n : AipNode) : SameKernel (readNode n) := by
  apply sameKernel_of_wp
  intro k
  mvcgen [readNode, swapEndian, branch]

theorem getPeerDumpAllowed_sameKernel (p : Peer) (ctx : DumpCtx) (skb0 skb : NlSkb)
    (pubkey : String) (attrs : List (String × Lean.Json)) (node : Option NodeId) :
    SameKernel (getPeerDumpAllowedSource p ctx skb0 skb pubkey attrs node) := by
  apply sameKernel_of_wp
  intro k
  have hn := fun id => sameKernel_wp _ (getNode_sameKernel id) (fun s => s = k)
  have hr := fun n => sameKernel_wp _ (readNode_sameKernel n) (fun s => s = k)
  have ha := fun skb fam addr cidr => sameKernel_wp _ (getAllowedips_sameKernel skb fam addr cidr) (fun s => s = k)
  have hl (α β : Type) := list_view_spec (fun w => w.k) (α := α) (β := β) (fun s => s = k)
  mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, hl,
    getPeerDumpAllowedSource, hn, hr, ha, getDev, getK, branch, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all

theorem getPeerDumpTail_sameKernel (p : Peer) (ctx : DumpCtx) (skb : NlSkb) :
    SameKernel (getPeerDumpTailSource p ctx skb) := by
  unfold getPeerDumpTailSource
  repeat' first
    | (dump_kernel_head getPeerDumpAllowedSource; with_reducible exact getPeerDumpAllowed_sameKernel _ _ _ _ _ _ _)
    | (dump_kernel_head Leanux.branch; with_reducible exact sameKernel_branch _ _)
    | dump_kernel_step

theorem getPeerDump_sameKernel (pid : PeerId) (ctx : DumpCtx) (skb : NlSkb) :
    SameKernel (getPeerDump pid ctx skb) := by
  rw [getPeerDump_source]
  apply sameKernel_of_wp
  intro k
  have ht := fun p => sameKernel_wp _ (getPeerDumpTail_sameKernel p ctx skb) (fun s => s = k)
  mvcgen [getPeer, getDev, getK, invariant, ht]

theorem coalesce_sameKernel (messages : List NlMessage) : SameKernel (coalesce messages) := by
  apply sameKernel_of_wp
  intro k
  have hl (α β : Type) := list_view_spec (fun w => w.k) (α := α) (β := β) (fun s => s = k)
  mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, hl, coalesce, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all

end Leanux.Proofs.Framing
