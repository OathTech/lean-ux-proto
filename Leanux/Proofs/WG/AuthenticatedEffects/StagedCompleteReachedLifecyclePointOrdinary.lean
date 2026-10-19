import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedLifecyclePointCanonical
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedLifecyclePointLoops

/-! Concrete ordinary lifecycle fragments need only the actual packet
account. Creation and checked destruction have separate phase proofs. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Lifecycle.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal HandshakeSecurity Driver
set_option maxHeartbeats 600000
elab "lifecycle_ordinary_uncast" : tactic => Lean.Elab.Tactic.withMainContext do
  let target := (← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)).consumeMData
  unless target.isAppOf ``Ordinary do Lean.throwError "not a frame certificate"
  let args := target.getAppArgs
  if args.size < 1 then Lean.throwError "missing frame shape"
  let raw := args.back!.consumeMData
  let shape := if raw.isAppOf ``id then raw.getAppArgs.back! else raw
  unless shape.isAppOf ``Eq.mpr do Lean.throwError "not a source cast"
  let parts := shape.getAppArgs
  if parts.size < 2 then Lean.throwError "missing cast proof"
  let rec expand (fuel : Nat) (proof : Lean.Expr) : Lean.MetaM Lean.Expr := do
    if proof.isAppOf ``congrArg then return proof
    match fuel with
    | 0 => return proof
    | n+1 =>
      match proof.getAppFn with
      | .const name levels =>
        let info ← Lean.getConstInfo name
        match info.value? true with
        | some value =>
          let unfolded := Lean.mkAppN (value.instantiateLevelParams info.levelParams levels) proof.getAppArgs
          expand n unfolded.consumeMData.headBeta
        | none => return proof
      | _ => return proof
  let proof ← expand 8 parts[parts.size-2]!.consumeMData
  unless proof.isAppOf ``congrArg do Lean.throwError m!"not a canonical source congruence: {proof.getAppFn} ({proof.getAppArgs.size} args), {proof}"
  let proofArgs := proof.getAppArgs
  if proofArgs.size < 4 then Lean.throwError "incomplete source congruence"
  let same := proofArgs.back!
  let function := proofArgs[proofArgs.size-2]!
  let functionType ← Lean.Meta.whnf (← Lean.Meta.inferType function)
  let .forallE _ domain _ _ := functionType | Lean.throwError "not a unary source congruence"
  Lean.Meta.withLocalDeclD `source domain fun source => do
    let shaped := (Lean.mkApp function source).headBeta.consumeMData
    unless shaped.isAppOf ``Shape do Lean.throwError "source congruence does not produce Shape"
    let some action := shaped.getAppArgs.back? | Lean.throwError "missing congruent source"
    let lifted ← Lean.Meta.mkLambdaFVars #[source] action
    let equation ← Lean.Meta.mkAppM ``congrArg #[lifted,same]
    let frameType ← Lean.Meta.mkAppM ``Ordinary #[parts.back!]
    let frame ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar frameType
    let result ← Lean.Meta.mkAppM ``Ordinary.source_mpr #[equation,frame]
    Lean.Elab.Tactic.liftMetaTactic fun goal => do
      let more ← goal.apply result
      return frame.mvarId! :: more

macro "lifecycle_ordinary_steps" : tactic => `(tactic| first
  | lifecycle_ordinary_uncast
  | assumption
  | exact True.intro
  | constructor
  | (intro)
  | (dsimp +failIfUnchanged only [Ordinary,id])
  | split)

theorem Ordinary.source_cast {left right : PrefixM Event α} (same : left=right)
    {shape : Shape left} (before : Ordinary shape) : Ordinary (same ▸ shape) := by
  cases same
  exact before

theorem list_ordinary {body : ι → σ → PrefixM Event (ForInStep σ)}
    {shapes : ∀value acc,Shape (body value acc)} {initial : σ} (before : ∀value acc,Ordinary (shapes value acc)) :
    Ordinary (listShape items initial body shapes) := by
  induction items generalizing initial with
  | nil => trivial
  | cons item rest ih =>
    rw [listShape_cons]
    unfold consShape
    apply Ordinary.source_cast
    refine ⟨before item initial,?_⟩
    intro decision
    cases decision with
    | done final => trivial
    | yield next => exact ih

theorem timers_ordinary (pid : PeerId) : Ordinary (timersShape pid) := by
  unfold timersShape
  repeat' first | apply list_ordinary | lifecycle_ordinary_steps

theorem after_dead_ordinary (pid : PeerId) : Ordinary (afterDeadShape pid) := by
  unfold afterDeadShape
  repeat' first | exact timers_ordinary _ | lifecycle_ordinary_steps

theorem remove_all_ordinary : Ordinary removeAllShape := by
  unfold removeAllShape
  repeat' first | exact after_dead_ordinary _ | apply list_ordinary | lifecycle_ordinary_steps

theorem down_ordinary : Ordinary downShape := by
  unfold downShape
  repeat' first | exact timers_ordinary _ | apply list_ordinary | lifecycle_ordinary_steps

theorem prepare_ordinary : Ordinary prepareShape := by
  unfold prepareShape
  repeat' first | exact remove_all_ordinary | lifecycle_ordinary_steps

theorem down_framed (before : Account h w) : Framed downShape w h := down_ordinary.framed before

theorem prepare_framed (before : Account h w) : Framed prepareShape w h := prepare_ordinary.framed before

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Lifecycle.Points
