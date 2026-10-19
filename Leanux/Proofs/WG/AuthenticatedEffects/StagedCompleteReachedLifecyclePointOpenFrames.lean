import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedLifecyclePointOrdinary
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedLifecyclePointStrong

/-! The concrete open traversal retains C1 allocation state at each real
staging entry. The two scoped send children remain explicit only for their
native interiors, not for their normal frame or source entry premise. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Lifecycle.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal HandshakeSecurity Driver
set_option maxHeartbeats 600000
elab "lifecycle_strong_uncast" : tactic => Lean.Elab.Tactic.withMainContext do
  let target := (← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)).consumeMData
  unless target.isAppOf ``Strong do Lean.throwError "not a frame certificate"
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
    let frameType ← Lean.Meta.mkAppM ``Strong #[parts.back!]
    let frame ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar frameType
    let result ← Lean.Meta.mkAppM ``Strong.source_mpr #[equation,frame]
    Lean.Elab.Tactic.liftMetaTactic fun goal => do
      let more ← goal.apply result
      return frame.mvarId! :: more

theorem staging_strong (pid : PeerId) : Strong (.child (.family (.staging pid))) :=
  ⟨CompleteProduct.state (CompleteProduct.fixture _ _ (CompleteProduct.staging pid)),fun _ _ before=>before⟩

theorem keepalive_strong (pid : PeerId) : Strong (.child (.family (.keepalive pid))) :=
  ⟨CompleteProduct.state (CompleteProduct.fixture _ _ (CompleteProduct.keepalive pid)),fun _ _ before=>before⟩

theorem running_checked (running : Bool) :
    CompleteProduct.Checked (liftPrefix (liftWG (modifyDev fun d=>{d with running}))) := by
  apply CompleteProduct.wg
  apply CompleteProduct.pair
    (CompletePassive.native CompleteProduct.Safe CompleteProduct.account_safe _
      (ReceiveFrames.device (fun d=>{d with running}) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl)))
    (erasesStatePrefix_lift _)
  exact AllocatedFrames.observed (erasesStatePrefix_lift _) (allocationDeviceControl.running running)

elab "lifecycle_certificate_head " expected:ident : tactic => do
  let target := (← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)).consumeMData
  unless target.isAppOf ``Strong || target.isAppOf ``Ordinary do Lean.throwError "not a shape predicate"
  let some shape := target.getAppArgs.back? | Lean.throwError "missing shape"
  let .const actual _ := shape.consumeMData.getAppFn | Lean.throwError "not a named shape"
  let name := expected.getId.eraseMacroScopes.toString
  unless actual.toString == name || actual.toString.endsWith ("."++name) do Lean.throwError "different shape"

elab "lifecycle_and" : tactic => do
  let target := (← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)).consumeMData
  unless target.isAppOf ``And do Lean.throwError "not explicit conjunction"
  Lean.Elab.Tactic.evalTactic (← `(tactic| constructor))

elab "lifecycle_forall" : tactic => do
  let target := (← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)).consumeMData
  unless target.isForall do Lean.throwError "not explicit forall"
  Lean.Elab.Tactic.evalTactic (← `(tactic| intro))

macro "lifecycle_strong_step" : tactic => `(tactic| first
  | lifecycle_strong_uncast
  | (lifecycle_certificate_head Shape.child; first | exact staging_strong _ | exact keepalive_strong _)
  | (complete_product_wg getDev; exact CompleteProduct.wg _ (CompleteProduct.state_store _ getDev_sameWGStore))
  | (complete_product_wg getPeer; exact CompleteProduct.wg _ (CompleteProduct.state_store _ (CompleteProduct.peer_read_store _)))
  | (complete_product_wg branch; exact branch_checked _ _)
  | (complete_product_wg modifyDev; exact running_checked _)
  | (complete_product_wg socketInit; exact socket_checked _ (socketInit_sameSocket _))
  | (complete_product_head Family.action; exact (staging_strong _).1)
  | (complete_product_head FixtureEffects.runWith; exact (keepalive_strong _).1)
  | assumption
  | (dsimp +failIfUnchanged only [Strong,id])
  | exact True.intro
  | lifecycle_and
  | lifecycle_forall
  | split)

theorem Strong.source_cast {left right : PrefixM Event α} (same : left=right)
    {shape : Shape left} (before : Strong shape) : Strong (same ▸ shape) := by
  cases same
  exact before

theorem list_strong {body : ι → σ → PrefixM Event (ForInStep σ)}
    {shapes : ∀value acc,Shape (body value acc)} {initial : σ} (before : ∀value acc,Strong (shapes value acc)) :
    Strong (listShape items initial body shapes) := by
  induction items generalizing initial with
  | nil => trivial
  | cons item rest ih =>
    rw [listShape_cons]
    unfold consShape
    apply Strong.source_cast
    refine ⟨before item initial,?_⟩
    intro decision
    cases decision with
    | done final => trivial
    | yield next => exact ih

theorem opened_strong : Strong openedShape := by
  have staging (pid : PeerId) : CompleteProduct.Checked (Family.staging pid).action :=
    (staging_strong pid).1
  have keepalive (pid : PeerId) : CompleteProduct.Checked (Family.keepalive pid).action :=
    (keepalive_strong pid).1
  unfold openedShape
  repeat' first | (lifecycle_certificate_head listShape; apply list_strong) | lifecycle_strong_step
  case left.right.left.left => exact staging _
  case left.left => exact keepalive _

theorem up_strong : Strong upShape := by
  unfold upShape
  repeat' first | (lifecycle_certificate_head openedShape; exact opened_strong) | lifecycle_strong_step

theorem up_framed (before : CompleteProduct.Carrier h w) : Framed upShape w h :=
  up_strong.framed before

theorem opened_framed (before : CompleteProduct.Carrier h w) : Framed openedShape w h :=
  opened_strong.framed before

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Lifecycle.Points
