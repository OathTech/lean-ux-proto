import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedDispatchPointFramed

/-! Source-specific frame discharge. All nondeletion families are available
from the actual packet account; deletion keeps its stronger original input. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Dispatch.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues Configuration TransmitSecurity CausalJournal
set_option maxHeartbeats 800000

elab "dispatch_plain_uncast" : tactic => Lean.Elab.Tactic.withMainContext do
  let target := (← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)).consumeMData
  unless target.isAppOf ``Plain do Lean.throwError "not a frame certificate"
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
    let frameType ← Lean.Meta.mkAppM ``Plain #[parts.back!]
    let frame ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar frameType
    let result ← Lean.Meta.mkAppM ``Plain.source_mpr #[equation,frame]
    Lean.Elab.Tactic.liftMetaTactic fun goal => do
      let more ← goal.apply result
      return frame.mvarId! :: more

macro "dispatch_plain_steps" : tactic => `(tactic| repeat' first
  | dispatch_plain_uncast
  | assumption
  | exact True.intro
  | constructor
  | (intro)
  | (dsimp +failIfUnchanged only [Plain])
  | split)

theorem socket_plain (plain : Plain body) : Plain (socketShape fd body) := by
  unfold socketShape
  dispatch_plain_steps

theorem netlink_plain (plain : Plain body) : Plain (netlinkShape body) := by
  unfold netlinkShape
  repeat' first
    | apply socket_plain
    | assumption
    | exact True.intro
    | constructor
    | (intro)
    | (dsimp +failIfUnchanged only [Plain])

theorem dump_device_plain (ref : DeviceRef) : Plain (dumpDeviceShape ref) := by
  unfold dumpDeviceShape
  apply netlink_plain
  refine ⟨True.intro,?_⟩
  intro result
  cases result <;> dispatch_plain_steps

theorem dump_start_plain (ref : DeviceRef) : Plain (dumpStartShape ref) := by
  unfold dumpStartShape
  apply socket_plain
  dispatch_plain_steps

theorem dump_receive_plain : Plain dumpReceiveShape := by
  unfold dumpReceiveShape
  apply socket_plain
  refine ⟨True.intro,?_⟩
  intro _
  refine ⟨True.intro,?_⟩
  intro messages
  cases messages <;> dispatch_plain_steps

theorem observe_plain : Plain observeShape := by
  unfold observeShape
  repeat' first
    | apply socket_plain
    | exact True.intro
    | constructor
    | (intro)
    | (dsimp +failIfUnchanged only [Plain])
    | split

theorem canonical_plain (call : Syscall) (different : call≠.wgDelete) : Plain (canonical call) := by
  unfold canonical
  cases call
  case wgDelete => exact False.elim (different rfl)
  case seccompProbe nr args target strict => cases target <;> exact True.intro
  all_goals repeat' first
    | exact dump_device_plain _
    | exact dump_start_plain _
    | exact dump_receive_plain
    | exact observe_plain
    | apply socket_plain
    | apply netlink_plain
    | dispatch_plain_uncast
    | exact True.intro
    | (dsimp +failIfUnchanged only [Plain])
    | split

theorem canonical_framed (call : Syscall)
    (before : Runner.Points.Child.Entry (.dispatch call) h w) : Framed (canonical call) w h := by
  by_cases deletion : call=.wgDelete
  · subst call
    exact before
  · exact (canonical_plain call deletion).framed before.1.1

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Dispatch.Points
