import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPreparePointCanonicalFrames

/-! Complete caller framing for preparation, including its native match
branches. The eliminators transport the fixed indexed witness through the
original source equalities; their proofs are ordinary kernel-checked cases. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Prepare.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity CausalJournal RetirementSecurity
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

variable {w : WGWorld} {a : Ambient}

theorem option_function_framed {E α ι : Type}
    (domain : Option ι → Prop) (action : Option ι → WGPrefix E α) (query : Option ι)
    (absent : domain none → Shape (action none)) (present : ∀value,domain (some value) → Shape (action (some value)))
    (evidence : domain query) (h : List E) (w : WGWorld) (a : Ambient)
    (no : ∀proof,Framed (absent proof) w a h)
    (yes : ∀value proof,Framed (present value proof) w a h) :
    Framed (Option.rec (motive:=fun value=>domain value → Shape (action value)) absent present query evidence) w a h := by
  cases query
  · exact no evidence
  · exact yes _ evidence

elab "prepare_option_frame" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target ← Lean.instantiateMVars (← goal.getType)
  unless target.isAppOf ``Framed do Lean.throwError "not a preparation frame"
  let inputs := target.getAppArgs
  let shape := inputs[inputs.size-4]!.consumeMData.headBeta
  unless shape.isAppOf ``Option.rec do Lean.throwError "not an option source"
  let args := shape.getAppArgs
  unless args.size == 6 do Lean.throwError "not an applied option source"
  let (domain,action) ← Lean.Meta.lambdaTelescope args[1]! fun indices body => do
    Lean.Meta.forallTelescope body fun values result => do
      unless values.size == 1 && result.isAppOf ``Shape do Lean.throwError "different option motive"
      let domain ← Lean.Meta.mkLambdaFVars indices (← Lean.Meta.inferType values[0]!)
      let action ← Lean.Meta.mkLambdaFVars indices result.getAppArgs.back!
      pure (domain,action)
  let proof ← Lean.Meta.mkAppM ``option_function_framed #[domain,action,args[4]!,args[2]!,args[3]!,args[5]!,inputs.back!,inputs[inputs.size-3]!,inputs[inputs.size-2]!]
  Lean.Elab.Tactic.replaceMainGoal (← goal.apply proof)

theorem rec_function_framed {E α ι : Type} {source target : ι}
    (domain : (value : ι) → source=value → Prop)
    (action : (value : ι) → source=value → WGPrefix E α)
    (base : domain source rfl → Shape (action source rfl)) (eq : source=target)
    (witness : domain target eq) (h : List E) (w : WGWorld) (a : Ambient)
    (frames : ∀proof,Framed (base proof) w a h) :
    Framed ((Eq.rec (motive:=fun value proof=>domain value proof → Shape (action value proof)) base eq) witness) w a h := by
  cases eq
  exact frames witness

elab "prepare_rec_frame" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target ← Lean.instantiateMVars (← goal.getType)
  unless target.isAppOf ``Framed do Lean.throwError "not a preparation frame"
  let inputs := target.getAppArgs
  let shape := inputs[inputs.size-4]!
  let .app recursor witness := shape.consumeMData.headBeta | Lean.throwError "not an applied transport"
  unless recursor.isAppOf ``Eq.rec do Lean.throwError "not equality transport"
  let args := recursor.getAppArgs
  let (domain,action) ← Lean.Meta.lambdaTelescope args[2]! fun indices body => do
    Lean.Meta.forallTelescope body fun values result => do
      unless values.size == 1 && result.isAppOf ``Shape do Lean.throwError "different transport motive"
      let domain ← Lean.Meta.mkLambdaFVars indices (← Lean.Meta.inferType values[0]!)
      let action ← Lean.Meta.mkLambdaFVars indices result.getAppArgs.back!
      pure (domain,action)
  let proof ← Lean.Meta.mkAppM ``rec_function_framed #[domain,action,args[3]!,args[5]!,witness,inputs.back!,inputs[inputs.size-3]!,inputs[inputs.size-2]!]
  Lean.Elab.Tactic.replaceMainGoal (← goal.apply proof)

elab "prepare_framed_match" : tactic => do
  let target := (← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)).consumeMData
  unless target.isAppOf ``Framed do Lean.throwError "not a frame certificate"
  let args := target.getAppArgs
  let .const name _ := args[args.size-4]!.consumeMData.headBeta.getAppFn
    | Lean.throwError "not a named source matcher"
  unless (name.toString.splitOn ".match_").length > 1 do Lean.throwError "not a source matcher"
  Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $(Lean.mkIdent name)))

theorem option_fallback_framed {E α ι : Type}
    (guard domain : Option ι → Prop) (action : Option ι → WGPrefix E α) (query : Option ι)
    (absent : (guard none → domain none → Shape (action none)) → domain none → Shape (action none))
    (present : ∀value,(guard (some value) → domain (some value) → Shape (action (some value))) →
      domain (some value) → Shape (action (some value)))
    (fallback : guard query → domain query → Shape (action query)) (evidence : domain query)
    (h : List E) (w : WGWorld) (a : Ambient)
    (no : ∀fallback,(∀g proof,Framed (fallback g proof) w a h) → ∀proof,Framed (absent fallback proof) w a h)
    (yes : ∀value fallback,(∀g proof,Framed (fallback g proof) w a h) →
      ∀proof,Framed (present value fallback proof) w a h)
    (fallbackFrame : ∀g proof,Framed (fallback g proof) w a h) :
    Framed (Option.rec (motive:=fun value=>(guard value → domain value → Shape (action value)) →
      domain value → Shape (action value)) absent present query fallback evidence) w a h := by
  cases query
  · exact no fallback fallbackFrame evidence
  · exact yes _ fallback fallbackFrame evidence

elab "prepare_fallback_frame" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target ← Lean.instantiateMVars (← goal.getType)
  unless target.isAppOf ``Framed do Lean.throwError "not a preparation frame"
  let inputs := target.getAppArgs
  let shape := inputs[inputs.size-4]!.consumeMData.headBeta
  unless shape.isAppOf ``Option.rec do Lean.throwError "not an option source"
  let args := shape.getAppArgs
  unless args.size == 7 do Lean.throwError "not a fallback option source"
  let (guard,domain,action) ← Lean.Meta.lambdaTelescope args[1]! fun indices body => do
    Lean.Meta.forallTelescope body fun values result => do
      unless values.size == 2 && result.isAppOf ``Shape do Lean.throwError "different option motive"
      let guard ← Lean.Meta.forallTelescope (← Lean.Meta.inferType values[0]!) fun proofs _ => do
        unless proofs.size == 2 do Lean.throwError "different fallback motive"
        Lean.Meta.mkLambdaFVars indices (← Lean.Meta.inferType proofs[0]!)
      let domain ← Lean.Meta.mkLambdaFVars indices (← Lean.Meta.inferType values[1]!)
      let action ← Lean.Meta.mkLambdaFVars indices result.getAppArgs.back!
      pure (guard,domain,action)
  let proof ← Lean.Meta.mkAppM ``option_fallback_framed #[guard,domain,action,args[4]!,args[2]!,args[3]!,args[5]!,args[6]!,inputs.back!,inputs[inputs.size-3]!,inputs[inputs.size-2]!]
  Lean.Elab.Tactic.replaceMainGoal (← goal.apply proof)


/-- Every fixed preparation source point preserves the incoming transmit
ownership view. All setter requirements follow the original getters and the
cached publication peer; the caller supplies no frame premise. -/
theorem canonical_framed (h : List (MaterialOrigin.Event RxOrigin.Receipt)) :
    Framed canonical w a h := by
  unfold canonical
  repeat' first
    | exact decrypt_framed _ _
    | exact setRx_framed _ _ _
    | exact publication_framed _ _ _
    | prepare_framed_match
    | prepare_option_frame
    | prepare_fallback_frame
    | prepare_rec_frame
    | (solve | apply_assumption)
    | prepare_direct_frame_step

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Prepare.Points
