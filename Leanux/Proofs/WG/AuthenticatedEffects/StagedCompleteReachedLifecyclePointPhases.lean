import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedLifecyclePointOrdinary
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedLifecyclePointEnvironmentFrames

/-! Creation and the exact destructor guard derive their fixed canonical
phase certificate. Old terminals persist through reset; no pending ticket is
settled by erasure. Stops receive no synthetic returned state. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Lifecycle.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal HandshakeSecurity
set_option maxHeartbeats 600000
elab "lifecycle_framed_uncast" : tactic => Lean.Elab.Tactic.withMainContext do
  let target := (← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)).consumeMData
  unless target.isAppOf ``Framed do Lean.throwError "not a frame certificate"
  let args := target.getAppArgs
  if args.size < 1 then Lean.throwError "missing frame shape"
  if args.size < 3 then Lean.throwError "missing frame entry"
  let raw := args[args.size-3]!.consumeMData
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
    let frameType ← Lean.Meta.mkAppM ``Framed #[parts.back!,args[args.size-2]!,args.back!]
    let frame ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar frameType
    let result ← Lean.Meta.mkAppM ``Framed.source_mpr #[equation,frame]
    Lean.Elab.Tactic.liftMetaTactic fun goal => do
      let more ← goal.apply result
      return frame.mvarId! :: more

theorem create_framed (before : Account h w) : Framed createShape w h := by
  change Framed ((congrArg Shape create_factor).mpr createBodyShape) w h
  apply Framed.source_mpr create_factor
  unfold createBodyShape
  refine ⟨before,?_⟩
  intro saved u middle read
  cases read
  dsimp only
  split
  · repeat' lifecycle_framed_uncast
    exact before
  · repeat' lifecycle_framed_uncast
    have absent : w.wg.dev=none := by
      cases device : w.wg.dev <;> simp_all
    obtain ⟨ledger,account⟩ := before
    refine ⟨⟨ledger,account,absent⟩,?_⟩
    intro ignored v last setup
    cases setup
    refine ⟨⟨ledger,w.wg,account,absent,rfl⟩,?_⟩
    intro ret target after native
    have history := native_history (liftWG wgNewlink) native
    have ready : Creating h ledger w.wg (setupWorld w.wg) := ⟨account,absent,rfl⟩
    have out := ready.newlink (HolderPoll.native_receipt (congrArg Prod.fst native))
    subst after
    dsimp only
    split
    · repeat' lifecycle_framed_uncast
      refine ⟨⟨ledger,out.1,out.2⟩,?_⟩
      intro ignored v last erased
      exact Native.normal .erase ⟨ledger,out.1,out.2⟩ erased
    · repeat' lifecycle_framed_uncast
      exact ⟨⟨ledger,out.1⟩,fun _ _ _ pureRun=>by cases pureRun; exact ⟨ledger,out.1⟩⟩

theorem tail_framed (before : CompleteRetired.GuardEntry h ledger holders w.wg) :
    Framed tailShape w h := by
  unfold tailShape
  repeat' first | lifecycle_framed_uncast | (dsimp +failIfUnchanged only [Framed,id])
  refine ⟨⟨ledger,holders,before⟩,?_⟩
  intro ignored v last checked
  have history := native_history (liftWG TxWork.Destruct.check) checked
  subst last
  cases ignored
  have facts := guard_no_pending before (HolderPoll.native_receipt (congrArg Prod.fst checked))
  have account : CompleteCarrier.Accounted h ledger [] [] v.wg := by rw [facts.1]; exact before.accounted
  refine ⟨⟨ledger,account⟩,?_⟩
  intro ignored u middle settled
  have account' := native_account _ (wg_frame _ RetiredFrames.settle) account settled
  refine ⟨⟨ledger,account',facts.2⟩,?_⟩
  intro ignored target after erased
  exact Native.normal .erase ⟨ledger,account',facts.2⟩ erased

/-- Original destructor entry facts, propagated through its actual complete
prepare run, derive the SAME-holder guard input at each reached tail. -/
theorem destruct_framed (before : RetiredPeer.Lifecycle.Packet.Entry h w.wg w.ambient) :
    Framed destructShape w h := by
  unfold destructShape
  repeat' first | lifecycle_framed_uncast | (dsimp +failIfUnchanged only [Framed,id])
  refine ⟨prepare_framed before.1,?_⟩
  intro value u middle run
  obtain ⟨_,_,_,prepared⟩ := RetiredPeer.Lifecycle.Packet.prepare_ready.liftWGObserver w h before
  rw [run] at prepared
  obtain ⟨ledger,holders,guard⟩ := prepared
  repeat' lifecycle_framed_uncast
  exact tail_framed guard

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Lifecycle.Points
