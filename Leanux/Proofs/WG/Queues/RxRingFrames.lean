import Leanux.Proofs.WG.Queues.RxRingJournal
import Leanux.Proofs.WG.Queues.EnqueueAdmission
import Leanux.Proofs.Framing.Index
import Leanux.Proofs.Framing.WGIndex

/-! Exact deviceIndex/decrypt-ring frames for the original non-ring helpers.
Peer/keypair deletion is permitted; it does not delete the device ring. -/
set_option maxHeartbeats 1000000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Queues.RxRing
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes Std.Do
open Leanux.Proofs.WG.Keypairs Leanux.Proofs.WG.Keypairs.WGFrames

def nativeCell (w : WGWorld) : Option (Nat × PtrRing SkbId) :=
  w.dev.map fun d => (d.ifindex, d.decryptQueue)

theorem kernel {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → WGWorld} {a : StateT S m α}
    (ha : SameView (fun w => wgStoreView (project w)) a) :
    SameView (fun w => nativeCell (project w)) a :=
  ha.of_factor (fun store : WGStoreView => store.dev.map (fun d => (d.ifindex, d.decryptQueue)))
    (fun w => nativeCell (project w)) (fun _ => rfl)

theorem modify (f : Device → Device) (he : ∀ d, (f d).ifindex = d.ifindex)
    (hq : ∀ d, (f d).decryptQueue = d.decryptQueue) : SameView nativeCell (modifyDev f) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' hr
  cases hr
  simp [nativeCell, Option.map_map, Function.comp_def, he, hq]

theorem getPeer_frame (pid : PeerId) : SameView nativeCell (getPeer pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient p v ambient' hr
  exact congrArg nativeCell (Leanux.Proofs.WG.Peers.getPeer_current pid w v p ambient ambient' hr).1

theorem getKeypair_frame (id : KeypairId) : SameView nativeCell (getKeypair id) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient k v ambient' hr
  exact congrArg nativeCell (Leanux.Proofs.WG.Keypairs.getKeypair_current id w v ambient ambient' k hr).1

theorem setPeer_frame (pid : PeerId) (p : Peer) : SameView nativeCell (setPeer pid p) :=
  modify _ (fun _ => rfl) (fun _ => rfl)

open Lean Meta Elab Tactic in
elab "ring_base_join" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``SameView do throwError "not a ring frame"
  let .app property action := target | throwError "missing action"
  let action := action.consumeMData
  if let .letE name ty value body _ := action then
    unless name.toString.startsWith "__do_jp" do throwError "not a join"
    let claim ← forallTelescope ty fun args _ =>
      mkForallFVars args (mkApp property (mkAppN value args))
    let proof ← mkFreshExprSyntheticOpaqueMVar claim
    let (continuation, next) ← withLocalDeclD name ty fun f => do
      let claim ← forallTelescope ty fun args _ =>
        mkForallFVars args (mkApp property (mkAppN f args))
      withLocalDeclD `ring_base_continuation claim fun hf => do
        let next ← mkFreshExprSyntheticOpaqueMVar (mkApp property (body.instantiate1 f))
        return (← mkLambdaFVars #[f, hf] next, next.mvarId!)
    goal.assign (mkApp2 continuation value proof)
    replaceMainGoal [proof.mvarId!, next]
  else
    let action := action.headBeta
    unless action.getAppFn.isFVar do throwError "not a local continuation"
    for decl in ← getLCtx do
      if decl.userName == `ring_base_continuation then
        let proof := mkAppN decl.toExpr action.getAppArgs
        if ← withReducible (isDefEq (← inferType proof) target) then
          goal.assign proof
          replaceMainGoal []
          return
    throwError "no matching continuation contract"

open Lean Meta Elab Tactic in
elab "ring_base_lift " n:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``SameView do throwError "not a ring frame"
  let action := target.getAppArgs.back! |>.consumeMData |>.headBeta
  unless action.isAppOf ``MonadLift.monadLift || action.isAppOf ``MonadLiftT.monadLift do
    throwError "not a component lift"
  let args := action.getAppArgs
  if args.isEmpty then throwError "missing component action"
  let sourceType ← instantiateMVars (← inferType args.back!)
  let typeArgs := sourceType.getAppArgs
  if typeArgs.isEmpty then throwError "missing component result type"
  let name ← realizeGlobalConstNoOverloadWithInfo n
  let expected ← mkAppM name #[typeArgs.back!]
  unless ← withReducible (isDefEq sourceType expected) do
    throwError "different component state"

/-- Source-head composition for the native device ring observation. -/
macro "ring_base_source" "[" fs:ident,* "]" : tactic => do
  let expand ← if fs.getElems.isEmpty then `(tactic| skip) else `(tactic| unfold $fs:ident*)
  `(tactic|
    (have ambient {α : Type} (a : AmbientM α) : SameView nativeCell (monadLift a : WG.M α) :=
       fun initial => hoare_liftAmbient a (fun w => nativeCell w = initial)
     have index {α : Type} (a : IndexM α) : SameView nativeCell (monadLift a : WG.M α) := by
       intro initial
       apply hoare_liftIndex
       intro g d table hg hd
       simpa [nativeCell, hd] using hg
     have read : SameView nativeCell (get : WG.M WGWorld) := by
       apply (ProjectedAction.iff_run_ambient _ _ _).mpr
       intro w a x v a' hr
       cases hr
       rfl
     have stopped {α : Type} (e : Stop) : SameView nativeCell (throw e : WG.M α) := by
       apply (ProjectedAction.iff_run_ambient _ _ _).mpr
       intro w a x v a' hr
       cases hr
     have edit (f : WGWorld → WGWorld) (hf : ∀ w, nativeCell (f w) = nativeCell w) :
         SameView nativeCell (_root_.modify f : WG.M Unit) := by
       intro initial
       apply hoare_modify
       intro w hw
       exact (hf w).trans hw
     have choice {α : Type} (p : Prop) [Decidable p] (yes no : WG.M α)
         (hy : p → SameView nativeCell yes) (hn : ¬p → SameView nativeCell no) :
         SameView nativeCell (if p then yes else no) := by
       by_cases h : p
       · simpa only [ite_eq_left h] using hy h
       · simpa only [ite_eq_right h] using hn h
     have loop {α β : Type} (xs : List α) (b : β) (f : α → β → WG.M (ForInStep β))
         (hf : ∀ x b, SameView nativeCell (f x b)) : SameView nativeCell (forIn xs b f) :=
       fun initial => list_view_spec nativeCell (fun s => s = initial) xs b f (fun x b => hf x b initial)
     $expand
     repeat' first
       | ring_base_join
       | contradiction
       | (snapshot_head getPeer; exact getPeer_frame _)
       | (snapshot_head getKeypair; exact getKeypair_frame _)
       | (snapshot_head setPeer; exact setPeer_frame _ _)
       | (snapshot_head setKeypair; unfold setKeypair)
       | (snapshot_head IndexOwner.peerDeref; exact fun initial => indexOwner_peerDeref_preserves _ (fun w => nativeCell w = initial))
       | (snapshot_head modifyDev; exact modify _ (fun _ => rfl) (fun _ => rfl))
       | (snapshot_head _root_.modify; exact edit _ (fun _ => rfl))
       | (snapshot_head get; exact read)
       | (snapshot_head MonadStateOf.get; exact read)
       | (snapshot_head MonadLiftT.monadLift; first | (ring_base_lift AmbientM; exact ambient _) | (ring_base_lift IndexM; exact index _))
       | (snapshot_head MonadLift.monadLift; first | (ring_base_lift AmbientM; exact ambient _) | (ring_base_lift IndexM; exact index _))
       | (snapshot_head throw; exact stopped _)
       | (snapshot_head MonadExceptOf.throw; exact stopped _)
       | (snapshot_head branchExpired; exact (branchExpired_sameWGWorld _ _ _ _).factor nativeCell)
       | (snapshot_head branch; unfold branch)
       | (snapshot_head branchCmp; unfold branchCmp)
       | (snapshot_head invariant; unfold invariant)
       | (snapshot_head unsupported; unfold unsupported)
       | (snapshot_head hiddenAlloc; unfold hiddenAlloc)
       | (snapshot_head refcountInc; unfold refcountInc)
       | (snapshot_head refcountIncNotZero; unfold refcountIncNotZero)
       | (snapshot_head refcountDecAndTest; unfold refcountDecAndTest)
       | (snapshot_head getDev; unfold getDev)
       | (snapshot_head requireNotPending; unfold requireNotPending)
       | (snapshot_head retirePeerUnits; unfold retirePeerUnits)
       | (snapshot_head modifyAmbient; unfold modifyAmbient)
       | (snapshot_head WG.orM; unfold WG.orM)
       | (snapshot_head liftM; unfold liftM)
       | (snapshot_head Pure.pure; exact SameView.pure _ _)
       | (snapshot_head Bind.bind; refine SameView.bind ?_ ?_)
       | (snapshot_head ForIn.forIn; apply loop)
       | (snapshot_head ite; apply choice)
       | keypairs_intro_forall
       | snapshot_head_reduce
       | snapshot_head_match))

theorem keypairGet_frame (id : Option KeypairId) : SameView nativeCell (keypairGet id) := by
  cases id <;> ring_base_source [keypairGet]

theorem keypairPut_frame (id : Option KeypairId) (now : Bool) : SameView nativeCell (keypairPut id now) := by
  cases id <;> ring_base_source [keypairPut]

theorem peerGet_frame (id : PeerId) : SameView nativeCell (peerGet id) := by
  ring_base_source [peerGet]

theorem peerGetMaybeZero_frame (id : Option PeerId) : SameView nativeCell (peerGetMaybeZero id) := by
  cases id <;> ring_base_source [peerGetMaybeZero]

theorem peerPut_frame (id : Option PeerId) : SameView nativeCell (peerPut id) := by
  cases id <;> ring_base_source [peerPut]

theorem indexLookup_frame (kinds : List IndexKind) (index : Nat) : SameView nativeCell (indexLookup kinds index) := by
  have peer (p : Option PeerId) : SameView nativeCell (peerGetMaybeZero p) := peerGetMaybeZero_frame p
  unfold indexLookup
  ring_base_source [IndexOwner.peerWord, IndexOwner.setPeerWord]
  all_goals exact peer _

theorem decryptPacket_frame (pkt : RxPacket) : SameView nativeCell (decryptPacket pkt) := by
  ring_base_source [decryptPacket]

end Leanux.Proofs.WG.Queues.RxRing
