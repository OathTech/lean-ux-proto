import Leanux.Proofs.WG.Queues.RingSource
import Leanux.Proofs.Framing.WGData
import Leanux.Proofs.WG.Queues.EnqueueAdmission
import Leanux.Proofs.Framing.Index
import Leanux.Proofs.Framing.WGIndex

/-! Exact deviceIndex/encrypt-ring frames for the original non-ring helpers.
Peer/keypair deletion is permitted; it does not delete the device ring. -/
set_option maxHeartbeats 1000000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Queues.TxRing
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes Std.Do

abbrev Event := Ring.Journal.Event (List SkbId)
abbrev Obs := PrefixM Event

def nativeCell (w : WGWorld) : Option (Nat × PtrRing (List SkbId)) :=
  w.dev.map fun d => (d.ifindex, d.encryptQueue)

def cell (w : World) : Option (Nat × PtrRing (List SkbId)) := nativeCell w.wg

abbrev Refines := Ring.Source.Refines (ι := List SkbId)
abbrev Safe := Ring.Source.Safe (ι := List SkbId)
abbrev Inv := Ring.Source.Inv cell
abbrev Initialized := Ring.Source.Initialized (ι := List SkbId)

theorem kernel {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → WGWorld} {a : StateT S m α}
    (ha : SameView (fun w => wgStoreView (project w)) a) :
    SameView (fun w => nativeCell (project w)) a :=
  ha.of_factor (fun store : WGStoreView => store.dev.map (fun d => (d.ifindex, d.encryptQueue)))
    (fun w => nativeCell (project w)) (fun _ => rfl)

theorem modify (f : Device → Device) (he : ∀ d, (f d).ifindex = d.ifindex)
    (hq : ∀ d, (f d).encryptQueue = d.encryptQueue) : SameView nativeCell (modifyDev f) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' hr
  cases hr
  simp [nativeCell, Option.map_map, Function.comp_def, he, hq]

theorem getPeer_frame (pid : PeerId) : SameView nativeCell (getPeer pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient p v ambient' hr
  exact congrArg nativeCell (Peers.getPeer_current pid w v p ambient ambient' hr).1

theorem getKeypair_frame (id : KeypairId) : SameView nativeCell (getKeypair id) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient k v ambient' hr
  exact congrArg nativeCell (Keypairs.getKeypair_current id w v ambient ambient' k hr).1

theorem setPeer_frame (pid : PeerId) (p : Peer) : SameView nativeCell (setPeer pid p) :=
  modify _ (fun _ => rfl) (fun _ => rfl)

open Lean Meta Elab Tactic in
elab "tx_ring_head " n:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← (← getMainGoal).getType)).consumeMData
  unless target.isAppOf ``Preserves do throwError "not a frame contract"
  let action := target.getAppArgs.back!.consumeMData.headBeta
  let expected ← realizeGlobalConstNoOverloadWithInfo n
  unless action.getAppFn.constName? == some expected do throwError "different action head"

open Lean Meta Elab Tactic in
elab "tx_ring_step" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  if target.isForall then
    evalTactic (← `(tactic| intro))
    return
  unless target.isAppOf ``Preserves do throwError "not a frame contract"
  let .app property action := target | throwError "missing action"
  let action := action.consumeMData
  if let .letE _ _ value body _ := action then
    replaceMainGoal [← goal.replaceTargetDefEq (mkApp property (body.instantiate1 value))]
    return
  let reduced := action.headBeta
  if !Expr.equal action reduced then
    replaceMainGoal [← goal.replaceTargetDefEq (mkApp property reduced)]
    return
  let head := action.getAppFn.constName?
  if head == some ``Bind.bind then
    evalTactic (← `(tactic| refine preserves_bind ?_ ?_))
  else if head == some ``Pure.pure then
    evalTactic (← `(tactic| exact preserves_pure _))
  else if head == some ``ite || head == some ``dite then
    evalTactic (← `(tactic| split))
  else if head == some ``liftM then
    evalTactic (← `(tactic| unfold liftM))
  else if (← Lean.Meta.matchMatcherApp? action).isSome then
    replaceMainGoal (← Lean.Meta.Split.splitMatch goal action)
  else
    throwError "unhandled frame action head {head}"

open Lean Meta Elab Tactic in
elab "tx_ring_lift_from " carrier:ident : tactic => withMainContext do
  let target := (← getMainTarget).consumeMData
  unless target.isAppOf ``Preserves do
    throwError "expected a frame contract"
  let action := target.getAppArgs.back! |>.consumeMData |>.headBeta
  unless action.isAppOf ``liftM || action.isAppOf ``MonadLift.monadLift ||
      action.isAppOf ``MonadLiftT.monadLift do
    throwError "expected a lifted action"
  let source := action.getAppArgs.back!
  let sourceType ← inferType source
  unless sourceType.isApp do throwError "expected an applied source monad"
  let name ← realizeGlobalConstNoOverloadWithInfo carrier
  let expected ← mkAppM name #[sourceType.getAppArgs.back!]
  unless ← withReducible (isDefEq sourceType expected) do
    throwError "different source monad"

theorem keypairPut_frame (id : Option KeypairId) (now : Bool) : SameView nativeCell (keypairPut id now) := by
  apply SameView.of_wp
  intro initial
  let P := fun w : WGWorld => nativeCell w = initial
  have ambient {α : Type} (a : AmbientM α) :
      Preserves P (monadLift a : WG.M α) := hoare_liftAmbient a P
  have index {α : Type} (a : IndexM α) :
      Preserves P (monadLift a : WG.M α) := by
    apply hoare_liftIndex a
    intro w d table hi hd
    simpa [P, nativeCell, hd] using hi
  have rc (old : Nat) : Preserves P (refcountDecAndTest old : WG.M Bool) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a x v a' hp hr
    simp [refcountDecAndTest, branch, branchCmp, AmbientM.branch,
      AmbientM.branchCmp, unsupported, AmbientM.unsupported] at hr
    repeat' split at hr
    all_goals simp_all
    all_goals rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
    all_goals exact hp
  change Preserves P (keypairPut id now)
  unfold keypairPut
  simp (config := { zeta := true }) only [branch, invariant]
  repeat' first
    | (tx_ring_head getKeypair; exact (getKeypair_frame _).wp (fun t => t = initial))
    | (tx_ring_head IndexOwner.peerDeref; exact indexOwner_peerDeref_preserves _ P)
    | (tx_ring_head setKeypair; unfold setKeypair)
    | (tx_ring_head modifyDev; apply hoare_modify; intro w h
       simpa [P, nativeCell, Option.map_map, Function.comp_def] using h)
    | (tx_ring_head refcountDecAndTest; exact rc _)
    | (tx_ring_lift_from IndexM; exact index _)
    | (tx_ring_lift_from AmbientM; exact ambient _)
    | (tx_ring_head _root_.modify; apply hoare_modify; intro w h; exact h)
    | tx_ring_step

theorem peerGet_frame (id : PeerId) : SameView nativeCell (peerGet id) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' hr
  cases hd : w.dev with
  | none =>
    simp [peerGet, requireNotPending, getPeer, getDev, hd,
      invariant, AmbientM.invariant] at hr
    cases hr
  | some d =>
    cases hp : d.peers[id]? with
    | none =>
      simp [peerGet, requireNotPending, getPeer, getDev, hd, hp,
        invariant, AmbientM.invariant] at hr
      cases hr
    | some peer =>
      simp [peerGet, requireNotPending, getPeer, getDev, setPeer, modifyDev,
        hd, hp, refcountInc, branch, branchCmp, AmbientM.branch, AmbientM.branchCmp,
        unsupported, AmbientM.unsupported] at hr
      split at hr <;> simp_all
      all_goals try split at hr <;> simp_all
      all_goals rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
      all_goals simp [nativeCell, hd]

theorem peerPut_frame (id : Option PeerId) : SameView nativeCell (peerPut id) := by
  apply SameView.of_wp
  intro initial
  let P := fun w : WGWorld => nativeCell w = initial
  have ambient {α : Type} (a : AmbientM α) :
      Preserves P (monadLift a : WG.M α) := hoare_liftAmbient a P
  have index {α : Type} (a : IndexM α) :
      Preserves P (monadLift a : WG.M α) := by
    apply hoare_liftIndex a
    intro w d table hi hd
    simpa [P, nativeCell, hd] using hi
  have rc (old : Nat) : Preserves P (refcountDecAndTest old : WG.M Bool) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a x v a' hp hr
    simp [refcountDecAndTest, branch, branchCmp, AmbientM.branch,
      AmbientM.branchCmp, unsupported, AmbientM.unsupported] at hr
    repeat' split at hr
    all_goals simp_all
    all_goals rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
    all_goals exact hp
  change Preserves P (peerPut id)
  unfold peerPut
  simp (config := { zeta := true }) only [branch, invariant, requireNotPending,
    retirePeerUnits, modifyAmbient]
  repeat' first
    | (tx_ring_head getPeer; exact (getPeer_frame _).wp (fun t => t = initial))
    | (tx_ring_head setPeer; exact (setPeer_frame _ _).wp (fun t => t = initial))
    | (tx_ring_head modifyDev; apply hoare_modify; intro w h
       simpa [P, nativeCell, Option.map_map, Function.comp_def] using h)
    | (tx_ring_head refcountDecAndTest; exact rc _)
    | (tx_ring_lift_from IndexM; exact index _)
    | (tx_ring_lift_from AmbientM; exact ambient _)
    | (tx_ring_head _root_.modify; apply hoare_modify; intro w h; exact h)
    | tx_ring_step

theorem cpu_frame (pid : PeerId) : SameView nativeCell (cpumaskChooseOnline pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' hr
  cases hd : w.dev with
  | none =>
    simp [cpumaskChooseOnline, getPeer, getDev, hd, invariant, AmbientM.invariant] at hr
    cases hr
  | some d =>
    cases hp : d.peers[pid]? with
    | none =>
      simp [cpumaskChooseOnline, getPeer, getDev, hd, hp, invariant, AmbientM.invariant] at hr
      cases hr
    | some p =>
      simp [cpumaskChooseOnline, getPeer, getDev, setPeer, modifyDev, hd, hp,
        branch, AmbientM.branch, Nat.mod_one] at hr
      repeat' split at hr
      all_goals simp_all
      all_goals rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
      all_goals simp [nativeCell, hd]

theorem enqueuePeer_frame (item : List SkbId) (state : PacketState) :
    SameView nativeCell (enqueuePerPeerTx item state) := by
  apply SameView.of_wp
  intro s
  let P := fun w : WGWorld => nativeCell w = s
  have ambient {α : Type} (a : AmbientM α) :
      Preserves P (monadLift a : WG.M α) := hoare_liftAmbient a P
  have packet {α : Type} (a : SkbM α) : Preserves P (liftSkb a) := by
    apply hoare_liftSkb a
    intro w d store hi hd
    simpa [P, nativeCell, hd] using hi
  have device : Preserves P getDev := (kernel (project := id) getDev_sameWGStore).wp (fun t => t = s)
  unfold enqueuePerPeerTx
  cases item.head? with
  | none => exact ambient (AmbientM.invariant "an empty ring item")
  | some first =>
    apply preserves_bind (packet (SkbStore.getTx first))
    intro tx
    apply preserves_bind (indexOwner_peerDeref_preserves (.keypair tx.keypair) P)
    intro pid
    apply preserves_bind ((peerGet_frame pid).wp (fun t => t = s))
    intro _
    apply preserves_bind ((getPeer_frame pid).wp (fun t => t = s))
    intro p
    dsimp only
    split
    · apply preserves_bind (ambient (AmbientM.invariant
        "an item for the tx worker that is not on its peer's tx_queue"))
      intro _
      apply preserves_bind (packet (SkbStore.setTx first fun p => {p with state}))
      intro _
      apply preserves_bind ((cpu_frame pid).wp (fun t => t = s))
      intro cpu
      apply preserves_bind device
      intro d
      apply preserves_bind (ambient (AmbientM.peekQueuedUnit .txWorker pid))
      intro queued
      split
      · apply preserves_bind (ambient (AmbientM.recordQueued .txWorker pid))
        intro _
        apply preserves_bind ((modify (fun d => {d with txWorkQueue := d.txWorkQueue ++ [pid]})
          (fun _ => rfl) (fun _ => rfl)).wp (fun t => t = s))
        intro _
        exact (peerPut_frame (some pid)).wp (fun t => t = s)
      · exact (peerPut_frame (some pid)).wp (fun t => t = s)
    · apply preserves_bind (packet (SkbStore.setTx first fun p => {p with state}))
      intro _
      apply preserves_bind ((cpu_frame pid).wp (fun t => t = s))
      intro cpu
      apply preserves_bind device
      intro d
      apply preserves_bind (ambient (AmbientM.peekQueuedUnit .txWorker pid))
      intro queued
      split
      · apply preserves_bind (ambient (AmbientM.recordQueued .txWorker pid))
        intro _
        apply preserves_bind ((modify (fun d => {d with txWorkQueue := d.txWorkQueue ++ [pid]})
          (fun _ => rfl) (fun _ => rfl)).wp (fun t => t = s))
        intro _
        exact (peerPut_frame (some pid)).wp (fun t => t = s)
      · exact (peerPut_frame (some pid)).wp (fun t => t = s)

end Leanux.Proofs.WG.Queues.TxRing
