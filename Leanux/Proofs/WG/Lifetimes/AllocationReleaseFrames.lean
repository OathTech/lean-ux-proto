import Leanux.Proofs.WG.Lifetimes.AllocationRetention
import Leanux.Proofs.WG.Keypairs.Ordinary
import Lean

set_option maxHeartbeats 1000000
set_option pp.structureInstances false

/-! Original-call frames for allocation metadata, and reuse of the already
proved keypair ordinary transition. Equal frontiers exclude allocation from
that transition; this fact is independent of the observed event history. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do

theorem metadata_modifyDev (f : Device → Device)
    (hf : ∀ d, deviceAllocationMetadata (f d) = deviceAllocationMetadata d) :
    SameView allocationMetadata (modifyDev f) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' hr
  cases hr
  simp [allocationMetadata, Option.map_map, Function.comp_def, hf]

theorem setPeer_metadata (i : PeerId) (p : Peer) : SameView allocationMetadata (setPeer i p) :=
  metadata_modifyDev _ (fun _ => rfl)

theorem setKeypair_metadata (i : KeypairId) (k : Keypair) : SameView allocationMetadata (setKeypair i k) :=
  metadata_modifyDev _ (fun _ => rfl)

theorem setRxSkb_metadata (i : SkbId) (f : RxPacket → RxPacket) :
    SameView allocationMetadata (setRxSkb i f) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' hr
  cases x
  cases hd : w.dev with
  | none => simp [setRxSkb, liftSkb_run, hd] at hr
  | some d =>
    cases hp : d.rxSkbs[i]? with
    | none =>
      simp [setRxSkb, liftSkb_run, SkbStore.setRx, SkbStore.getRx,
        hd, hp, invariant, AmbientM.invariant] at hr
      cases hr
    | some p =>
      rw [Packets.setRxSkb_run w ambient d i p f hd hp] at hr
      cases hr
      simp [allocationMetadata, deviceAllocationMetadata, Packets.update, hd]

open Lean Meta Elab Tactic in
elab "allocation_release_head " n:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← (← getMainGoal).getType)).consumeMData
  unless target.isAppOf ``Preserves do throwError "not a frame contract"
  let action := target.getAppArgs.back!.consumeMData.headBeta
  let expected ← realizeGlobalConstNoOverloadWithInfo n
  unless action.getAppFn.constName? == some expected do throwError "different action head"

open Lean Meta Elab Tactic in
elab "allocation_release_step" : tactic => withMainContext do
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
elab "allocation_release_lift_from " carrier:ident : tactic => withMainContext do
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


theorem peerGet_metadata (id : PeerId) : SameView allocationMetadata (peerGet id) := by
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
      all_goals simp [allocationMetadata, deviceAllocationMetadata, hd]

theorem peerPut_metadata (id : Option PeerId) : SameView allocationMetadata (peerPut id) := by
  apply SameView.of_wp
  intro initial
  let P := fun w : WGWorld => allocationMetadata w = initial
  have ambient {α : Type} (a : AmbientM α) :
      Preserves P (monadLift a : WG.M α) := hoare_liftAmbient a P
  have index {α : Type} (a : IndexM α) :
      Preserves P (monadLift a : WG.M α) := by
    apply hoare_liftIndex a
    intro w d table hi hd
    simpa [P, allocationMetadata, deviceAllocationMetadata, hd] using hi
  have rc (old : Nat) : Preserves P (refcountDecAndTest old : WG.M Bool) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a x v a' hp hr
    simp [refcountDecAndTest, branch, branchCmp, AmbientM.branch,
      AmbientM.branchCmp, unsupported, AmbientM.unsupported] at hr
    repeat' split at hr
    all_goals simp_all
    all_goals rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
    all_goals exact hp
  have read (pid : PeerId) : Preserves P (getPeer pid) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a p v a' h hr
    rw [(Peers.getPeer_current pid w v p a a' hr).1]
    exact h
  change Preserves P (peerPut id)
  unfold peerPut
  simp (config := { zeta := true }) only [branch, invariant, requireNotPending,
    retirePeerUnits, modifyAmbient]
  repeat' first
    | (allocation_release_head getPeer; exact read _)
    | (allocation_release_head setPeer; exact (setPeer_metadata _ _).wp (fun t => t = initial))
    | (allocation_release_head modifyDev
       apply (hoare_iff_run_ambient _ _ _).mpr
       intro w a x v a' h hr
       cases hr
       cases hd : w.dev <;>
         simpa [P, allocationMetadata, deviceAllocationMetadata, hd] using h)
    | (allocation_release_head refcountDecAndTest; exact rc _)
    | (allocation_release_lift_from IndexM; exact index _)
    | (allocation_release_lift_from AmbientM; exact ambient _)
    | (allocation_release_head _root_.modify; apply hoare_modify; intro w h; exact h)
    | allocation_release_step

def keypairReleaseRest (w : WGWorld) := (Peers.snapshot w, packetResidents w, allocationMetadata w)

theorem keypairPut_rest (kp : Option KeypairId) (now : Bool) :
    SameView keypairReleaseRest (keypairPut kp now) := by
  apply SameView.of_wp
  intro initial
  let P := fun w : WGWorld => keypairReleaseRest w = initial
  have ambient {α : Type} (a : AmbientM α) :
      Preserves P (monadLift a : WG.M α) := hoare_liftAmbient a P
  have index {α : Type} (a : IndexM α) :
      Preserves P (monadLift a : WG.M α) := by
    apply hoare_liftIndex a
    intro w d table hi hd
    unfold P keypairReleaseRest Peers.snapshot packetResidents allocationMetadata at hi ⊢
    simpa only [hd, Option.bind_some, Option.map_some, deviceAllocationMetadata] using hi
  have rc (old : Nat) : Preserves P (refcountDecAndTest old : WG.M Bool) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a x v a' hp hr
    simp [refcountDecAndTest, branch, branchCmp, AmbientM.branch,
      AmbientM.branchCmp, unsupported, AmbientM.unsupported] at hr
    repeat' split at hr
    all_goals simp_all
    all_goals rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
    all_goals exact hp
  have read (i : KeypairId) : Preserves P (getKeypair i) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a k v a' h hr
    rw [(Keypairs.getKeypair_current i w v a a' k hr).1]
    exact h
  change Preserves P (keypairPut kp now)
  unfold keypairPut
  simp (config := { zeta := true }) only [branch, invariant]
  repeat' first
    | (allocation_release_head getKeypair; exact read _)
    | (allocation_release_head IndexOwner.peerDeref; exact indexOwner_peerDeref_preserves _ P)
    | (allocation_release_head setKeypair; unfold setKeypair)
    | (allocation_release_head modifyDev
       apply (hoare_iff_run_ambient _ _ _).mpr
       intro w a x v a' h hr
       cases hr
       unfold P keypairReleaseRest Peers.snapshot packetResidents allocationMetadata at h ⊢
       cases hd : w.dev <;>
         simpa [deviceAllocationMetadata, hd] using h)
    | (allocation_release_head refcountDecAndTest; exact rc _)
    | (allocation_release_lift_from IndexM; exact index _)
    | (allocation_release_lift_from AmbientM; exact ambient _)
    | (allocation_release_head _root_.modify; apply hoare_modify; intro w h; exact h)
    | allocation_release_step

theorem ordinary_same_frontier (ho : Keypairs.Ordinary s t) (hf : t.frontier = s.frontier) :
    ∀ i c, t.slots i = some c → s.slots i = some c := by
  induction ho with
  | refl => exact fun _ _ h => h
  | erase s j =>
    intro i c hc
    by_cases he : i = j
    · subst i; simp at hc
    · simpa [Keypairs.Snapshot.put, he] using hc
  | empty => intro i c hc; cases hc
  | fresh => simp [Keypairs.Snapshot.fresh] at hf
  | @trans s t u first second ih₁ ih₂ =>
    have hf₁ : t.frontier = s.frontier := by
      have := first.frontier_mono; have := second.frontier_mono; omega
    have hf₂ : u.frontier = t.frontier := hf.trans hf₁.symm
    exact fun i c hc => ih₁ hf₁ i c (ih₂ hf₂ i c hc)

theorem keypairPut_retention (kp : Option KeypairId) (now : Bool) (w v : WGWorld)
    (ambient ambient' : Ambient)
    (hr : ((keypairPut kp now).run w).run ambient = .ok ((x, v), ambient')) : AllocationRetention w v := by
  have hrest := (ProjectedAction.iff_run_ambient _ _ _).mp
    (keypairPut_rest kp now) w ambient x v ambient' hr
  have hp : Peers.snapshot v = Peers.snapshot w := congrArg Prod.fst hrest
  have ht : packetResidents v = packetResidents w := congrArg (fun s => s.2.1) hrest
  have hm : allocationMetadata v = allocationMetadata w := congrArg (fun s => s.2.2) hrest
  have hf : (Keypairs.snapshot v).frontier = (Keypairs.snapshot w).frontier :=
    congrArg AllocationMetadata.keyCounter hm
  have retained := ordinary_same_frontier ((ProjectedAction.iff_run_ambient _ _ _).mp
    (Keypairs.keypairPut_ordinary kp now) w ambient x v ambient' hr) hf
  refine ⟨hm, hp ▸ Retained.refl _, ?_, fun i stamp hi => ht ▸ hi⟩
  intro i stamp hi
  have projected (q : WGWorld) : keypairResidents q i =
      ((Keypairs.snapshot q).slots i).map (·.stamp) := by
    simp [keypairResidents, Keypairs.snapshot, Keypairs.cell, Option.map_map, Function.comp_def]
  rw [projected] at hi
  cases hc : (Keypairs.snapshot v).slots i with
  | none => simp [hc] at hi
  | some c =>
    have old := retained i c hc
    rw [projected, old]
    simpa only [hc] using hi

theorem peerGet_retention (id : PeerId) (w v : WGWorld)
    (ambient ambient' : Ambient)
    (hr : ((peerGet id).run w).run ambient = .ok ((x, v), ambient')) : AllocationRetention w v := by
  have rest := (ProjectedAction.iff_run_ambient _ _ _).mp
    (peerGet_otherResidents id) w ambient x v ambient' hr
  have hk : keypairResidents v = keypairResidents w := congrArg Prod.fst rest
  have ht : packetResidents v = packetResidents w := congrArg Prod.snd rest
  exact ⟨(ProjectedAction.iff_run_ambient _ _ _).mp (peerGet_metadata id) w ambient x v ambient' hr,
    (ProjectedAction.iff_run_ambient _ _ _).mp (Peers.peerGet_retained id) w ambient x v ambient' hr,
    fun i stamp hi => hk ▸ hi,
    fun i stamp hi => ht ▸ hi⟩

theorem peerPut_retention (id : Option PeerId) (w v : WGWorld)
    (ambient ambient' : Ambient)
    (hr : ((peerPut id).run w).run ambient = .ok ((x, v), ambient')) : AllocationRetention w v := by
  have rest := (ProjectedAction.iff_run_ambient _ _ _).mp
    (peerPut_otherResidents id) w ambient x v ambient' hr
  have hk : keypairResidents v = keypairResidents w := congrArg Prod.fst rest
  have ht : packetResidents v = packetResidents w := congrArg Prod.snd rest
  exact ⟨(ProjectedAction.iff_run_ambient _ _ _).mp (peerPut_metadata id) w ambient x v ambient' hr,
    (ProjectedAction.iff_run_ambient _ _ _).mp (Peers.peerPut_retained id) w ambient x v ambient' hr,
    fun i stamp hi => hk ▸ hi,
    fun i stamp hi => ht ▸ hi⟩

end Leanux.Proofs.WG.Lifetimes
