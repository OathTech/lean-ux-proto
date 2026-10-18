import Leanux.Proofs.WG.Keypairs.Evolution.Scheduler

/-! Framing original worker dispatch and the bounded scheduler with explicit
ordinary callback contracts. Receive-capable callbacks are handled separately by
the logged evolution layer. -/
namespace Leanux.Proofs.WG.Keypairs.EnvFrames
open Leanux Leanux.WG Std.Do Leanux.Proofs.WG.Keypairs
open Leanux.Proofs.Framing
open WGFrames WGTransitions WGMore WGConfig WGDevice
open Observers SchedulerObservers
open Lean Meta Elab Tactic

set_option maxHeartbeats 400000
set_option pp.structureInstances false

private theorem workerAmbient (a : AmbientM α) :
    ProductOrdinaryAction (monadLift a : Leanux.M α) := by
  apply SameView.ordinary
  intro initial
  exact productAmbient_spec a (fun w => snapshot w.wg = initial) (fun _ _ h => h)

/-- Prove each compiler-generated continuation once, then use its contract. -/
elab "env_product_join_let" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``ProductOrdinaryAction || target.isAppOf ``Lifetimes.ProjectedAction do throwError "not ProductOrdinaryAction"
  let action := target.getAppArgs.back! |>.consumeMData
  let .letE name ty value body _ := action | throwError "not a let"
  unless name.toString.startsWith "__do_jp" do throwError "not a join continuation"
  let property ← forallTelescope ty fun args _ => do
    let result ← mkAppM ``ProductOrdinaryAction #[mkAppN value args]
    mkForallFVars args result
  let valueProof ← mkFreshExprSyntheticOpaqueMVar property
  let (continuation, next) ← withLocalDeclD name ty fun f => do
    let contract ← forallTelescope ty fun args _ => do
      let result ← mkAppM ``ProductOrdinaryAction #[mkAppN f args]
      mkForallFVars args result
    withLocalDeclD `env_product_join contract fun hf => do
      let bodyProp ← mkAppM ``ProductOrdinaryAction #[body.instantiate1 f]
      let next ← mkFreshExprSyntheticOpaqueMVar bodyProp
      let proof ← mkLambdaFVars #[f, hf] next
      pure (proof, next.mvarId!)
  goal.assign (mkApp2 continuation value valueProof)
  replaceMainGoal [valueProof.mvarId!, next]

elab "env_product_join_use" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``ProductOrdinaryAction || target.isAppOf ``Lifetimes.ProjectedAction do throwError "not ProductOrdinaryAction"
  let action := target.getAppArgs.back! |>.consumeMData |>.headBeta
  unless action.getAppFn.isFVar do throwError "not a local continuation"
  for decl in ← getLCtx do
    if decl.userName == `env_product_join then
      let proof := mkAppN decl.toExpr action.getAppArgs
      try
        if ← withReducible (isDefEq (← inferType proof) target) then
          goal.assign proof
          replaceMainGoal []
          return
      catch _ => pure ()
  throwError "no continuation contract"

macro "env_product_step" : tactic => `(tactic|
  first
    | (unfold ProductOrdinaryAction)
    | (simp (config := { failIfUnchanged := true }) only [monadLift_self])
    | keypairs_intro_forall
    | with_reducible assumption
    | env_product_join_let
    | env_product_join_use
    | (ordinary_head Leanux.hidden; exact workerAmbient (AmbientM.hidden _))
    | (ordinary_head Leanux.hiddenClock64; exact workerAmbient (AmbientM.hiddenClock64 _))
    | (ordinary_head Leanux.hiddenJiffies; exact workerAmbient (AmbientM.hiddenJiffies _))
    | (ordinary_head Leanux.branch; exact workerAmbient (AmbientM.branch _ _))
    | (ordinary_head Leanux.branchCmp; exact workerAmbient (AmbientM.branchCmp _ _ _ _))
    | (ordinary_head Leanux.recordBudget; exact workerAmbient AmbientM.recordBudget)
    | (ordinary_head Leanux.budgetExhausted; exact workerAmbient (AmbientM.budgetExhausted _))
    | (ordinary_head Leanux.peekUnit; exact workerAmbient (AmbientM.peekUnit _))
    | (ordinary_head Leanux.resolveUnit; exact workerAmbient (AmbientM.resolveUnit _ _ _))
    | (ordinary_head Leanux.peekHiddenSite; exact workerAmbient AmbientM.peekHiddenSite)
    | (ordinary_head Leanux.getAmbient; exact workerAmbient (get : AmbientM Ambient))
    | (ordinary_head Leanux.invariant; exact workerAmbient (AmbientM.invariant _))
    | (ordinary_head Leanux.unsupported; exact workerAmbient (AmbientM.unsupported _))
    | (ordinary_head Leanux.modifyAmbient; unfold Leanux.modifyAmbient)
    | (ordinary_head liftM; first | exact workerAmbient _ | apply OrdinaryAction.liftWG)
    | (ordinary_head MonadLift.monadLift; first | exact workerAmbient _ | apply OrdinaryAction.liftWG)
    | (ordinary_head MonadLiftT.monadLift; first | exact workerAmbient _ | apply OrdinaryAction.liftWG)
    | (ordinary_head Pure.pure; exact SameView.ordinary (SameView.pure _ _))
    | env_ordinary_head_reduce
    | observer_ordinary_leaf
    | ordinary_strict_step)

theorem runWorker_sameSnapshot (worker : Worker) (body : Leanux.M Unit)
    (hb : SameView (fun w : World => snapshot w.wg) body) : SameView (fun w : World => snapshot w.wg) (Env.runWorker worker body) :=
  Framing.runWorker_sameView (fun w => snapshot w.wg)
    (fun _ _ he => congrArg
      (fun s : ProductStore43 =>
        (⟨s.2.2.2.keypairCounter, fun i => (s.2.2.2.dev.bind fun d => d.keypairs[i]?).map cell⟩ : Snapshot)) he)
    worker body hb

theorem runWorker_snapshot_spec (P : Snapshot → Prop) (worker : Worker)
    (body : Leanux.M Unit) (hb : SameView (fun w : World => snapshot w.wg) body) :
    ⦃fun w => ⌜P (snapshot w.wg)⌝⦄ Env.runWorker worker body
    ⦃⇓? _ w => ⌜P (snapshot w.wg)⌝⦄ := (runWorker_sameSnapshot worker body hb).wp P

theorem runWorker_ordinary (worker : Worker) (body : Leanux.M Unit)
    (hb : ProductOrdinaryAction body) : ProductOrdinaryAction (Env.runWorker worker body) := by
  unfold Env.runWorker
  repeat' env_product_step

macro "env_worker_step" : tactic => `(tactic|
  first
    | (ordinary_head Env.runWorker; refine runWorker_ordinary _ _ ?_)
    | (ordinary_head Env.condResched; exact SameView.ordinary (condResched_sameSnapshot _))
    | (ordinary_head Env.deliverSent; exact SameView.ordinary deliverSent_sameSnapshot)
    | env_product_step)

theorem runWorker_spec (P : Snapshot → Prop) (hp : Stable P) (worker : Worker)
    (body : Leanux.M Unit) (hb : ProductOrdinaryAction body) :
    ⦃fun w => ⌜P (snapshot w.wg)⌝⦄ Env.runWorker worker body
    ⦃⇓? _ w => ⌜P (snapshot w.wg)⌝⦄ := (runWorker_ordinary worker body hb).wp P hp

theorem workerIter_ordinary (w : Worker) (pid : Option Nat) (step afterItem : Leanux.M Bool)
    (hs : ProductOrdinaryAction step) (ha : ProductOrdinaryAction afterItem) :
    ProductOrdinaryAction (workerIter w pid step afterItem) := by
  unfold workerIter
  repeat' env_worker_step

theorem workerLoop_ordinary (w : Worker) (pid : Option Nat) (step : Leanux.M Bool)
    (afterItem : Leanux.M Unit) (bound : Nat) (drained : String)
    (hs : ProductOrdinaryAction step) (ha : ProductOrdinaryAction afterItem) :
    ProductOrdinaryAction (workerLoop w pid step afterItem bound drained) := by
  unfold workerLoop
  repeat' first
    | (ordinary_head workerIter; refine workerIter_ordinary _ _ _ _ hs ?_)
    | env_worker_step

theorem encryptStep_ordinary (checksum : Packet → Leanux.M Packet) (softirq : Leanux.M Unit)
    (hc : ∀ pkt, ProductOrdinaryAction (checksum pkt)) (hs : ProductOrdinaryAction softirq) :
    ProductOrdinaryAction (WG.encryptStep checksum softirq) := by
  have poll : ProductOrdinaryAction (WG.encryptRingPoll softirq) := by
    unfold WG.encryptRingPoll
    repeat' env_worker_step
  apply (ordinaryAction_iff_wp _).mpr
  intro P hp
  have poll_spec := Lifetimes.ProjectedAction.wp poll P hp
  have enc (id : KeypairId) (pkt : DataPacket) :=
    Lifetimes.ProjectedAction.wp (encryptPacket_ordinary checksum hc id pkt) P hp
  have packetStore (α : Type) (a : WG.SkbM α) :
      ProductOrdinaryAction (MonadLift.monadLift (WG.liftSkb a) : Leanux.M α) := by
    apply OrdinaryAction.liftWG
    apply SameView.ordinary
    intro initial
    apply hoare_liftSkb _ (fun w => snapshot w = initial)
    intro g d store hg hd
    simpa [snapshot, hd] using hg
  have readPacket (id : SkbId) :
      ⦃fun w : World => ⌜P (snapshot w.wg)⌝⦄
        (MonadLift.monadLift (WG.getTxSkb id) : Leanux.M _)
      ⦃⇓? _ w => ⌜P (snapshot w.wg)⌝⦄ :=
    Lifetimes.ProjectedAction.wp (packetStore _ _) P hp
  have writePacket (id : SkbId) (f : DataPacket → DataPacket) :
      ⦃fun w : World => ⌜P (snapshot w.wg)⌝⦄
        (MonadLift.monadLift (WG.setTxSkb id f) : Leanux.M _)
      ⦃⇓? _ w => ⌜P (snapshot w.wg)⌝⦄ :=
    Lifetimes.ProjectedAction.wp (packetStore _ _) P hp
  have enqueue (item : List SkbId) (state : PacketState) :
      ⦃fun w : World => ⌜P (snapshot w.wg)⌝⦄
        (MonadLift.monadLift (WG.enqueuePerPeerTx item state) : Leanux.M _)
      ⦃⇓? _ w => ⌜P (snapshot w.wg)⌝⦄ :=
    Lifetimes.ProjectedAction.wp
      (OrdinaryAction.liftWG (SameView.ordinary (enqueuePerPeerTx_sameSnapshot item state))) P hp
  have ambient := fun α (a : AmbientM α) => productAmbient_spec a
    (fun w => P (snapshot w.wg)) (fun _ _ h => h)
  change Preserves (fun w => P (snapshot w.wg)) (WG.encryptStep checksum softirq)
  unfold WG.encryptStep
  apply preserves_bind poll_spec
  intro item
  cases item with
  | none => exact preserves_pure _
  | some first =>
    dsimp only
    cases hh : first.head? with
    | none => exact ambient _ (AmbientM.invariant _)
    | some headId =>
      dsimp only
      apply preserves_bind (readPacket headId)
      intro head
      refine preserves_bind (list_view_spec (m := Except Stop)
        (fun w : World => snapshot w.wg) P _ _ _ ?_) ?_
      · intro id state
        apply preserves_bind (ambient _ (AmbientM.branch .encWorkerSkbIterate true))
        intro _
        apply preserves_bind (readPacket id)
        intro packet
        apply preserves_bind (enc head.keypair packet)
        intro encrypted
        apply preserves_bind (ambient _ (AmbientM.branch .encWorkerEncrypted encrypted.isSome))
        intro success
        split
        · exact preserves_bind (writePacket id _) (fun _ => preserves_pure _)
        · exact preserves_pure _
      · intro state
        split
        · exact preserves_bind (ambient _ (AmbientM.branch .encWorkerSkbIterate false))
            (fun _ => preserves_bind (enqueue first state) (fun _ => preserves_pure _))
        · exact preserves_bind (enqueue first state) (fun _ => preserves_pure _)

theorem encryptIter_ordinary (checksum : Packet → Leanux.M Packet) (softirq : Leanux.M Unit) (need : Leanux.M Bool)
    (hc : ∀ pkt, ProductOrdinaryAction (checksum pkt)) (hs : ProductOrdinaryAction softirq)
    (hn : ProductOrdinaryAction need) : ProductOrdinaryAction (WG.encryptIter checksum softirq need) := by
  unfold WG.encryptIter
  refine workerIter_ordinary _ _ _ _ (encryptStep_ordinary checksum softirq hc hs) ?_
  repeat' env_worker_step

theorem txIter_ordinary (pid : PeerId) (need : Leanux.M Bool) (hn : ProductOrdinaryAction need) :
    ProductOrdinaryAction (WG.txIter pid need) := by
  unfold WG.txIter
  refine workerIter_ordinary _ _ _ _ (txStep_ordinary pid).liftWG ?_
  repeat' env_worker_step

theorem handshakeReceiveWorker_ordinary (resched : Leanux.M Unit) (hr : ProductOrdinaryAction resched) :
    ProductOrdinaryAction (WG.handshakeReceiveWorker resched) := by
  exact workerLoop_ordinary _ _ _ _ _ _ receiveStep_ordinary.liftWG hr

theorem handshakeReceiveWorker_spec (P : Snapshot → Prop) (hp : Stable P)
    (resched : Leanux.M Unit) (hr : ProductOrdinaryAction resched) :
    ⦃fun w => ⌜P (snapshot w.wg)⌝⦄ WG.handshakeReceiveWorker resched
    ⦃⇓? _ w => ⌜P (snapshot w.wg)⌝⦄ := (handshakeReceiveWorker_ordinary resched hr).wp P hp

end Leanux.Proofs.WG.Keypairs.EnvFrames
