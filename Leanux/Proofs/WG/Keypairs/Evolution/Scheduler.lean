import Leanux.Proofs.WG.Keypairs.Evolution.Observers
import Leanux.Proofs.Logged.Scheduler
import Leanux.Proofs.WG.Keypairs.Frames.EnvLeaves

/-! Lifetime evolution through the remaining workers and the bounded receive
scheduler. The original checksum callback and logged scheduling callbacks retain
explicit contracts; no scheduling restriction is added. -/
namespace Leanux.Proofs.WG.Keypairs.SchedulerObservers
open Leanux Leanux.WG Leanux.Env Std.Do Leanux.Proofs.Logged
open Leanux.Proofs.WG.Keypairs Leanux.Proofs.WG.Keypairs.Observers
open Leanux.Proofs.Framing
open WGFrames WGTransitions WGMore WGConfig EnvFrames

set_option maxHeartbeats 400000
set_option pp.structureInstances false


private theorem schedulerAmbient (a : AmbientM α) :
    ProductOrdinaryAction (monadLift a : Leanux.M α) := by
  apply SameView.ordinary
  intro initial
  exact productAmbient_spec a (fun w => snapshot w.wg = initial) (fun _ _ h => h)

private theorem schedulerGetEnv : ProductOrdinaryAction getEnv := by
  apply (Lifetimes.ProjectedAction.iff_run _ _ _).mpr
  intro w x v hr
  change Except.ok (w.fixture, w) = Except.ok (x, v) at hr
  cases hr
  exact .refl _

private theorem schedulerModifyEnv (f : EnvWorld → EnvWorld) : ProductOrdinaryAction (modifyEnv f) := by
  apply (Lifetimes.ProjectedAction.iff_run _ _ _).mpr
  intro w x v hr
  change Except.ok ((), {w with fixture := f w.fixture}) = Except.ok (x, v) at hr
  cases hr
  exact .refl _

macro "scheduler_evolves_step" : tactic => `(tactic|
  first
    | (evolves_head Leanux.getAmbient; exact evolves_lift (schedulerAmbient (get : AmbientM Ambient)))
    | (evolves_head Leanux.peekUnit; exact evolves_lift (schedulerAmbient (AmbientM.peekUnit _)))
    | (evolves_head Leanux.resolveUnit; exact evolves_lift (schedulerAmbient (AmbientM.resolveUnit _ _ _)))
    | (unfold ProductOrdinaryAction)
    | (ordinary_head Leanux.getEnv; exact schedulerGetEnv)
    | (ordinary_head Leanux.modifyEnv; exact schedulerModifyEnv _)
    | env_ordinary_head_reduce
    | evolves_step)

theorem encryptPacket_ordinary (checksum : Packet → Leanux.M Packet)
    (hc : ∀ pkt, ProductOrdinaryAction (checksum pkt)) (kp : KeypairId) (pkt : DataPacket) :
    ProductOrdinaryAction (WG.encryptPacket checksum kp pkt) := by
  apply (ordinaryAction_iff_wp _).mpr
  intro P hp
  have checksum_spec (p : Packet) := Lifetimes.ProjectedAction.wp (hc p) P hp
  have ambient := fun α (a : AmbientM α) => productAmbient_spec a
    (fun w => P (snapshot w.wg)) (fun _ _ h => h)
  have padding (len mtu : Nat) :
      ⦃fun w : World => ⌜P (snapshot w.wg)⌝⦄
        (MonadLift.monadLift (calculateSkbPadding len mtu) : Leanux.M _)
      ⦃⇓? _ w => ⌜P (snapshot w.wg)⌝⦄ := Lifetimes.ProjectedAction.wp
    (OrdinaryAction.liftWG (SameView.ordinary (calculateSkbPadding_sameSnapshot len mtu))) P hp
  have key (id : KeypairId) :
      ⦃fun w : World => ⌜P (snapshot w.wg)⌝⦄
        (MonadLift.monadLift (getKeypair id) : Leanux.M _)
      ⦃⇓? _ w => ⌜P (snapshot w.wg)⌝⦄ := Lifetimes.ProjectedAction.wp
    (OrdinaryAction.liftWG (SameView.ordinary (getKeypair_sameSnapshot id))) P hp
  unfold Hoare at ambient
  mvcgen [-Std.Do.Spec.monadLift_StateT, WG.encryptPacket, skipCut, hiddenAlloc,
    branch, padding, key, checksum_spec, ambient]

theorem encryptStepLogged_evolves (checksum : Packet → Leanux.M Packet) (softirq : GhostM Unit)
    (hc : ∀ pkt, ProductOrdinaryAction (checksum pkt)) (hs : Evolves softirq) :
    Evolves (encryptStepLogged checksum softirq) := by
  unfold encryptStepLogged WG.encryptRingPoll
  repeat' first
    | (ordinary_head WG.encryptPacket; exact encryptPacket_ordinary _ hc _ _)
    | (ordinary_head WG.enqueuePerPeerTx; exact SameView.ordinary (enqueuePerPeerTx_sameSnapshot _ _))
    | scheduler_evolves_step

theorem encryptIterLogged_evolves (checksum : Packet → Leanux.M Packet)
    (softirq : GhostM Unit) (needResched : GhostM Bool)
    (hc : ∀ pkt, ProductOrdinaryAction (checksum pkt)) (hs : Evolves softirq) (hr : Evolves needResched) :
    Evolves (encryptIterLogged checksum softirq needResched) := by
  unfold encryptIterLogged
  refine workerIterLogged_evolves _ _ _ _ (encryptStepLogged_evolves _ _ hc hs) ?_
  repeat' scheduler_evolves_step

theorem txStep_ordinary (pid : PeerId) : OrdinaryAction (WG.txStep pid) := by
  unfold WG.txStep
  repeat' first
    | (ordinary_head WG.createDataDone; exact SameView.ordinary (createDataDone_sameSnapshot _ _))
    | observer_ordinary_leaf
    | env_ordinary_head_reduce
    | ordinary_strict_step

theorem txIterLogged_evolves (pid : PeerId) (needResched : GhostM Bool)
    (hr : Evolves needResched) : Evolves (txIterLogged pid needResched) := by
  unfold txIterLogged
  refine workerIterLogged_evolves _ _ _ _ (evolves_liftM (txStep_ordinary pid).liftWG) ?_
  repeat' scheduler_evolves_step

theorem receiveStep_ordinary : OrdinaryAction WG.receiveStep := by
  unfold WG.receiveStep
  repeat' first
    | (ordinary_head WG.receiveHandshakePacket; exact receiveHandshakePacket_ordinary _ _)
    | observer_ordinary_leaf
    | env_ordinary_head_reduce
    | ordinary_strict_step

theorem handshakeReceiveWorkerLogged_evolves (resched : GhostM Unit)
    (hr : Evolves resched) : Evolves (handshakeReceiveWorkerLogged resched) := by
  exact workerLoopLogged_evolves _ _ _ _ _ _ (evolves_liftM receiveStep_ordinary.liftWG) hr

macro "scheduler_worker_step" : tactic => `(tactic|
  first
    | (evolves_head runWorkerLogged; refine runWorkerLogged_evolves _ _ ?_)
    | (ordinary_head Env.condResched; exact SameView.ordinary (condResched_sameSnapshot _))
    | (ordinary_head Env.Activation.occupancy; exact SameView.ordinary (activationOccupancy_sameSnapshot _))
    | (ordinary_head Env.Activation.hasWork; exact SameView.ordinary (activationHasWork_sameSnapshot _))
    | (ordinary_head List.filterM;
        exact SameView.ordinary (filterM_sameSnapshot Env.Activation.consistent activationConsistent_sameSnapshot _))
    | (ordinary_head Leanux.Env.deliverSent; exact SameView.ordinary deliverSent_sameSnapshot)
    | scheduler_evolves_step)

theorem napiSoftirqLogged_evolves : Evolves napiSoftirqLogged := by
  unfold napiSoftirqLogged
  repeat' first
    | (evolves_head rxPollLogged; refine rxPollLogged_evolves _ _ _ ?_
       intro packets
       exact evolves_liftM (ordinary_forM packets Env.deliverInner deliverInner_ordinary))
    | scheduler_worker_step

theorem napiIrqExitLogged_evolves : Evolves napiIrqExitLogged := by
  unfold napiIrqExitLogged
  repeat' first
    | (evolves_head napiSoftirqLogged; exact napiSoftirqLogged_evolves)
    | scheduler_worker_step

theorem cryptAheadLogged_evolves (pid : PeerId) : Evolves (cryptAheadLogged pid) := by
  unfold cryptAheadLogged
  repeat' first
    | with_reducible exact evolves_throw _
    | (evolves_head encryptIterLogged;
        refine encryptIterLogged_evolves _ _ _ (fun p => SameView.ordinary (checksumHelp_sameSnapshot p))
          napiSoftirqLogged_evolves ?_)
    | scheduler_worker_step

theorem activationIterLogged_evolves (a : Activation) : Evolves (activationIterLogged a) := by
  unfold activationIterLogged
  repeat' first
    | (evolves_head cryptAheadLogged; exact cryptAheadLogged_evolves _)
    | (evolves_head encryptIterLogged;
        refine encryptIterLogged_evolves _ _ _ (fun p => SameView.ordinary (checksumHelp_sameSnapshot p))
          napiSoftirqLogged_evolves ?_)
    | (evolves_head txIterLogged; refine txIterLogged_evolves _ _ ?_)
    | (evolves_head decryptIterLogged;
        refine decryptIterLogged_evolves _ _ _ napiSoftirqLogged_evolves napiIrqExitLogged_evolves ?_)
    | (evolves_head workerIterLogged;
        refine workerIterLogged_evolves _ _ _ _ (evolves_liftM receiveStep_ordinary.liftWG) ?_)
    | scheduler_worker_step

theorem activationRunLogged_evolves (a : Activation) : Evolves (activationRunLogged a) := by
  unfold activationRunLogged
  repeat' first
    | (evolves_head activationIterLogged; exact activationIterLogged_evolves _)
    | scheduler_worker_step

theorem dispatchActivationLogged_evolves (w : Worker) : Evolves (dispatchActivationLogged w) := by
  unfold dispatchActivationLogged
  repeat' first
    | (evolves_head activationRunLogged; exact activationRunLogged_evolves _)
    | scheduler_worker_step

theorem scheduleLogged_evolves (stack : Option Worker) : Evolves (scheduleLogged stack) := by
  unfold scheduleLogged
  repeat' first
    | (evolves_head dispatchActivationLogged; exact dispatchActivationLogged_evolves _)
    | (evolves_head napiSoftirqLogged; exact napiSoftirqLogged_evolves)
    | (evolves_head activationRunLogged; exact activationRunLogged_evolves _)
    | scheduler_worker_step

theorem nestedReschedLogged_evolves (self : Worker) : Evolves (nestedReschedLogged self) := by
  unfold nestedReschedLogged
  repeat' first
    | (evolves_head scheduleLogged; exact scheduleLogged_evolves _)
    | scheduler_worker_step

theorem runCryptWorkersLogged_evolves : Evolves runCryptWorkersLogged := by
  unfold runCryptWorkersLogged
  repeat' first
    | (evolves_head scheduleLogged; exact scheduleLogged_evolves _)
    | scheduler_worker_step

end Leanux.Proofs.WG.Keypairs.SchedulerObservers
