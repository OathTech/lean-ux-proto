import Leanux.Proofs.WG.Keypairs.Evolution.Observers
import Leanux.Proofs.Logged.Scheduler
import Leanux.Proofs.WG.Keypairs.Frames.EnvLeaves

/-! Lifetime evolution through the remaining workers and the bounded receive
scheduler. The original checksum callback and logged scheduling callbacks retain
explicit contracts; no scheduling restriction is added. -/
namespace Leanux.Proofs.WG.Keypairs.SchedulerObservers
open Leanux Leanux.WG Leanux.Env Std.Do Leanux.Proofs.Logged
open Leanux.Proofs.WG.Keypairs Leanux.Proofs.WG.Keypairs.Observers
open KernelFrames WGFrames WGTransitions WGMore WGConfig EnvFrames

set_option maxHeartbeats 400000
set_option pp.structureInstances false

theorem encryptPacket_ordinary (checksum : Packet → M Packet)
    (hc : ∀ pkt, OrdinaryAction (checksum pkt)) (kp : KeypairId) (pkt : DataPacket) :
    OrdinaryAction (WG.encryptPacket checksum kp pkt) := by
  have checksum_spec (P : Snapshot → Prop) (hp : Stable P) (p : Packet) :=
    (hc p).wp P hp
  frame_ordinary [WG.encryptPacket] using [skipCut_spec, calculateSkbPadding_spec,
    hiddenAlloc_snapshot_spec, getKeypair_spec] ordinary [checksum_spec]

theorem encryptStepLogged_evolves (checksum : Packet → M Packet) (softirq : GhostM Unit)
    (hc : ∀ pkt, OrdinaryAction (checksum pkt)) (hs : Evolves softirq) :
    Evolves (encryptStepLogged checksum softirq) := by
  unfold encryptStepLogged
  repeat' first
    | (ordinary_head WG.encryptPacket; exact encryptPacket_ordinary _ hc _ _)
    | (ordinary_head WG.enqueuePerPeerTx; exact (enqueuePerPeerTx_sameSnapshot _ _).ordinary)
    | evolves_step

theorem encryptIterLogged_evolves (checksum : Packet → M Packet)
    (softirq : GhostM Unit) (needResched : GhostM Bool)
    (hc : ∀ pkt, OrdinaryAction (checksum pkt)) (hs : Evolves softirq) (hr : Evolves needResched) :
    Evolves (encryptIterLogged checksum softirq needResched) := by
  unfold encryptIterLogged
  refine workerIterLogged_evolves _ _ _ _ (encryptStepLogged_evolves _ _ hc hs) ?_
  repeat' evolves_step

theorem txStep_ordinary (pid : PeerId) : OrdinaryAction (WG.txStep pid) := by
  unfold WG.txStep
  repeat' first
    | (ordinary_head WG.createDataDone; exact (createDataDone_sameSnapshot _ _).ordinary)
    | observer_ordinary_leaf
    | ordinary_strict_step

theorem txIterLogged_evolves (pid : PeerId) (needResched : GhostM Bool)
    (hr : Evolves needResched) : Evolves (txIterLogged pid needResched) := by
  unfold txIterLogged
  refine workerIterLogged_evolves _ _ _ _ (evolves_liftM (txStep_ordinary pid)) ?_
  repeat' evolves_step

theorem receiveStep_ordinary : OrdinaryAction WG.receiveStep := by
  unfold WG.receiveStep
  repeat' first
    | (ordinary_head WG.receiveHandshakePacket; exact receiveHandshakePacket_ordinary _ _)
    | observer_ordinary_leaf
    | ordinary_strict_step

theorem handshakeReceiveWorkerLogged_evolves (resched : GhostM Unit)
    (hr : Evolves resched) : Evolves (handshakeReceiveWorkerLogged resched) := by
  exact workerLoopLogged_evolves _ _ _ _ _ _ (evolves_liftM receiveStep_ordinary) hr

macro "scheduler_worker_step" : tactic => `(tactic|
  first
    | (evolves_head runWorkerLogged; refine runWorkerLogged_evolves _ _ ?_)
    | (ordinary_head Leanux.peekUnit; exact (peekUnit_sameSnapshot _).ordinary)
    | (ordinary_head Leanux.resolveUnit; exact (resolveUnit_sameSnapshot _ _ _).ordinary)
    | (ordinary_head Env.condResched; exact (condResched_sameSnapshot _).ordinary)
    | (ordinary_head Env.Activation.hasWork; exact (activationHasWork_sameSnapshot _).ordinary)
    | (ordinary_head List.filterM;
        exact (filterM_sameSnapshot Env.Activation.consistent activationConsistent_sameSnapshot _).ordinary)
    | (ordinary_head Leanux.Env.deliverSent; exact deliverSent_sameSnapshot.ordinary)
    | evolves_step)

theorem napiSoftirqLogged_evolves : Evolves napiSoftirqLogged := by
  unfold napiSoftirqLogged
  repeat' first
    | (evolves_head rxPollLogged; refine rxPollLogged_evolves _ _ _ ?_
       intro packets
       exact evolves_liftM (ordinary_forM packets Env.deliverInner deliverInner_ordinary))
    | scheduler_worker_step

theorem napiIrqExitLogged_evolves : Evolves napiIrqExitLogged := by
  have tail : Evolves (do
      let w ← getWorld
      setWorld { w with napiBeforePut := w.napiBeforePut.drop 1, napiAmbiguous := w.napiAmbiguous + 1 }
      if w.napiBeforePut.headD false then napiSoftirqLogged) := by
    refine evolves_read_write _ _ (fun _ => Ordinary.refl _) ?_
    intro w
    exact evolves_ite _ (fun _ => napiSoftirqLogged_evolves) (fun _ => evolves_pure ())
  unfold napiIrqExitLogged
  repeat' first | with_reducible exact tail | evolves_step

theorem activationIterLogged_evolves (a : Activation) : Evolves (activationIterLogged a) := by
  unfold activationIterLogged
  repeat' first
    | (evolves_head encryptIterLogged;
        refine encryptIterLogged_evolves _ _ _ (fun p => (checksumHelp_sameSnapshot p).ordinary)
          napiSoftirqLogged_evolves ?_)
    | (evolves_head txIterLogged; refine txIterLogged_evolves _ _ ?_)
    | (evolves_head decryptIterLogged;
        refine decryptIterLogged_evolves _ _ _ napiSoftirqLogged_evolves napiIrqExitLogged_evolves ?_)
    | (evolves_head workerIterLogged;
        refine workerIterLogged_evolves _ _ _ _ (evolves_liftM receiveStep_ordinary) ?_)
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
