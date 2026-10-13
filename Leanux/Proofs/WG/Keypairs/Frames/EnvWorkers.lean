import Leanux.Proofs.WG.Keypairs.Evolution.Scheduler

/-! Framing original worker dispatch and the bounded scheduler with explicit
ordinary callback contracts. Receive-capable callbacks are handled separately by
the logged evolution layer. -/
namespace Leanux.Proofs.WG.Keypairs.EnvFrames
open Leanux Leanux.WG Std.Do Leanux.Proofs.WG.Keypairs
open KernelFrames WGFrames WGTransitions WGMore WGConfig WGDevice
open Observers SchedulerObservers

set_option maxHeartbeats 400000
set_option pp.structureInstances false

theorem runWorker_sameSnapshot (worker : Worker) (body : M Unit)
    (hb : SameSnapshot body) : SameSnapshot (Env.runWorker worker body) := by
  have body_spec (P : Snapshot → Prop) := hb.wp P
  frame_same [Env.runWorker] using [hidden_snapshot_spec, peekHiddenSite_spec, body_spec]

theorem runWorker_snapshot_spec (P : Snapshot → Prop) (worker : Worker)
    (body : M Unit) (hb : SameSnapshot body) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Env.runWorker worker body
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (runWorker_sameSnapshot worker body hb).wp P

theorem runWorker_ordinary (worker : Worker) (body : M Unit)
    (hb : OrdinaryAction body) : OrdinaryAction (Env.runWorker worker body) := by
  unfold Env.runWorker
  repeat' first | observer_ordinary_leaf | ordinary_strict_step

theorem runWorker_spec (P : Snapshot → Prop) (hp : Stable P) (worker : Worker)
    (body : M Unit) (hb : OrdinaryAction body) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Env.runWorker worker body
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (runWorker_ordinary worker body hb).wp P hp

theorem workerIter_ordinary (w : Worker) (pid : Option Nat) (step afterItem : M Bool)
    (hs : OrdinaryAction step) (ha : OrdinaryAction afterItem) :
    OrdinaryAction (workerIter w pid step afterItem) := by
  unfold workerIter
  repeat' first | observer_ordinary_leaf | ordinary_strict_step

theorem workerLoop_ordinary (w : Worker) (pid : Option Nat) (step : M Bool)
    (afterItem : M Unit) (bound : Nat) (drained : String)
    (hs : OrdinaryAction step) (ha : OrdinaryAction afterItem) :
    OrdinaryAction (workerLoop w pid step afterItem bound drained) := by
  unfold workerLoop
  repeat' first
    | (ordinary_head workerIter; refine workerIter_ordinary _ _ _ _ hs ?_)
    | observer_ordinary_leaf
    | ordinary_strict_step

theorem encryptStep_ordinary (checksum : Packet → M Packet) (softirq : M Unit)
    (hc : ∀ pkt, OrdinaryAction (checksum pkt)) (hs : OrdinaryAction softirq) :
    OrdinaryAction (WG.encryptStep checksum softirq) := by
  unfold WG.encryptStep
  repeat' first
    | (ordinary_head WG.encryptPacket; exact encryptPacket_ordinary _ hc _ _)
    | (ordinary_head WG.enqueuePerPeerTx; exact (enqueuePerPeerTx_sameSnapshot _ _).ordinary)
    | observer_ordinary_leaf
    | ordinary_strict_step

theorem encryptIter_ordinary (checksum : Packet → M Packet) (softirq : M Unit) (need : M Bool)
    (hc : ∀ pkt, OrdinaryAction (checksum pkt)) (hs : OrdinaryAction softirq)
    (hn : OrdinaryAction need) : OrdinaryAction (WG.encryptIter checksum softirq need) := by
  unfold WG.encryptIter
  refine workerIter_ordinary _ _ _ _ (encryptStep_ordinary checksum softirq hc hs) ?_
  repeat' first | observer_ordinary_leaf | ordinary_strict_step

theorem txIter_ordinary (pid : PeerId) (need : M Bool) (hn : OrdinaryAction need) :
    OrdinaryAction (WG.txIter pid need) := by
  unfold WG.txIter
  refine workerIter_ordinary _ _ _ _ (txStep_ordinary pid) ?_
  repeat' first | observer_ordinary_leaf | ordinary_strict_step

theorem handshakeReceiveWorker_ordinary (resched : M Unit) (hr : OrdinaryAction resched) :
    OrdinaryAction (WG.handshakeReceiveWorker resched) := by
  exact workerLoop_ordinary _ _ _ _ _ _ receiveStep_ordinary hr

theorem handshakeReceiveWorker_spec (P : Snapshot → Prop) (hp : Stable P)
    (resched : M Unit) (hr : OrdinaryAction resched) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ WG.handshakeReceiveWorker resched
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (handshakeReceiveWorker_ordinary resched hr).wp P hp

macro "env_worker_step" : tactic => `(tactic|
  first
    | (ordinary_head Env.runWorker; refine runWorker_ordinary _ _ ?_)
    | (ordinary_head Leanux.getK; exact getK_sameSnapshot.ordinary)
    | (ordinary_head Leanux.peekUnit; exact (peekUnit_sameSnapshot _).ordinary)
    | (ordinary_head Leanux.resolveUnit; exact (resolveUnit_sameSnapshot _ _ _).ordinary)
    | (ordinary_head Env.condResched; exact (condResched_sameSnapshot _).ordinary)
    | (ordinary_head Env.deliverSent; exact deliverSent_sameSnapshot.ordinary)
    | observer_ordinary_leaf
    | ordinary_strict_step)

end Leanux.Proofs.WG.Keypairs.EnvFrames
