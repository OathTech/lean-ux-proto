import Leanux.Proofs.WG.TimerDiscipline.HookStateNativeFrames
import Leanux.Proofs.WG.Keypairs.Evolution.Scheduler
import Leanux.Proofs.WG.Index.TimerProductRulesSource
import Leanux.Proofs.WG.TimerDiscipline.HookStateFrames
/-! Concrete ordinary/snapshot contracts for the quiet scheduler leaves. Decrypt publication and the encrypt suffix use their existing exact source cuts; timer dispatch and placeholder traversal reuse TimerProductRules. No successful-run premise is required of callers. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.HookState
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Std.Do
open Keypairs Keypairs.WGFrames Keypairs.WGTransitions Keypairs.WGMore Keypairs.EnvFrames
theorem encryptTail_ordinary (item : Option (List SkbId)) :
    ProductOrdinaryAction (RxWorkers.encryptTailSource item) := by
  have packet (key : KeypairId) (pkt : DataPacket) :
      ProductOrdinaryAction (encryptPacket Env.checksumHelp key pkt) :=
    Keypairs.SchedulerObservers.encryptPacket_ordinary _
      (fun p => Keypairs.SameView.ordinary (checksumHelp_sameSnapshot p)) key pkt
  have step : ProductOrdinaryAction (RxWorkers.encryptStepTailSource item) := by
    apply (ordinaryAction_iff_wp _).mpr
    intro P hp
    let Q := fun w : World => P (snapshot w.wg)
    have ambient {α : Type} (a : AmbientM α) : Preserves Q (monadLift a : Leanux.M α) :=
      productAmbient_spec a Q (fun _ _ hi => hi)
    have read (id : SkbId) : Preserves Q (monadLift (getTxSkb id) : Leanux.M DataPacket) := by
      apply Lifetimes.ProjectedAction.wp (OrdinaryAction.liftWG
        (Keypairs.SameView.ordinary (show SameSnapshot (getTxSkb id) from by snapshot_source [getTxSkb] using []))) P hp
    have write (id : SkbId) (f : DataPacket → DataPacket) :
        Preserves Q (monadLift (setTxSkb id f) : Leanux.M Unit) := by
      apply Lifetimes.ProjectedAction.wp (OrdinaryAction.liftWG
        (Keypairs.SameView.ordinary (show SameSnapshot (setTxSkb id f) from by snapshot_source [setTxSkb] using []))) P hp
    have enqueue (xs : List SkbId) (state : PacketState) :
        Preserves Q (monadLift (enqueuePerPeerTx xs state) : Leanux.M Unit) :=
      Lifetimes.ProjectedAction.wp (OrdinaryAction.liftWG
        (Keypairs.SameView.ordinary (enqueuePerPeerTx_sameSnapshot xs state))) P hp
    have encrypted (key : KeypairId) (pkt : DataPacket) :
        Preserves Q (encryptPacket Env.checksumHelp key pkt) :=
      Lifetimes.ProjectedAction.wp (packet key pkt) P hp
    change Preserves Q (RxWorkers.encryptStepTailSource item)
    routing_tx_source [RxWorkers.encryptStepTailSource] using [read,write,enqueue,encrypted,ambient]
  exact workerIter_ordinary _ _ _ _ step
    (ordinary_bind (Keypairs.SameView.ordinary (condResched_sameSnapshot _))
      (fun _ => Keypairs.SameView.ordinary (fun initial =>
        productAmbient_spec (AmbientM.branch _ _) _ (fun _ _ hi => hi))))

theorem timer_ordinary (worker : Worker) (pid : PeerId) (timer : PeerTimer)
    (wheel : WheelEntry) (prior : Option UInt64) :
    ProductOrdinaryAction (timerDispatchUnit worker pid timer wheel prior) := by
  apply (ordinaryAction_iff_wp _).mpr
  intro P hp
  apply Index.TimerProductRules.dispatch (fun w : World => P (snapshot w.wg))
  · intro α a frame
    exact (store_snapshot a frame).wp P
  · intro w body hb
    exact runTimerSection_kernel_contract w body
      (fun g _ _ _ => P (snapshot g)) (fun g _ _ _ => P (snapshot g)) hb
  · intro p t
    exact (OrdinaryAction.liftWG (timerCallback_ordinary p t)).wp P hp
  · intro p t
    exact (OrdinaryAction.liftWG (Keypairs.SameView.ordinary (delTimer_sameSnapshot p t))).wp P hp
theorem placeholder_ordinary (j : UInt64) :
    ProductOrdinaryAction (RxHistory.placeholderTimerPassSource j) := by
  apply (ordinaryAction_iff_wp _).mpr
  intro P hp
  apply Index.TimerProductRules.placeholder (fun w : World => P (snapshot w.wg))
  · intro α a frame
    exact (store_snapshot a frame).wp P
  · intro w body hb
    exact runTimerSection_kernel_contract w body
      (fun g _ _ _ => P (snapshot g)) (fun g _ _ _ => P (snapshot g)) hb
  · intro p t
    exact (OrdinaryAction.liftWG (timerCallback_ordinary p t)).wp P hp
  · intro p t
    exact (OrdinaryAction.liftWG (Keypairs.SameView.ordinary (delTimer_sameSnapshot p t))).wp P hp
end Leanux.Proofs.WG.TimerDiscipline.HookState
