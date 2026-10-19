import Leanux.Proofs.WG.Keypairs.Evolution.Syscalls
import Leanux.Proofs.WG.Queues.RxWorkerCuts

/-! Native worker cuts preserve replay coherence via the existing keypair
lifetime relation. These frames concern native state, not receipt histories. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.ReplayEntry
open Leanux Leanux.WG Leanux.Proofs.Framing Std.Do
open Lifetimes Queues Keypairs Keypairs.WGFrames Keypairs.WGTransitions
open Keypairs.WGMore Keypairs.WGConfig Keypairs.Observers Keypairs.EnvFrames Keypairs.SchedulerObservers
set_option maxHeartbeats 600000

theorem publish_ordinary (id : SkbId) (state : PacketState) : OrdinaryAction (RxWorkers.publishSource id state) := by
  unfold RxWorkers.publishSource
  repeat' first | observer_ordinary_leaf | ordinary_strict_step

theorem prepare_ordinary : OrdinaryAction RxWorkers.prepareSource := by
  unfold RxWorkers.prepareSource
  repeat' first
    | (ordinary_head RxWorkers.publishSource; exact publish_ordinary _ _)
    | observer_ordinary_leaf
    | ordinary_strict_step

theorem poll_ordinary : OrdinaryAction TxRing.pollSource := by
  unfold TxRing.pollSource
  repeat' first | observer_ordinary_leaf | ordinary_strict_step

theorem encrypt_ordinary (item : Option (List SkbId)) : ProductOrdinaryAction (RxWorkers.encryptStepTailSource item) := by
  apply (ordinaryAction_iff_wp _).mpr
  intro P hp
  have enc (id : KeypairId) (pkt : DataPacket) :=
    ProjectedAction.wp (encryptPacket_ordinary Env.checksumHelp
      (fun packet => SameView.ordinary (checksumHelp_sameSnapshot packet)) id pkt) P hp
  have packetStore (α : Type) (a : WG.SkbM α) :
      ProductOrdinaryAction (MonadLift.monadLift (WG.liftSkb a) : Leanux.M α) := by
    apply OrdinaryAction.liftWG
    apply SameView.ordinary
    intro initial
    apply hoare_liftSkb _ (fun w => snapshot w = initial)
    intro g d store hg hd
    simpa [snapshot,hd] using hg
  have readPacket (id : SkbId) :
      ⦃fun w : World => ⌜P (snapshot w.wg)⌝⦄
        (MonadLift.monadLift (WG.getTxSkb id) : Leanux.M _)
      ⦃⇓? _ w => ⌜P (snapshot w.wg)⌝⦄ :=
    ProjectedAction.wp (packetStore _ _) P hp
  have writePacket (id : SkbId) (f : DataPacket → DataPacket) :
      ⦃fun w : World => ⌜P (snapshot w.wg)⌝⦄
        (MonadLift.monadLift (WG.setTxSkb id f) : Leanux.M _)
      ⦃⇓? _ w => ⌜P (snapshot w.wg)⌝⦄ :=
    ProjectedAction.wp (packetStore _ _) P hp
  have enqueue (xs : List SkbId) (state : PacketState) :
      ⦃fun w : World => ⌜P (snapshot w.wg)⌝⦄
        (MonadLift.monadLift (WG.enqueuePerPeerTx xs state) : Leanux.M _)
      ⦃⇓? _ w => ⌜P (snapshot w.wg)⌝⦄ :=
    ProjectedAction.wp
      (OrdinaryAction.liftWG (SameView.ordinary (enqueuePerPeerTx_sameSnapshot xs state))) P hp
  have ambient := fun α (a : AmbientM α) => productAmbient_spec a
    (fun w => P (snapshot w.wg)) (fun _ _ h => h)
  change Preserves (fun w => P (snapshot w.wg)) (RxWorkers.encryptStepTailSource item)
  unfold RxWorkers.encryptStepTailSource
  apply preserves_bind (ambient _ (AmbientM.branch .encWorkerConsumed item.isSome))
  intro _
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

end Leanux.Proofs.WG.AuthenticatedEffects.ReplayEntry
