import Leanux.Proofs.WG.Packets.PublicationPeerRemoval
import Leanux.Proofs.WG.Origins.ConfiguredMaintenance
import Leanux.Proofs.WG.Peers.ConfiguredTimers

/-! Native timer cancellation and queued key clearing retain publication
anchors and the epoch-scoped packet peer frontier. Successful endpoints alone
are asserted; absent peers, failed records and reference errors remain Stops. -/
namespace Leanux.Proofs.WG.PublicationFrontier
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues PublicationCompletion

private theorem keypairsClear_geometry (pid : PeerId) :
    SameView OwnerCompletion.geometry (keypairsClear pid) := by
  intro initial
  change Preserves (fun w => OwnerCompletion.geometry w = initial) _
  unfold keypairsClear
  index_unfold _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer
  repeat' completion_step initial

private theorem handshakeClear_geometry (pid : PeerId) :
    SameView OwnerCompletion.geometry (handshakeClear pid) := by
  intro initial
  change Preserves (fun w => OwnerCompletion.geometry w = initial) _
  unfold handshakeClear handshakeZero
  repeat' first
    | (first | allocation_release_head liftIndex | allocation_release_lift_from IndexM
       apply hoare_liftIndex
       intro w d table hi hd
       simpa only [OwnerCompletion.geometry,RxCredits.rxView,hd,Option.map_some,
         Option.bind_some] using hi)
    | completion_step initial

theorem keypairsClear_preserves (pid : PeerId) (history : List RxHistory.Event) :
    Preserves (Inv history) (keypairsClear pid) :=
  preserves_of_configured _ ((keypairsClear_geometry pid).factor Prod.snd)
    (ConfiguredMaintenance.keypairsClear_view pid) history

theorem handshakeClear_preserves (pid : PeerId) (history : List RxHistory.Event) :
    Preserves (Inv history) (handshakeClear pid) :=
  preserves_of_configured _ ((handshakeClear_geometry pid).factor Prod.snd)
    (ConfiguredMaintenance.handshakeClear_view pid) history

theorem delTimer_preserves (pid : PeerId) (timer : PeerTimer)
    (history : List RxHistory.Event) : Preserves (Inv history) (delTimer pid timer) :=
  preserves_of_configured _
    (((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.del_geometry) pid timer).factor Prod.snd)
    (ConfiguredIdentity.delTimer_view pid timer) history

macro "publication_removal_step " history:term : tactic => `(tactic| first
  | (rx_retention_head getDev; exact store_preserves getDev_sameWGStore $history)
  | (rx_retention_head getPeer
     apply (hoare_iff_run_ambient _ _ _).mpr
     intro w ambient result v finalAmbient hi hr
     have same := (Queues.getPeer_normal _ _ _ _ _ _ hr).1
     simpa only [same] using hi)
  | (rx_retention_head modifyDev
     apply modifyDev_preserves _ ?_ ?_ ?_ ?_ $history
     all_goals intros; rfl)
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | (rx_retention_head ForIn.forIn
     apply list_view_spec id (Inv $history)
     intro x b
     change Preserves (Inv $history) _)
  | (first | rx_retention_head throw | rx_retention_head MonadExceptOf.throw
     apply (hoare_iff_run_ambient _ _ _).mpr
     intro w ambient result v finalAmbient hi hr
     cases hr)
  | rx_retention_step)

theorem queuedExpiredZeroKeyMaterial_preserves (pid : PeerId)
    (history : List RxHistory.Event) :
    Preserves (Inv history) (queuedExpiredZeroKeyMaterial pid) := by
  unfold queuedExpiredZeroKeyMaterial
  exact preserves_bind (handshakeClear_preserves pid history) (fun _ =>
    preserves_bind (keypairsClear_preserves pid history) (fun _ =>
      peerPut_preserves (some pid) history))

theorem expiredZeroKeyMaterial_preserves (pid : PeerId)
    (history : List RxHistory.Event) :
    Preserves (Inv history) (expiredZeroKeyMaterial pid) := by
  unfold expiredZeroKeyMaterial
  simp (config := {zeta := false}) only [branch,peekQueuedUnit,recordQueued]
  repeat' first
    | (rx_retention_head peerGet; exact peerGet_preserves _ history)
    | (rx_retention_head peerPut; exact peerPut_preserves _ history)
    | publication_removal_step history

theorem runFlushedClearWork_preserves (pid : PeerId)
    (history : List RxHistory.Event) :
    Preserves (Inv history) (runFlushedClearWork pid) := by
  unfold runFlushedClearWork
  simp (config := {zeta := false}) only [hidden]
  repeat' first
    | (rx_retention_head queuedExpiredZeroKeyMaterial
       exact queuedExpiredZeroKeyMaterial_preserves _ history)
    | publication_removal_step history

end Leanux.Proofs.WG.PublicationFrontier
