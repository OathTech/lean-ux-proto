import Leanux.Proofs.WG.Noise.ConsumeConfirmationSource
import Leanux.Proofs.WG.Origins.HandshakeSources
import Leanux.Proofs.WG.Origins.RetainingLeaves
import Leanux.Proofs.WG.KeyTimes.Receive
import Leanux.Proofs.WG.Index.ReceiveCompletionRulesSource
set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.ReceiveCompletion
open Leanux Leanux.WG Noise Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues Origins.HandshakeSources

theorem prepareRest_preserves_source (P : WGWorld → Prop) (pid : PeerId) (pkt : RxPacket)
    (fresh : Preserves P (keepKeyFreshRx pid))
    (received : Preserves P (timersAnyAuthenticatedPacketReceived pid))
    (traversal : Preserves P (timersTraversal pid))
    (data : Preserves P (timersDataReceived pid))
    (stats : ∀ len, Preserves P (updateRxStats pid len))
    (dishonest : ∀ why, Preserves P (WG.dishonest why))
    (ecn : ∀ protocol ds bytes, Preserves P (inetEcnDecapsulate protocol ds bytes)) :
    Preserves P (RxCredits.prepareRest pid pkt) := by
  apply Rules.to_native
  exact Rules.prepareRest (fun g _=>P g) pid pkt (fun decision value=>Rules.of_native (hoare_liftAmbient (AmbientM.branch decision value) P))
    (Rules.of_native fresh) (Rules.of_native received) (Rules.of_native traversal)
    (Rules.of_native data) (fun len=>Rules.of_native (stats len))
    (fun why=>Rules.of_native (dishonest why))
    (fun protocol ds bytes=>Rules.of_native (ecn protocol ds bytes))

theorem rxFinish_preserves_source (P : WGWorld → Prop) (pid : PeerId) (ready : Packets.RxReady)
    (lookup : Preserves P (RxBorrow.source ready.protocol ready.bytes))
    (dishonest : Preserves P (WG.dishonest .peer))
    (stats : Preserves P (updateRxStats pid (ready.originalLen + MESSAGE_DATA_LEN_0))) :
    Preserves P (Packets.rxFinish pid ready) := by
  apply Rules.to_native
  exact Rules.rxFinish (fun g _=>P g) pid ready (fun decision value=>Rules.of_native (hoare_liftAmbient (AmbientM.branch decision value) P))
    (Rules.of_native lookup) (Rules.of_native dishonest) (Rules.of_native stats)

theorem afterConfirmation_preserves_source (P : WGWorld → Prop)
    (pid : PeerId) (pkt : RxPacket) (confirmed : Bool)
    (complete : Preserves P (timersHandshakeComplete pid .walltimeLastHandshakeData))
    (staged : Preserves P (sendStagedPackets pid))
    (prepare : Preserves P (RxCredits.prepareRest pid pkt))
    (finish : ∀ ready, Preserves P (Packets.rxFinish pid ready)) :
    Preserves P (ConsumeConfirmation.afterConfirmation pid pkt confirmed) := by
  apply Rules.to_native
  exact Rules.afterConfirmation (fun g _=>P g) pid pkt confirmed (fun decision value=>Rules.of_native (hoare_liftAmbient (AmbientM.branch decision value) P))
    (Rules.of_native complete) (Rules.of_native staged) (Rules.of_native prepare)
    (fun ready=>Rules.of_native (finish ready))

theorem keepKeyFreshRx_preserves_source (P : WGWorld → Prop) (pid : PeerId)
    (modify : Preserves P (modifyPeer pid fun p => {p with sentLastminuteHandshake := true}))
    (queued : Preserves P (sendQueuedHandshakeInitiation pid false)) :
    Preserves P (keepKeyFreshRx pid) := by
  apply Rules.to_native
  exact Rules.keepKeyFreshRx (fun g _=>P g) pid (fun decision value=>Rules.of_native (hoare_liftAmbient (AmbientM.branch decision value) P))
    (fun birthday=>Rules.of_native ((branchExpired_sameWGWorld .rxFreshExpired birthday
      (REJECT_AFTER_TIME - KEEPALIVE_TIMEOUT - REKEY_TIMEOUT)).wp P))
    (Rules.of_native modify) (Rules.of_native queued)

theorem dataReceived_preserves_source (P : WGWorld → Prop) (pid : PeerId)
    (arm : Preserves P (modPeerTimer .timerJiffiesDataReceived pid .sendKeepalive KEEPALIVE_TIMEOUT_TICKS))
    (update : Preserves P (modifyPeer pid fun p => {p with timerNeedAnotherKeepalive := true})) :
    Preserves P (timersDataReceived pid) := by
  apply Rules.to_native
  exact Rules.dataReceived (fun g _=>P g) pid (fun decision value=>Rules.of_native (hoare_liftAmbient (AmbientM.branch decision value) P))
    (Rules.of_native arm) (Rules.of_native update)

end Leanux.Proofs.WG.Index.ReceiveCompletion
