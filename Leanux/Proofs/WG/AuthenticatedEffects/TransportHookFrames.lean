import Leanux.Proofs.WG.AuthenticatedEffects.TransportCarrierOuter
import Leanux.Proofs.WG.HandshakeSecurity.ResponderStagingSource
import Leanux.Proofs.WG.Packets.PublicationTransmit

/-! Concrete native receive-store frames at the shared driver callbacks. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TransportHookFrames
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues Packets TransportCarrier
set_option maxHeartbeats 600000

theorem selection (pid : PeerId) :
    SameView RxDisposition.nativeRxStore (HandshakeSecurity.Responder.selectionPrefix pid) := by
  unfold HandshakeSecurity.Responder.selectionPrefix
  apply SameView.bind (TransportPublication.getPeer_rx pid)
  intro p
  apply SameView.bind (show SameView RxDisposition.nativeRxStore (branch .stagedEmpty p.staged.isEmpty) from
    fun initial => hoare_liftAmbient (AmbientM.branch .stagedEmpty p.staged.isEmpty) (fun w => RxDisposition.nativeRxStore w = initial))
  intro empty
  split
  · exact SameView.pure _ _
  · apply SameView.bind (TransportPublication.setPeer_rx _ _)
    intro _
    apply SameView.bind
      (((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.keypairGet_geometry) p.keypairCurrent).factor Prod.snd)
    intro kp
    exact SameView.pure _ _

theorem confirmation (pid : PeerId) (kid : KeypairId) :
    SameView RxDisposition.nativeRxStore (receivedWithKeypair pid kid) :=
  ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.received_geometry) pid kid).factor Prod.snd

theorem session (pid : PeerId) : SameView RxDisposition.nativeRxStore (beginSession pid) :=
  PublicationFrontier.beginSession_rx pid

theorem reserve (kid : KeypairId) :
    SameView RxDisposition.nativeRxStore (TransmitSecurity.Nonce.reserveNative kid) := by
  unfold TransmitSecurity.Nonce.reserveNative
  apply SameView.bind
    (((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.readKey) kid).factor Prod.snd)
  intro k
  apply SameView.bind
  · unfold setKeypair
    exact modifyDev_rx _ (fun _ => rfl) (fun _ => rfl)
  · intro _
    exact SameView.pure _ _

theorem allocate (packets : List DataPacket) :
    SameView RxDisposition.nativeRxStore (packets.mapM newTxSkb) :=
  (RxCredits.newTxList_protect packets).factor (fun v => v.2.1)

theorem create (pid : PeerId) (item : List SkbId) :
    SameView RxDisposition.nativeRxStore (createData pid item) :=
  ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.create_geometry) pid item).factor Prod.snd

theorem poll : SameView RxDisposition.nativeRxStore TxRing.pollSource := by
  unfold TxRing.pollSource
  apply SameView.bind (TransportPublication.store_rx _ getDev_sameWGStore)
  intro d
  change SameView RxDisposition.nativeRxStore
    (modifyDev (fun dev => {dev with encryptQueue := d.encryptQueue.consume.2}) >>= fun _ => pure d.encryptQueue.consume.1)
  apply SameView.bind (modifyDev_rx (fun dev => {dev with encryptQueue := d.encryptQueue.consume.2})
    (fun _ => rfl) (fun _ => rfl))
  intro _
  exact SameView.pure _ _

theorem transmit (pid : PeerId) : SameView RxDisposition.nativeRxStore (txStep pid) :=
  ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationTransmit.«0».Leanux.Proofs.WG.PublicationJoint.txStep_geometry) pid).factor Prod.snd

end Leanux.Proofs.WG.AuthenticatedEffects.TransportHookFrames
