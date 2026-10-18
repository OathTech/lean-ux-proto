import Leanux.Proofs.WG.TransmitSecurity.NonceReceiveFrames
import Leanux.Proofs.WG.TransmitSecurity.NonceStagingSafety

/-! Receive confirmation may release staged packets. The observer follows that
native call and preserves every nonce allocation before later receive failure. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Nonce
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

def receiveTailObserved (pid : PeerId) (pkt : RxPacket) (confirmed : Bool) :
    WGPrefix Allocation (Option (List UInt8)) := do
  if ← liftWGPrefix (branch .doneReceivedNew confirmed) then
    liftWGPrefix (timersHandshakeComplete pid .walltimeLastHandshakeData)
    stagingObserved pid
  match ← liftWGPrefix (RxCredits.prepareRest pid pkt) with
  | none => pure none
  | some ready => liftWGPrefix (Packets.rxFinish pid ready)

def consumeObserved (pid : PeerId) (pkt : RxPacket) (ep : Endpoint) :
    WGPrefix Allocation (Option (List UInt8)) := do
  liftWGPrefix (setPeerEndpoint pid ep)
  let confirmed ← liftWGPrefix (receivedWithKeypair pid pkt.keypair)
  receiveTailObserved pid pkt confirmed

theorem receiveTailObserved_erases (pid : PeerId) (pkt : RxPacket) (confirmed : Bool) :
    ErasesStatePrefix (receiveTailObserved pid pkt confirmed)
      (HandshakeSecurity.Confirmation.afterConfirmation pid pkt confirmed) := by
  unfold receiveTailObserved HandshakeSecurity.Confirmation.afterConfirmation
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro newKey
  have tail : ErasesStatePrefix (E := Allocation)
      (do match ← liftWGPrefix (RxCredits.prepareRest pid pkt) with
          | none => pure none
          | some ready => liftWGPrefix (Packets.rxFinish pid ready))
      (do match ← RxCredits.prepareRest pid pkt with
          | none => pure none
          | some ready => Packets.rxFinish pid ready) := by
    apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
    intro ready
    cases ready
    · exact erasesStatePrefix_pure _
    · exact erasesStatePrefix_lift _
  split
  · apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
    intro _
    exact erasesStatePrefix_bind (stagingObserved_erases pid) (fun _ => tail)
  · exact tail

theorem consumeObserved_erases (pid : PeerId) (pkt : RxPacket) (ep : Endpoint) :
    ErasesStatePrefix (consumeObserved pid pkt ep) (consumeDataDone pid pkt ep) := by
  rw [HandshakeSecurity.Confirmation.source]
  unfold consumeObserved
  exact erasesStatePrefix_bind (erasesStatePrefix_lift _) (fun _ =>
    erasesStatePrefix_bind (erasesStatePrefix_lift _) (fun confirmed =>
      receiveTailObserved_erases pid pkt confirmed))

theorem receiveTailObserved_safe (pid : PeerId) (pkt : RxPacket) (confirmed : Bool) :
    StatePrefixPreserves (fun h w _ => Inv (view w) h) List.Nodup
      (receiveTailObserved pid pkt confirmed) := by
  unfold receiveTailObserved
  apply StatePrefixEnsures.bind (Frames.lift_frame (Frames.ambient _))
  intro newKey
  have tail : StatePrefixPreserves (fun h w _ => Inv (view w) h) List.Nodup
      (do match ← liftWGPrefix (RxCredits.prepareRest pid pkt) with
          | none => pure none
          | some ready => liftWGPrefix (Packets.rxFinish pid ready)) := by
    apply StatePrefixEnsures.bind (Frames.lift_frame (Frames.prepare_rest pid pkt))
    intro ready
    cases ready
    · exact StatePrefixEnsures.pure _ (fun _ _ _ hi => hi.nodup) (fun _ _ _ hi => hi)
    · exact Frames.lift_frame (Frames.rx_finish _ _)
  split
  · apply StatePrefixEnsures.bind (Frames.lift_frame (Frames.complete _ _))
    intro _
    exact StatePrefixEnsures.bind (stagingObserved_safe pid) (fun _ => tail)
  · exact tail

theorem consumeObserved_safe (pid : PeerId) (pkt : RxPacket) (ep : Endpoint) :
    StatePrefixPreserves (fun h w _ => Inv (view w) h) List.Nodup
      (consumeObserved pid pkt ep) := by
  unfold consumeObserved
  apply StatePrefixEnsures.bind (Frames.lift_frame (Frames.full
    (Origins.Retaining.setPeerEndpoint_material _ _) (Keypairs.WGFrames.setPeerEndpoint_sameSnapshot _ _)))
  intro _
  apply StatePrefixEnsures.bind (Frames.lift_preserves (Frames.confirm _ _))
  intro confirmed
  exact receiveTailObserved_safe pid pkt confirmed

end Leanux.Proofs.WG.TransmitSecurity.Nonce
