import Leanux.Proofs.WG.Queues.RxConsumeProtection
import Leanux.Proofs.Logged.NativeCapture

/-! Confirmation is observed at its native return, before timers, staged sends,
or packet delivery can fail. The source cut reuses campaign 1's receive factors;
it does not assert authentication merely from an arbitrary consume input. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.Confirmation
open Leanux Leanux.WG Leanux.Proofs.Logged
open Queues

structure Receipt where
  peer : PeerId
  packet : RxPacket
  endpoint : Endpoint
  execution : WGRunWitness Bool

def Receipt.Valid (r : Receipt) : Prop :=
  r.execution.Valid (receivedWithKeypair r.peer r.packet.keypair)

def afterConfirmation (pid : PeerId) (pkt : RxPacket) (confirmed : Bool) :
    WG.M (Option (List UInt8)) := do
  if ← branch .doneReceivedNew confirmed then
    timersHandshakeComplete pid .walltimeLastHandshakeData
    sendStagedPackets pid
  match ← RxCredits.prepareRest pid pkt with
  | none => pure none
  | some ready => Packets.rxFinish pid ready

theorem source (pid : PeerId) (pkt : RxPacket) (ep : Endpoint) :
    consumeDataDone pid pkt ep = (do
      setPeerEndpoint pid ep
      let confirmed ← receivedWithKeypair pid pkt.keypair
      afterConfirmation pid pkt confirmed) := by
  rw [Packets.consumeDataDone_factor, RxCredits.rxPrepare_factor]
  simp only [RxCredits.promoteAndSend, afterConfirmation, bind_assoc,
    RxCredits.bind_if_source, pure_bind]
  rfl

def confirmObserved (pid : PeerId) (pkt : RxPacket) (ep : Endpoint) : WGPrefix Receipt Bool :=
  receiptWGObserved (liftWGPrefix (receivedWithKeypair pid pkt.keypair))
    (fun run => ⟨pid, pkt, ep, run⟩)

def observed (pid : PeerId) (pkt : RxPacket) (ep : Endpoint) :
    WGPrefix Receipt (Option (List UInt8)) := do
  liftWGPrefix (setPeerEndpoint pid ep)
  let confirmed ← confirmObserved pid pkt ep
  liftWGPrefix (afterConfirmation pid pkt confirmed)

theorem confirm_erases (pid : PeerId) (pkt : RxPacket) (ep : Endpoint) :
    ErasesStatePrefix (confirmObserved pid pkt ep) (receivedWithKeypair pid pkt.keypair) :=
  receiptWGObserved_erases (erasesStatePrefix_lift _) _

theorem erases (pid : PeerId) (pkt : RxPacket) (ep : Endpoint) :
    ErasesStatePrefix (observed pid pkt ep) (consumeDataDone pid pkt ep) := by
  rw [source]
  unfold observed
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro _
  exact erasesStatePrefix_bind (confirm_erases pid pkt ep) (fun _ => erasesStatePrefix_lift _)

end Leanux.Proofs.WG.HandshakeSecurity.Confirmation
