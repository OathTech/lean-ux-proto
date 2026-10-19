import Leanux.Proofs.WG.TransmitSecurity.StagedReceiveFrames
import Leanux.Proofs.WG.TransmitSecurity.StagedHandshakeTransport
import Leanux.Proofs.WG.AuthenticatedEffects.CausalCallbackQuietPackets
import Leanux.Proofs.WG.AuthenticatedEffects.CausalReceiptNativeCallbacks

/-! The actual receive completion retains staged provenance through promotion,
response-triggered staging and subsequent receive maintenance. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open AuthenticatedEffects AuthenticatedEffects.CausalJournal
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

theorem prepare_observed (pid : PeerId) (packet : RxPacket) :
    StateSafe (PacketEffects.prepareWith effects pid packet) :=
  state_history (Driver.effects_prepare_history effects_history pid packet)
    (PacketEffects.prepare_erases (CausalEffects.ops_erases scope? Event.armed Event.queued) pid packet)
    (fun _ => Native.prepare pid packet)

theorem prepare_disposal (pid : PeerId) (packet : RxPacket) :
    StateSafe (HandshakeSecurity.StagedDisposal.PacketSource.prepareWith effects hooks.peerRelease pid packet) := by
  have quiet := CallbackQuiet.prepare selection? (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) pid packet
  exact state_quiet quiet.1 quiet.2
    (RetirementSecurity.NestedPeerRelease.projects_erases selection?
      (CallbackQuiet.prepare_projects selection? (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) pid packet)
      (erasesStatePrefix_lift _)) (fun _ => Native.prepare pid packet)

theorem receive_finish (pid : PeerId) (ready : Packets.RxReady) :
    StateSafe (RetirementSecurity.NestedPeerRelease.rxFinishWith (Driver.nestedOps hooks) pid ready) := by
  have quiet := CallbackFrames.rx_finish_quiet selection? (fun _ => rfl) pid ready
  exact state_quiet quiet.1 quiet.2 (CallbackFrames.rx_finish_erases pid ready)
    (fun _ => Native.receive_finish pid ready)

theorem receive_tail (pid : PeerId) (packet : RxPacket) (confirmed : Bool) :
    StateSafe (Driver.receiveTailObserved hooks pid packet confirmed) := by
  unfold Driver.receiveTailObserved
  repeat' first
    | (staged_origin_head Driver.stagingObserved; exact staging_observed _)
    | (staged_origin_head HandshakeSecurity.StagedDisposal.PacketSource.prepareWith; exact prepare_disposal _ _)
    | (staged_origin_head RetirementSecurity.NestedPeerRelease.rxFinishWith; exact receive_finish _ _)
    | (staged_origin_head liftWGPrefix
       apply state_lift; intro history
       repeat' first
         | (rx_retention_head Packets.rxFinish; exact Native.receive_finish _ _)
         | staged_origin_native
       done)
    | staged_origin_step

theorem consume_observed (pid : PeerId) (packet : RxPacket) (endpoint : Endpoint) :
    StateSafe (Driver.consumeObserved hooks pid packet endpoint) := by
  unfold Driver.consumeObserved
  exact state_bind (state_lift _ (fun _ => Native.endpoint pid endpoint)) (fun _ =>
    state_bind (confirmation_observed pid packet.keypair) (receive_tail pid packet))

end Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
