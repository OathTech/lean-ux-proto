import Leanux.Proofs.WG.AuthenticatedEffects.CausalCoverageEffects

/-! Native consume and stack reply callbacks require their real caller scope.
Neither arbitrary packet bytes nor a receive-candidate label supplies
authentication; the poll's certified replay theorem supplies that later join. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Coverage
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity Queues Lifetimes
open HandshakeSecurity.Confirmation.Poll
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

theorem fresh_receive (pid : PeerId) (live : frames ≠ []) :
    StateAt frames (HandshakeSecurity.StagedDisposal.PacketSource.freshReceiveWith effects hooks.peerRelease pid) := by
  unfold HandshakeSecurity.StagedDisposal.PacketSource.freshReceiveWith
  repeat' first
    | (coverage_head HandshakeSecurity.StagedDisposal.Effects.queuedWith; exact restore_queued _ _ live)
    | coverage_effect_step live

theorem prepare_packet (pid : PeerId) (packet : RxPacket) (live : frames ≠ []) :
    StateAt frames (HandshakeSecurity.StagedDisposal.PacketSource.prepareWith effects hooks.peerRelease pid packet) := by
  unfold HandshakeSecurity.StagedDisposal.PacketSource.prepareWith
  repeat' first
    | (coverage_head HandshakeSecurity.StagedDisposal.PacketSource.freshReceiveWith; exact fresh_receive _ live)
    | (coverage_head TimerEffects.traversalWith; exact traversal _ live)
    | (coverage_head TimerEffects.dataReceivedWith; exact data_received _ live)
    | coverage_effect_step live

theorem rx_finish (pid : PeerId) (ready : Packets.RxReady) :
    StateAt frames (RetirementSecurity.NestedPeerRelease.rxFinishWith (Driver.nestedOps hooks) pid ready) := by
  unfold RetirementSecurity.NestedPeerRelease.rxFinishWith RetirementSecurity.NestedPeerRelease.rxAfterLookupWith
  simp only [Driver.nestedOps]
  repeat' first
    | (coverage_head Driver.Hooks.peerRelease; exact peer_release _)
    | coverage_state_step

theorem receive_tail (pid : PeerId) (packet : RxPacket) (confirmed : Bool) (live : frames ≠ []) :
    StateAt frames (Driver.receiveTailObserved hooks pid packet confirmed) := by
  unfold Driver.receiveTailObserved
  repeat' first
    | (coverage_head RetirementSecurity.NestedPeerRelease.rxFinishWith; exact rx_finish _ _)
    | (coverage_head HandshakeSecurity.StagedDisposal.PacketSource.prepareWith; exact prepare_packet _ _ live)
    | (coverage_head Driver.stagingObserved; exact staging _ live)
    | coverage_state_step

theorem consume (pid : PeerId) (packet : RxPacket) (endpoint : Endpoint) (live : frames ≠ []) :
    StateAt frames (Driver.consumeObserved hooks pid packet endpoint) := by
  unfold Driver.consumeObserved
  repeat' first
    | (coverage_head Driver.receiveTailObserved; exact receive_tail _ _ _ live)
    | (coverage_head Driver.Hooks.confirmation; exact old_state _ live)
    | coverage_state_step

private theorem reply (dst : Nat) (bytes : List UInt8) (live : frames ≠ []) : ProductAt frames
    (reply4With (fun family addr packets mtu => liftWGObserver
      (Driver.transmitObserved hooks family addr packets mtu)) dst bytes) := by
  unfold reply4With
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (coverage_head Driver.transmitObserved; exact product_state _ (transmit_front _ _ _ _ live))
    | coverage_product_step

private theorem receive4 (bytes : List UInt8) (live : frames ≠ []) : ProductAt frames
    (receive4With (reply4With (fun family addr packets mtu => liftWGObserver
      (Driver.transmitObserved hooks family addr packets mtu))) bytes) :=
  receive4With_preserves (I := fun h _ => Inv frames h) (S := Safe) (fun _ _ ready => ready.1)
    (fun _ _ _ _ ready => ready) _ (fun dst bytes => reply dst bytes live) bytes

theorem stack_input (bytes : List UInt8) (live : frames ≠ []) :
    ProductAt frames (Driver.stackObserved hooks bytes) := by
  unfold Driver.stackObserved stackReceiveWith
  repeat' first
    | (coverage_head receive4With; exact receive4 _ live)
    | coverage_product_step

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Coverage
