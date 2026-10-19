import Leanux.Proofs.WG.AuthenticatedEffects.CausalScopeStaging

/-! The actual authenticated consumer and stack reply path restore the incoming
scope stack. Native replay eligibility and stack-input origins remain separate. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.ScopeBalance
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity Queues Lifetimes
open HandshakeSecurity.Confirmation.Poll
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

theorem fresh_receive (pid : PeerId) : StateSafe (HandshakeSecurity.StagedDisposal.PacketSource.freshReceiveWith effects hooks.peerRelease pid) := by
  unfold HandshakeSecurity.StagedDisposal.PacketSource.freshReceiveWith
  repeat' first
    | (scope_balance_head HandshakeSecurity.StagedDisposal.Effects.queuedWith; exact restore_queued _ _)
    | scope_effect_step

theorem prepare (pid : PeerId) (packet : RxPacket) : StateSafe (HandshakeSecurity.StagedDisposal.PacketSource.prepareWith effects hooks.peerRelease pid packet) := by
  unfold HandshakeSecurity.StagedDisposal.PacketSource.prepareWith
  repeat' first
    | (scope_balance_head HandshakeSecurity.StagedDisposal.PacketSource.freshReceiveWith; exact fresh_receive _)
    | (scope_balance_head TimerEffects.traversalWith; exact traversal _)
    | (scope_balance_head TimerEffects.dataReceivedWith; exact data_received _)
    | scope_effect_step

theorem rx_finish (pid : PeerId) (ready : Packets.RxReady) :
    StateSafe (RetirementSecurity.NestedPeerRelease.rxFinishWith (Driver.nestedOps hooks) pid ready) := by
  unfold RetirementSecurity.NestedPeerRelease.rxFinishWith RetirementSecurity.NestedPeerRelease.rxAfterLookupWith
  simp only [Driver.nestedOps]
  repeat' first
    | (scope_balance_head Driver.Hooks.peerRelease; exact peer_release _)
    | scope_state_step

theorem receive_tail (pid : PeerId) (packet : RxPacket) (confirmed : Bool) :
    StateSafe (Driver.receiveTailObserved hooks pid packet confirmed) := by
  unfold Driver.receiveTailObserved
  repeat' first
    | (scope_balance_head RetirementSecurity.NestedPeerRelease.rxFinishWith; exact rx_finish _ _)
    | (scope_balance_head HandshakeSecurity.StagedDisposal.PacketSource.prepareWith; exact prepare _ _)
    | (scope_balance_head Driver.stagingObserved; exact staging _)
    | scope_state_step

theorem consume (pid : PeerId) (packet : RxPacket) (endpoint : Endpoint) :
    StateSafe (Driver.consumeObserved hooks pid packet endpoint) := by
  unfold Driver.consumeObserved
  repeat' first
    | (scope_balance_head Driver.receiveTailObserved; exact receive_tail _ _ _)
    | (scope_balance_head Driver.Hooks.confirmation; exact old_state _)
    | scope_state_step

private theorem reply (dst : Nat) (bytes : List UInt8) : ProductSafe
    (reply4With (fun family addr packets mtu => liftWGObserver
      (Driver.transmitObserved hooks family addr packets mtu)) dst bytes) := by
  unfold reply4With
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (scope_balance_head Driver.transmitObserved; exact product_state _ (transmit_front _ _ _ _))
    | scope_product_step

private theorem receive4 (bytes : List UInt8) : ProductSafe
    (receive4With (reply4With (fun family addr packets mtu => liftWGObserver
      (Driver.transmitObserved hooks family addr packets mtu))) bytes) := by
  intro frames
  exact receive4With_preserves (I := fun h _ => CausalScope.stack (h.filterMap scope?) = .ok frames)
    (S := CausalScope.WellFormed scope?) (fun _ _ ready => ⟨frames,ready⟩)
    (fun _ _ _ _ ready => ready) _ (fun dst bytes => reply dst bytes frames) bytes

theorem stack_input (bytes : List UInt8) : ProductSafe (Driver.stackObserved hooks bytes) := by
  unfold Driver.stackObserved stackReceiveWith
  repeat' first
    | (scope_balance_head receive4With; exact receive4 _)
    | scope_product_step

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.ScopeBalance
