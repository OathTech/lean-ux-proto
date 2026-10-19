import Leanux.Proofs.WG.TransmitSecurity.BatchNativeContents

/-! Native timer, endpoint and work-queue maintenance preserves the batch
projection through its existing independent packet and peer-queue frames. -/
namespace Leanux.Proofs.WG.TransmitSecurity.BatchCoherence.Native
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open RetirementSecurity Queues.RxCredits

private theorem fun_frame {action : WG.M α} (packets : SameView txCryptWire action)
    (queues : SameView handoffTxView action) : Preserves Inv action := wire queues packets

theorem maintenance (call : MaintenanceCall) : Preserves Inv call.original := by
  cases call with
  | cache pid =>
    exact fun_frame
      ((pinned_const _private.Leanux.Proofs.WG.RetirementSecurity.TxCryptSocketFrames.«0».Leanux.Proofs.WG.RetirementSecurity.dstCacheReset_cryptWire) pid)
      (ownership_queues ((pinned_const _private.Leanux.Proofs.WG.RetirementSecurity.OwnershipSocketFrames.«0».Leanux.Proofs.WG.RetirementSecurity.dstCacheReset_ownership) pid))
  | endpoint pid e =>
    exact fun_frame (endpoint_cryptWire pid e) (ownership_queues (endpoint_ownership pid e))
  | arm pid timer delay clock =>
    exact fun_frame (armTimer_cryptWire pid timer delay clock)
      (ownership_queues (armTimer_ownership pid timer delay clock))
  | deleteTimer pid timer =>
    exact fun_frame (delTimer_cryptWire pid timer) (ownership_queues (delTimer_ownership pid timer))
  | guard pid =>
    exact fun_frame (modPeerTimerGuard_cryptWire pid) (ownership_queues (modPeerTimerGuard_ownership pid))
  | modifyTimer site pid timer delay =>
    exact fun_frame (modPeerTimer_cryptWire site pid timer delay)
      (ownership_queues (modPeerTimer_ownership site pid timer delay))
  | handshakeComplete pid site =>
    exact fun_frame (handshakeComplete_cryptWire pid site) (ownership_queues (handshakeComplete_ownership pid site))
  | authenticatedReceived pid =>
    exact fun_frame (delTimer_cryptWire pid .newHandshake) (ownership_queues (delTimer_ownership pid .newHandshake))
  | dataReceived pid =>
    exact fun_frame (dataReceived_cryptWire pid) (ownership_queues (dataReceived_ownership pid))
  | traversal pid =>
    exact fun_frame (timersTraversal_cryptWire pid) (ownership_queues (timersTraversal_ownership pid))
  | queuedHandshake pid retry =>
    exact fun_frame (sendQueued_cryptWire pid retry) (ownership_queues (sendQueued_ownership pid retry))
  | keyFresh pid =>
    exact fun_frame (freshRx_cryptWire pid) (ownership_queues (freshRx_ownership pid))


theorem maintenance_coherent (call : MaintenanceCall) :
    Preserves (Coherent locals active) call.original :=
  coherent_join (OccurrenceTimers.maintenance call) (maintenance call)

end Leanux.Proofs.WG.TransmitSecurity.BatchCoherence.Native
