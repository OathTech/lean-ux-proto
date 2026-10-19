import Leanux.Proofs.WG.RetirementSecurity.TxWorkTimers

/-! Native timer callbacks preserve active and suspended TX service. The
source's clear-work bookkeeping is separate from outstanding TX ownership. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits
namespace TxSuspension

theorem clear_endpoint (pid : PeerId) : Keeps (clearPeerEndpointSrc pid) := by
  suspension_source [clearPeerEndpointSrc,dstCacheResetNow] using [peer,set_peer,cache_reset]

theorem purge (pid : PeerId) : Keeps (purgeStagedPackets pid) := by
  suspension_source [purgeStagedPackets] using [peer,set_peer,modify_device]

theorem timer_callback (pid : PeerId) (kind : PeerTimer) : Keeps (timerCallback pid kind) := by
  cases kind
  all_goals
    unfold timerCallback
    suspension_source [expiredRetransmitHandshake,expiredSendKeepalive,expiredNewHandshake,
      expiredZeroKeyMaterial,expiredSendPersistentKeepalive] using [peer,set_peer,branch,compare,delete,purge,
      timer,clear_endpoint,queued_handshake,keepalive,peer_get,device,peek_queued,peer_put,record_queued,modify_device]

end TxSuspension
namespace TxWork

theorem callback_actor (pid : PeerId) (kind : PeerTimer) :
    Preserves (At (Covered locals crypt) crypt active) (liftWG (timerCallback pid kind)) :=
  At.native (fun _=>serving_callback pid kind) (TxSuspension.timer_callback pid kind)

theorem keepalive_actor (pid : PeerId) : Preserves (At (Covered locals crypt) crypt active) (liftWG (sendKeepalive pid)) :=
  At.native (fun _=>serving_keepalive pid) (TxSuspension.keepalive pid)

theorem serving_queued_zero (pid : PeerId) : Preserves (Serving locals crypt tx) (queuedExpiredZeroKeyMaterial pid) := by
  apply serving_join
  · unfold queuedExpiredZeroKeyMaterial
    apply preserves_bind (passive (OccurrenceKeys.handshake_clear_wire pid)
      (OccurrenceKeys.handshake_clear_queues pid) (handshake_clear_work pid))
    intro _
    apply preserves_bind (passive (OccurrenceKeys.clear_wire pid) (OccurrenceKeys.clear_queues pid) (clear_work pid))
    intro _
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b before run
    cases result
    exact before.peer_put (some pid) a b run
  · exact TxCovered.join (OccurrenceTimers.queued_zero pid) (TxCoverageDeferred.queued_zero pid)

theorem clear_worker_actor (pid : PeerId) :
    Preserves (At (Covered locals crypt) crypt active) (liftWG (queuedExpiredZeroKeyMaterial pid)) :=
  At.native (fun _=>serving_queued_zero pid) (TxSuspension.clear_worker pid)

end TxWork
end Leanux.Proofs.WG.RetirementSecurity
