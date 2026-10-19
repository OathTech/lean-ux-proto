import Leanux.Proofs.WG.RetirementSecurity.TxCoverageTraffic
import Leanux.Proofs.WG.RetirementSecurity.OccurrenceTimers

/-! Native key, timer and handshake actor frames for converse TX ownership.
Each passive case reuses its exact packet/queue projection; keepalive enters
the original staging proof. No initialized state premise is postulated here. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxCoverageNative
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open Queues.RxCredits
variable {locals : List TxLocalBatch}

theorem peer_update (pid : PeerId) (f : Peer→Peer)
    (queue : ∀p,(f p).txQueue.all=p.txQueue.all) :
    Preserves (TxCoverage locals) (getPeer pid >>= fun p=>setPeer pid (f p)) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨p,u,c,read,write⟩:=run
  obtain ⟨same,clock,d,device,stored⟩:=Origins.getPeer_return pid w u p a c read
  subst u
  subst c
  cases write
  have transfer : (txLocalItems locals++txPeerItems p).Perm (txLocalItems locals++txPeerItems (f p)) := by
    simp only [txPeerItems,queue]
    exact List.Perm.refl _
  simpa only [replacePeer,device,Option.map_some] using before.exchange device stored (f p) transfer

theorem peer_update_bind (pid : PeerId) (f : Peer→Peer) (tail : Unit→WG.M α)
    (queue : ∀p,(f p).txQueue.all=p.txQueue.all)
    (next : ∀x,Preserves (TxCoverage locals) (tail x)) :
    Preserves (TxCoverage locals) (getPeer pid >>= fun p=>setPeer pid (f p) >>= tail) := by
  simpa only [bind_assoc] using preserves_bind (peer_update pid f queue) next

macro "coverage_native_step" : tactic => `(tactic| first
  | (receive_update_head setPeer; apply peer_update <;> intro p <;> rfl)
  | (receive_update_head Bind.bind
     apply peer_update_bind
     · intro p; rfl
     intro x)
  | (rx_retention_head getPeer; exact getPeer_preserves _ _)
  | (rx_retention_head getDev; exact store getDev_sameWGStore)
  | (rx_retention_head modifyDev; apply modify_device <;> intro d <;> rfl)
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | (rx_retention_head invariant; exact hoare_liftAmbient (AmbientM.invariant _) _)
  | rxstack_preserves_join
  | rx_retention_step)

theorem keepalive (pid : PeerId) : Preserves (TxCoverage locals) (sendKeepalive pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  cases result
  rw [OccurrenceHandshake.keepalive_factor,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨ready,u,c,prepared,tail⟩:=run
  have cells := congrArg Prod.snd ((ProjectedAction.iff_run_ambient _ _ _).mp
    (OccurrenceHandshake.keepalive_prepare_geometry pid) w a ready u c prepared)
  have queues := (ProjectedAction.iff_run_ambient _ _ _).mp
    (OccurrenceHandshake.keepalive_prepare_queues pid) w a ready u c prepared
  have kept := before.cells cells (queueContents_of_exact queues)
  cases ready with
  | false => simp only [Bool.false_eq_true,ite_false] at tail; cases tail; exact kept
  | true => exact kept.staged pid c b tail

theorem peer_get (pid : PeerId) : Preserves (TxCoverage locals) (peerGet pid) :=
  wire (ownership_queues (peerGet_ownership pid)) (peerGet_cryptWire pid)

theorem handshake_zero (pid : PeerId) : Preserves (TxCoverage locals) (handshakeZero pid) :=
  wire (OccurrenceKeys.handshake_zero_queues pid) (OccurrenceKeys.handshake_zero_wire pid)

theorem handshake_clear (pid : PeerId) : Preserves (TxCoverage locals) (handshakeClear pid) :=
  wire (OccurrenceKeys.handshake_clear_queues pid) (OccurrenceKeys.handshake_clear_wire pid)

theorem clear (pid : PeerId) : Preserves (TxCoverage locals) (keypairsClear pid) :=
  wire (OccurrenceKeys.clear_queues pid) (OccurrenceKeys.clear_wire pid)

theorem expire (pid : PeerId) : Preserves (TxCoverage locals) (expireCurrentPeerKeypairs pid) :=
  wire (OccurrenceKeys.expire_queues pid) (OccurrenceKeys.expire_wire pid)

theorem create (owner : Option PeerId) : Preserves (TxCoverage locals) (keypairCreate owner) :=
  wire (OccurrenceKeys.create_queues owner) (OccurrenceKeys.create_wire owner)

theorem rotate (pid : PeerId) (kid : KeypairId) : Preserves (TxCoverage locals) (addNewKeypair pid kid) :=
  wire (OccurrenceKeys.rotate_queues pid kid) (OccurrenceKeys.rotate_wire pid kid)

theorem derive (kid : KeypairId) (initiator : Bool) (chain : List UInt8) : Preserves (TxCoverage locals) (deriveKeys kid initiator chain) :=
  wire (OccurrenceKeys.derive_queues kid initiator chain) (OccurrenceKeys.derive_wire kid initiator chain)

theorem session (pid : PeerId) : Preserves (TxCoverage locals) (beginSession pid) :=
  wire (OccurrenceKeys.session_queues pid) (OccurrenceKeys.session_wire pid)

theorem create_initiation (pid : PeerId) : Preserves (TxCoverage locals) (createInitiation pid) :=
  wire (OccurrenceKeys.create_initiation_queues pid) (OccurrenceKeys.create_initiation_wire pid)

theorem create_response (pid : PeerId) : Preserves (TxCoverage locals) (createResponse pid) :=
  wire (OccurrenceKeys.create_response_queues pid) (OccurrenceKeys.create_response_wire pid)

theorem add_mac (pid : PeerId) (message : List UInt8) : Preserves (TxCoverage locals) (addMacToPacket pid message) :=
  wire (OccurrenceKeys.add_mac_queues pid message) (OccurrenceKeys.add_mac_wire pid message)


private theorem fun_frame {action : WG.M α} (packets : SameView txCryptWire action)
    (queues : SameView handoffTxView action) : Preserves (TxCoverage locals) action := wire queues packets

theorem maintenance (call : MaintenanceCall) : Preserves (TxCoverage locals) call.original := by
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



theorem consume_initiation (message : List UInt8) : Preserves (TxCoverage locals) (consumeInitiation message) :=
  contents_wire (OccurrenceHandshake.consume_initiation_contents message)
    (OccurrenceHandshake.consume_initiation_wire message)

theorem consume_response (message : List UInt8) : Preserves (TxCoverage locals) (consumeResponse message) :=
  contents_wire (OccurrenceHandshake.consume_response_contents message)
    (OccurrenceHandshake.consume_response_wire message)

theorem consume_cookie (message : List UInt8) : Preserves (TxCoverage locals) (cookieMessageConsume message) :=
  contents_wire (OccurrenceHandshake.cookie_consume_contents message)
    (OccurrenceHandshake.cookie_consume_wire message)

theorem send_buffer (pid : PeerId) (message : List UInt8) : Preserves (TxCoverage locals) (sendBufferToPeer pid message) :=
  contents_wire (OccurrenceHandshake.buffer_contents pid message) (OccurrenceHandshake.buffer_wire pid message)

theorem send_response (pid : PeerId) : Preserves (TxCoverage locals) (sendHandshakeResponse pid) :=
  contents_wire (OccurrenceHandshake.send_response_contents pid) (OccurrenceHandshake.send_response_wire pid)

theorem send_initiation (pid : PeerId) : Preserves (TxCoverage locals) (sendHandshakeInitiation pid) :=
  contents_wire (OccurrenceHandshake.send_initiation_contents pid) (OccurrenceHandshake.send_initiation_wire pid)

theorem send_worker (pid : PeerId) : Preserves (TxCoverage locals) (handshakeSendWorker pid) :=
  contents_wire (OccurrenceHandshake.send_worker_contents pid) (OccurrenceHandshake.send_worker_wire pid)

theorem derived (pid : PeerId) : Preserves (TxCoverage locals) (timersSessionDerived pid) :=
  contents_wire (OccurrenceHandshake.derived_contents pid) (OccurrenceHandshake.derived_wire pid)

theorem initiated (pid : PeerId) : Preserves (TxCoverage locals) (timersHandshakeInitiated pid) :=
  contents_wire (OccurrenceHandshake.initiated_contents pid) (OccurrenceHandshake.initiated_wire pid)

end Leanux.Proofs.WG.RetirementSecurity.TxCoverageNative
