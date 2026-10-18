import Leanux.Proofs.WG.HandshakeSecurity.ResponderHandshakeHistory
import Leanux.Proofs.WG.Queues.SlotTimers

namespace Leanux.Proofs.WG.HandshakeSecurity.Responder
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues Queues.RxCredits Origins Origins.Retaining

theorem native_join {a : WG.M α} (authorization : Preserves (Authorized confirmed) a)
    (bounded : Preserves CurrentSlots.Inv a) : Preserves (History.Native confirmed) a := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w amb result v b entry run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp authorization w amb result v b entry.1 run,
    (hoare_iff_run_ambient _ _ _).mp bounded w amb result v b entry.2 run⟩

theorem sendView_native {a : WG.M α} (frame : SameView sendView a)
    (bounded : Preserves CurrentSlots.Inv a) (confirmed : List Nat) :
    Preserves (History.Native confirmed) a :=
  native_join (sendView_authorized frame confirmed) bounded

theorem peerGet_native (pid : PeerId) (confirmed : List Nat) :
    Preserves (History.Native confirmed) (peerGet pid) :=
  native_fields (pool_of_material (peerGet_material pid)) (CurrentSlots.peerGet_fields pid) confirmed

theorem queued_native (pid : PeerId) (retry : Bool) (confirmed : List Nat) :
    Preserves (History.Native confirmed) (sendQueuedHandshakeInitiation pid retry) :=
  native_join (authorization_of_frames (queued_core pid retry) (queued_keyEffect pid retry) confirmed)
    (CurrentSlots.sendQueuedHandshakeInitiation_preserves pid retry)

theorem keepalive_native (pid : PeerId) (confirmed : List Nat) :
    Preserves (History.Native confirmed) (sendKeepalive pid) :=
  native_join (keepalive_authorized pid confirmed)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeReceiveSlots.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeReceiveSlots.keepalive_slots) pid)

theorem delTimer_native (pid : PeerId) (timer : PeerTimer) (confirmed : List Nat) :
    Preserves (History.Native confirmed) (delTimer pid timer) :=
  sendView_native ((pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.delTimer_view) pid timer)
    (CurrentSlots.delTimer_preserves pid timer) confirmed

theorem modTimer_native (site : HiddenSite) (pid : PeerId) (timer : PeerTimer)
    (delay : Nat) (confirmed : List Nat) :
    Preserves (History.Native confirmed) (modPeerTimer site pid timer delay) :=
  sendView_native ((pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.modPeerTimer_view) site pid timer delay)
    (CurrentSlots.modPeerTimer_preserves site pid timer delay) confirmed

theorem clearEndpoint_native (pid : PeerId) (confirmed : List Nat) :
    Preserves (History.Native confirmed) (clearPeerEndpointSrc pid) := by
  unfold clearPeerEndpointSrc dstCacheResetNow
  repeat' first
    | (rx_retention_head dstCacheReset
       exact sendView_native ((pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.dstCacheReset_view) _)
         (CurrentSlots.fields_preserves (project := id) (CurrentSlots.dstCacheReset_fields _)) confirmed)
    | responder_handshake_step confirmed

theorem purge_native (pid : PeerId) (confirmed : List Nat) :
    Preserves (History.Native confirmed) (purgeStagedPackets pid) := by
  apply native_fields (pool_of_material (purgeStagedPackets_material pid))
  intro initial
  change Preserves (fun w => CurrentSlots.fields w = initial) _
  unfold purgeStagedPackets
  repeat' slot_fields_step initial

theorem handshakeClear_native (pid : PeerId) (confirmed : List Nat) :
    Preserves (History.Native confirmed) (handshakeClear pid) := by
  unfold handshakeClear handshakeZero
  repeat' responder_handshake_step confirmed

theorem keypairsClear_native (H1 : H1ResponderCurrentEdges) (pid : PeerId)
    (confirmed : List Nat) : Preserves (History.Native confirmed) (keypairsClear pid) := by
  apply native_join
  · apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b entry run
    cases result
    exact clear_authorized H1 pid confirmed w v a b entry run
  · exact CurrentSlots.keypairsClear_preserves pid

theorem sendInitiation_native (pid : PeerId) (confirmed : List Nat) :
    Preserves (History.Native confirmed) (sendHandshakeInitiation pid) :=
  sendView_native ((pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.sendHandshakeInitiation_view) pid)
    (CurrentSlots.Removal.sendInitiation_preserves pid) confirmed

theorem sendWorker_native (pid : PeerId) (confirmed : List Nat) :
    Preserves (History.Native confirmed) (handshakeSendWorker pid) := by
  unfold handshakeSendWorker
  exact preserves_bind (sendInitiation_native pid confirmed) (fun _ => peerPut_native (some pid) confirmed)

theorem clearWorker_native (H1 : H1ResponderCurrentEdges) (pid : PeerId) (confirmed : List Nat) :
    Preserves (History.Native confirmed) (queuedExpiredZeroKeyMaterial pid) := by
  unfold queuedExpiredZeroKeyMaterial
  exact preserves_bind (handshakeClear_native pid confirmed) (fun _ =>
    preserves_bind (keypairsClear_native H1 pid confirmed) (fun _ => peerPut_native (some pid) confirmed))

macro "responder_timer_step " confirmed:term : tactic => `(tactic| first
  | (rx_retention_head clearPeerEndpointSrc; exact clearEndpoint_native _ $confirmed)
  | (rx_retention_head purgeStagedPackets; exact purge_native _ $confirmed)
  | (rx_retention_head sendKeepalive; exact keepalive_native _ $confirmed)
  | (rx_retention_head sendQueuedHandshakeInitiation; exact queued_native _ _ $confirmed)
  | (rx_retention_head peerGet; exact peerGet_native _ $confirmed)
  | (rx_retention_head delTimer; exact delTimer_native _ _ $confirmed)
  | (rx_retention_head modPeerTimer; exact modTimer_native _ _ _ _ $confirmed)
  | responder_handshake_step $confirmed)

theorem timerCallback_native (pid : PeerId) (timer : PeerTimer) (confirmed : List Nat) :
    Preserves (History.Native confirmed) (timerCallback pid timer) := by
  cases timer <;> simp only [timerCallback]
  all_goals first
    | unfold expiredRetransmitHandshake
    | unfold expiredSendKeepalive
    | unfold expiredNewHandshake
    | unfold expiredZeroKeyMaterial
    | unfold expiredSendPersistentKeepalive
  all_goals try simp (config := {zeta := false}) only
    [branch, branchCmp, peekQueuedUnit, recordQueued, Functor.discard, map_const, Function.comp_def, map_eq_pure_bind]
  all_goals repeat' responder_timer_step confirmed

end Leanux.Proofs.WG.HandshakeSecurity.Responder
