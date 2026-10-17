import Leanux.Proofs.WG.Queues.HandshakeReceiveSlots
import Leanux.Proofs.WG.Origins.ConfiguredCommand
import Leanux.Proofs.WG.AllowedIps.ClearEndpoint

/-! The existing three-slot compatibility invariant through native removal.
Actual deleting releases and recorded work drains retain their source guards;
no historical material or positive-reference premise is added. -/
namespace Leanux.Proofs.WG.CurrentSlots.Removal
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open Queues

private def fieldsOf (s : WGStoreView × (PeerId → Option Peer)) :=
  (s.1.dev.map Device.nextKeypairId,fun pid => (s.2 pid).map slotCell,
    RxCredits.keyWords {dev:=s.1.dev})

private theorem clear_factor (w : WGWorld) : fieldsOf (AllowedIps.clearListView w)=fields w := by
  unfold fieldsOf AllowedIps.clearListView fields RxCredits.keyWords slotCell
  simp only [Option.map_map,Option.map_bind,Option.bind_map,Function.comp_def]

theorem listDel_fields (id : NodeId) : SameView fields (listDel id) :=
  (AllowedIps.listDel_clearListView id).of_factor fieldsOf fields (fun w => (clear_factor w).symm)

private theorem node_fields {action : WG.M α} (same : SameNode action) : SameView fields action :=
  same.of_factor (fun s : WGStoreView => fields {dev:=s.dev}) _ (fun w => by
    unfold fields RxCredits.keyWords
    simp only [nodeView,wgStoreView,nodeDevice,Option.map_map,Option.bind_map,Function.comp_def])

macro "slot_remove_step" : tactic => `(tactic| first
  | (first | rx_retention_head throw | rx_retention_head MonadExceptOf.throw
     apply (hoare_iff_run_ambient _ _ _).mpr
     intro w a result v b hi run
     cases run)
  | slot_traffic_step)

theorem removeByPeer_preserves (pid : PeerId) : Preserves Inv (removeByPeer pid) := by
  rw [←AllowedIps.removeByPeerWithStep_eq]
  unfold AllowedIps.removeByPeerWithStep AllowedIps.removeStep
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head listDel; exact fields_preserves (project := id) (listDel_fields _))
    | (rx_retention_head AllowedIps.removeNodeBody; exact fields_preserves (project := id) (node_fields (removeNodeBody_sameNode _)))
    | slot_remove_step

theorem free_fields : SameView fields WG.free := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  have kept := (hoare_iff_run_ambient _ _ _).mp (AllowedIps.free_storeView (wgStoreView w))
    w a result v b rfl run
  have projected := congrArg fieldsOf kept
  unfold fieldsOf at projected
  unfold fields
  unfold RxCredits.keyWords slotCell at projected ⊢
  simpa only [AllowedIps.clearStoreView,
    AllowedIps.clearStoreProjection,AllowedIps.resetAllowedips,wgStoreView,
    Option.map_map,Option.map_bind,Option.bind_map,Function.comp_def] using projected

theorem makeDead_preserves (pid : PeerId) : Preserves Inv (peerMakeDead pid) := by
  unfold peerMakeDead
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head removeByPeer; exact removeByPeer_preserves _)
    | slot_remove_step

macro "slot_handshake_fields " initial:term : tactic => `(tactic| first
  | (rx_retention_head IndexOwner.peerDeref; exact indexOwner_peerDeref_preserves _ _)
  | (allocation_release_lift_from IndexM
     apply hoare_liftIndex
     intro w d table hi hd
     unfold fields RxCredits.keyWords at hi ⊢
     simpa only [hd,Option.map_some,Option.bind_some] using hi)
  | (rx_retention_head branchExpired; exact (branchExpired_sameWGWorld _ _ _ _).wp (fun w => fields w=$initial))
  | (rx_retention_head generatePublic; exact (generatePublic_sameWGWorld _).wp (fun w => fields w=$initial))
  | (rx_retention_head messageEphemeral; exact (messageEphemeral_sameWGWorld _ _ _ _).wp (fun w => fields w=$initial))
  | (rx_retention_head mixDh; exact (mixDh_sameWGWorld _ _ _ _).wp (fun w => fields w=$initial))
  | (rx_retention_head mixPrecomputedDh; exact (mixPrecomputedDh_sameWGWorld _ _).wp (fun w => fields w=$initial))
  | slot_fields_step $initial)

theorem createInitiation_fields (pid : PeerId) : SameView fields (createInitiation pid) := by
  intro initial
  change Preserves (fun w => fields w=initial) _
  unfold createInitiation
  index_unfold _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain
  simp (config := {zeta := false}) only [branch,hidden,invariant]
  repeat' slot_handshake_fields initial

theorem addMac_fields (pid : PeerId) (msg : List UInt8) : SameView fields (addMacToPacket pid msg) := by
  intro initial
  change Preserves (fun w => fields w=initial) _
  unfold addMacToPacket WG.andM
  simp (config := {zeta := false}) only [branch]
  repeat' slot_handshake_fields initial

private theorem initiated (pid : PeerId) : Preserves Inv (timersHandshakeInitiated pid) := by
  unfold timersHandshakeInitiated modPeerTimerGuard WG.andM
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head discard; apply discard_view_spec id Inv)
    | (rx_retention_head callerJiffies; exact (callerJiffies_sameWGWorld _).wp Inv)
    | (rx_retention_head jitterBelowRekeyTimeout; exact (jitterBelowRekeyTimeout_sameWGWorld _).wp Inv)
    | (rx_retention_head armTimer; exact armTimer_preserves _ _ _ _)
    | (rx_retention_head modPeerTimer; exact modPeerTimer_preserves _ _ _ _)
    | slot_remove_step

theorem sendInitiation_preserves (pid : PeerId) : Preserves Inv (sendHandshakeInitiation pid) := by
  unfold sendHandshakeInitiation
  simp (config := {zeta := false}) only [branch,hiddenClock64,invariant]
  repeat' first
    | (rx_retention_head createInitiation; exact fields_preserves (project := id) (createInitiation_fields _))
    | (rx_retention_head addMacToPacket; exact fields_preserves (project := id) (addMac_fields _ _))
    | (rx_retention_head timersTraversal; exact timersTraversal_preserves _)
    | (rx_retention_head timersAnyAuthenticatedPacketSent; exact delTimer_preserves _ .sendKeepalive)
    | (rx_retention_head timersHandshakeInitiated; exact initiated _)
    | (rx_retention_head sendBufferToPeer; exact (pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeReceiveSlots.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeReceiveSlots.send_slots) _ _)
    | slot_remove_step

theorem queuedClear (pid : PeerId) : Preserves Inv (queuedExpiredZeroKeyMaterial pid) := by
  unfold queuedExpiredZeroKeyMaterial
  exact preserves_bind (handshakeClear_preserves pid) (fun _ =>
    preserves_bind (keypairsClear_preserves pid) (fun _ => peerPut_preserves (some pid)))

theorem handshakeWorker (pid : PeerId) : Preserves Inv (handshakeSendWorker pid) := by
  unfold handshakeSendWorker
  exact preserves_bind (sendInitiation_preserves pid) (fun _ => peerPut_preserves (some pid))

theorem flushedSend (pid : PeerId) : Preserves Inv (runFlushedSendWork pid) := by
  let dequeue : WG.M Unit := do
    modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue.erase pid}
    let p ← getPeer pid
    if !p.handshakePending then invariant "queued work without a pending flag"
    setPeer pid {p with handshakePending := (←getDev).sendWorkQueue.contains pid}
  have unchanged : SameView fields dequeue := by
    intro initial
    unfold dequeue
    change Preserves (fun w => fields w=initial) _
    simp (config := {zeta := false}) only [invariant]
    repeat' slot_fields_step initial
  have factor : runFlushedSendWork pid=(do
      dequeue
      _ ← hidden (.sectionStart .sendWorker)
      handshakeSendWorker pid
      _ ← hidden (.sectionStop .sendWorker)) := by
    have bind_congr {α β : Type} (a : WG.M α) (f g : α → WG.M β)
        (h : ∀ x,f x=g x) : (a >>= f)=(a >>= g) := congrArg (fun k => a >>= k) (funext h)
    simp only [runFlushedSendWork,dequeue,bind_assoc]
    apply bind_congr
    intro _
    apply bind_congr
    intro p
    by_cases h : (!p.handshakePending)=true
    all_goals simp only [h,Bool.false_eq_true,ite_true,ite_false,bind_assoc]
  rw [factor]
  exact preserves_bind (fields_preserves (project := id) unchanged) (fun _ =>
    preserves_bind (hoare_liftAmbient (AmbientM.hidden (.sectionStart .sendWorker)) Inv) (fun _ =>
      preserves_bind (handshakeWorker pid) (fun _ =>
        preserves_bind (hoare_liftAmbient (AmbientM.hidden (.sectionStop .sendWorker)) Inv)
          (fun _ => preserves_pure _))))

theorem flushedClear (pid : PeerId) : Preserves Inv (runFlushedClearWork pid) := by
  unfold runFlushedClearWork
  simp (config := {zeta := false}) only [hidden]
  repeat' first
    | (rx_retention_head queuedExpiredZeroKeyMaterial; exact queuedClear _)
    | slot_remove_step

theorem drain (upTo : Option PeerId) : Preserves Inv (drainHandshakeSendWq upTo) := by
  unfold drainHandshakeSendWq
  simp (config := {zeta := false}) only [Std.Legacy.Range.forIn_eq_forIn_range',peekUnit,resolveUnit,getAmbient,invariant]
  repeat' first
    | (rx_retention_head runFlushedSendWork; exact flushedSend _)
    | (rx_retention_head runFlushedClearWork; exact flushedClear _)
    | slot_remove_step

theorem stopTimers (pid : PeerId) : Preserves Inv (timersStop pid) := by
  unfold timersStop
  repeat' first
    | (rx_retention_head delTimer; exact delTimer_preserves _ _)
    | (rx_retention_head drainHandshakeSendWq; exact drain _)
    | slot_remove_step

theorem afterDead (pid : PeerId) : Preserves Inv (peerRemoveAfterDead pid) := by
  unfold peerRemoveAfterDead
  simp (config := {zeta := false}) only [branch,unsupported,invariant]
  repeat' first
    | (rx_retention_head keypairsClear; exact keypairsClear_preserves _)
    | (rx_retention_head timersStop; exact stopTimers _)
    | (rx_retention_head drainHandshakeSendWq; exact drain _)
    | slot_remove_step

theorem remove (peer : Option PeerId) : Preserves Inv (peerRemove peer) := by
  unfold peerRemove
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head peerMakeDead; exact makeDead_preserves _)
    | (rx_retention_head peerRemoveAfterDead; exact afterDead _)
    | slot_remove_step

theorem removeAll : Preserves Inv peerRemoveAll := by
  unfold peerRemoveAll
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head free; exact fields_preserves (project := id) free_fields)
    | (rx_retention_head peerMakeDead; exact makeDead_preserves _)
    | (rx_retention_head peerRemoveAfterDead; exact afterDead _)
    | slot_remove_step

end Leanux.Proofs.WG.CurrentSlots.Removal
