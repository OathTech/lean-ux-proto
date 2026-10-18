import Leanux.Proofs.WG.Index.ReceiveCoreFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.ReceiveCompletion
open Leanux Leanux.WG Noise Std.Do Leanux.Proofs.Framing Lifetimes Queues

theorem ready_join {α : Type} (action : WG.M α)
    (slots : Preserves CurrentSlots.Inv action) (core : Preserves Reached.Core action) :
    Preserves TimerCore.Ready action :=
  (ensures_iff _ _ _).mp (TimerCore.ready_of_core action slots ((ensures_iff _ _ _).mpr core))

theorem fresh_ready (pid : PeerId) : Preserves TimerCore.Ready (keepKeyFreshRx pid) :=
  ready_join _ (CurrentSlots.keepKeyFreshRx_preserves pid)
    (keepKeyFreshRx_preserves_source _ pid
      (ConfigurationIndex.frame_core (ConfigurationIndex.modifyPeer_fields _ _ (fun _=>rfl)))
      ((ensures_iff _ _ _).mp (TimerCore.queued_core pid false)))

theorem data_ready (pid : PeerId) : Preserves TimerCore.Ready (timersDataReceived pid) :=
  dataReceived_preserves_source _ pid
    ((ensures_iff _ _ _).mp (TimerCore.arm .timerJiffiesDataReceived pid .sendKeepalive KEEPALIVE_TIMEOUT_TICKS))
    ((ensures_iff _ _ _).mp (TimerCore.update pid _ (fun _=>rfl) (fun _=>rfl)))

theorem stats_ready (pid : PeerId) (len : Nat) : Preserves TimerCore.Ready (updateRxStats pid len) :=
  ready_join _
    (CurrentSlots.fields_preserves (project:=id)
      ((pinned_const _private.Leanux.Proofs.WG.Queues.CurrentSlotCompletion.«0».Leanux.Proofs.WG.CurrentSlots.stats_fields) pid len))
    (ConfigurationIndex.frame_core (stats_fields pid len))

theorem dishonest_ready (why : Dishonest) : Preserves TimerCore.Ready (WG.dishonest why) :=
  ready_join _
    ((pinned_const _private.Leanux.Proofs.WG.Queues.CurrentSlotCompletion.«0».Leanux.Proofs.WG.CurrentSlots.dishonest_preserves) why)
    (ConfigurationIndex.frame_core (dishonest_fields why))

theorem prepare_ready (pid : PeerId) (pkt : RxPacket) :
    Preserves TimerCore.Ready (RxCredits.prepareRest pid pkt) :=
  prepareRest_preserves_source _ pid pkt (fresh_ready pid)
    ((ensures_iff _ _ _).mp (TimerCore.del pid .newHandshake))
    (ready_join _ (CurrentSlots.timersTraversal_preserves pid)
      ((ensures_iff _ _ _).mp (TimerCore.sender_core _
        (traversal_tables pid) (sender_traversal pid))))
    (data_ready pid) (stats_ready pid) dishonest_ready
    (fun protocol ds bytes=>ready_join _
      (store_slots (inetEcnDecapsulate_sameWGStore protocol ds bytes))
      (ConfigurationIndex.frame_core (store_fields (inetEcnDecapsulate_sameWGStore protocol ds bytes))))

theorem finish_ready (pid : PeerId) (ready : Packets.RxReady) :
    Preserves TimerCore.Ready (Packets.rxFinish pid ready) :=
  rxFinish_preserves_source _ pid ready
    (ready_join _ (lookupRepay_slots ready.protocol ready.bytes)
      (ConfigurationIndex.frame_core (lookupRepay_indexFields ready.protocol ready.bytes)))
    (dishonest_ready .peer) (stats_ready pid _)

theorem after_ready (pid : PeerId) (pkt : RxPacket) (confirmed : Bool) :
    Preserves TimerCore.Ready (ConsumeConfirmation.afterConfirmation pid pkt confirmed) := by
  apply afterConfirmation_preserves_source _ pid pkt confirmed
  · exact ready_join _ (CurrentSlots.timersHandshakeComplete_preserves pid _)
      ((ensures_iff _ _ _).mp (TimerCore.sender_core _
        (timersHandshakeComplete_tables pid _) (Incoming.handshakeComplete_sender pid _)))
  · apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b pre run
    exact ⟨(hoare_iff_run_ambient _ _ _).mp (CurrentSlots.sendStagedPackets_preserves pid)
      w a result v b pre.1 run, StagingRich.staged_core pid w a result v b pre run⟩
  · exact prepare_ready pid pkt
  · exact finish_ready pid

theorem consume_ready (pid : PeerId) (pkt : RxPacket) (endpoint : Endpoint) :
    Preserves TimerCore.Ready (consumeDataDone pid pkt endpoint) := by
  rw [ConsumeConfirmation.source]
  apply preserves_bind
    (ready_join _
      (CurrentSlots.fields_preserves (project:=id)
        ((pinned_const _private.Leanux.Proofs.WG.Queues.CurrentSlotCompletion.«0».Leanux.Proofs.WG.CurrentSlots.endpoint_fields) pid endpoint))
      (ConfigurationIndex.frame_core (ConfigurationIndex.endpoint_fields pid endpoint)))
  intro _
  exact preserves_bind
    (ready_join _ (CurrentSlots.receivedWithKeypair_preserves pid pkt.keypair)
      ((ensures_iff _ _ _).mp (receivedWithKeypair_indexCore pid pkt.keypair)))
    (after_ready pid pkt)
end Leanux.Proofs.WG.Index.ReceiveCompletion
