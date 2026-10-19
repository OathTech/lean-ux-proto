import Leanux.Proofs.WG.TimerDiscipline.HookOuterRulesSource
/-! Inline maintenance and configuration change no completed-session IDs.
They may emit hook receipts while draining actual send work. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.HandshakeMaintenance
open Leanux Leanux.WG Leanux.Proofs.Logged HandshakeJournal Lifetimes

theorem sendWorker_ids (pid : PeerId) : StateHistoryFrame Event.sessionId (sendWorker pid) := by
  intro g a h
  exact focusPrefix_other Event.hook decodeHook Event.sessionId (fun _=>rfl)
    ((HookJournal.Initiation.workerObserved pid).run g) a h

theorem sendWorker_ids_preserves (before : List Nat) (pid : PeerId) :
    StatePrefixPreserves (fun h _ _=>h.filterMap Event.sessionId=before)
      (fun h=>h.filterMap Event.sessionId=before) (sendWorker pid) := by
  intro g
  exact HookJournal.frame_preserves_filtered Event.sessionId (sendWorker_appends pid g)
    (sendWorker_ids pid g) before

theorem remove_ids (peer : Option PeerId) : StateHistoryFrame Event.sessionId (remove peer) := by
  intro g
  apply HookJournal.frame_of_preserves_filtered Event.sessionId
  intro before
  exact remove_preserves (fun h=>h.filterMap Event.sessionId=before)
    (sendWorker_ids_preserves before) peer g

theorem removeAll_ids : StateHistoryFrame Event.sessionId removeAll := by
  intro g
  apply HookJournal.frame_of_preserves_filtered Event.sessionId
  intro before
  exact removeAll_preserves (fun h=>h.filterMap Event.sessionId=before)
    (sendWorker_ids_preserves before) g

theorem envDown_ids : HistoryFrame Event.sessionId envDown := by
  apply HookJournal.frame_of_preserves_filtered Event.sessionId
  intro before
  exact envDown_preserves (fun h=>h.filterMap Event.sessionId=before)
    (sendWorker_ids_preserves before)

theorem envDelete_ids : HistoryFrame Event.sessionId envDelete := by
  apply HookJournal.frame_of_preserves_filtered Event.sessionId
  intro before
  exact envDelete_preserves (fun h=>h.filterMap Event.sessionId=before)
    (sendWorker_ids_preserves before)

end Leanux.Proofs.WG.TimerDiscipline.HandshakeMaintenance

namespace Leanux.Proofs.WG.TimerDiscipline.HookCommon
open Leanux Leanux.WG Leanux.Proofs.Logged HandshakeJournal Lifetimes

theorem peerCommand_ids (attrs : PeerAttrs) : StateHistoryFrame Event.sessionId (peerCommand attrs) := by
  intro g
  apply HookJournal.frame_of_preserves_filtered Event.sessionId
  intro before
  exact HookConfiguration.command_preserves (fun h=>h.filterMap Event.sessionId=before) _
    (fun p g=>HookJournal.frame_preserves_filtered Event.sessionId
      (HandshakeMaintenance.remove_appends p g) (HandshakeMaintenance.remove_ids p g) before) attrs g

theorem deviceCommand_ids (attrs : DeviceAttrs) : StateHistoryFrame Event.sessionId (deviceCommand attrs) := by
  intro g
  apply HookJournal.frame_of_preserves_filtered Event.sessionId
  intro before
  exact HookConfiguration.device_preserves (fun h=>h.filterMap Event.sessionId=before) _ _
    (fun p g=>HookJournal.frame_preserves_filtered Event.sessionId
      (HandshakeMaintenance.remove_appends p g) (HandshakeMaintenance.remove_ids p g) before)
    (fun g=>HookJournal.frame_preserves_filtered Event.sessionId
      (HandshakeMaintenance.removeAll_appends g) (HandshakeMaintenance.removeAll_ids g) before) attrs g

end Leanux.Proofs.WG.TimerDiscipline.HookCommon
