import Leanux.Proofs.WG.TransmitSecurity.StagedCreationFrames

/-! Allocation and publication use the same native source as the journal.
They preserve staged origins but do not establish terminal conservation. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open AuthenticatedEffects.CausalJournal

theorem allocate_epoch (packets : List DataPacket) :
    SameView Packets.epoch (packets.mapM newTxSkb) := by
  intro initial
  exact mapM_view_spec Packets.epoch (· = initial) newTxSkb packets
    (fun _ => (PacketOrigins.skb_epoch _).wp (· = initial))

theorem allocate_staged (packets : List DataPacket) :
    SameView stagedAt (packets.mapM newTxSkb) := by
  intro initial
  exact mapM_view_spec stagedAt (· = initial) newTxSkb packets
    (fun _ => (Exact.skb _).wp (· = initial))

theorem allocate_observed (packets : List DataPacket) : StateSafe (state (Journal.allocate packets)) := by
  apply state_quiet (StateAppends.focus _ _ _)
  · apply focused_history_frame _ _ selection? _ ((StateAppends.lift _).receiptWGObserved _)
    exact StateHistoryFrame.receiptWGObserved (by intro w a h; rfl) _ (fun _ => rfl)
  · exact focusStatePrefix_erases _ _ (receiptWGObserved_erases (erasesStatePrefix_lift _) _)
  · intro h
    exact frame (allocate_epoch packets) (Staged.of_view _ (allocate_staged packets))

theorem create_observed (pid : PeerId) (items : List SkbId) : StateSafe (state (Journal.create pid items)) := by
  have appends : StateAppends (Journal.create pid items) := by
    intro w a h
    exact Appends.focus Journal.Event.disposition Journal.disposition? (TxDisposition.create pid items)
      (NativeAdapter.world w a) h
  apply state_quiet (StateAppends.focus _ _ _)
  · apply focused_history_frame _ _ selection? _ appends
    intro w a h
    exact focusPrefix_other Journal.Event.disposition Journal.disposition? (selection? ∘ Event.old)
      (fun _ => rfl) (TxDisposition.create pid items) (NativeAdapter.world w a) h
  · exact focusStatePrefix_erases _ _ (NativeAdapter.lower_erases
      (focusPrefix_erases _ _ (TxDisposition.create_erases pid items)))
  · exact fun _ => Native.create pid items

theorem held_owner (owner : IndexOwner) :
    StatePrefixPreserves (Held pid peer) Safe (liftWGPrefix owner.peerDeref) :=
  held_world _ (fun initial => indexOwner_peerDeref_preserves owner (fun w => w = initial))

end Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
