import Leanux.Proofs.WG.TransmitSecurity.JournalPacketOrigins
import Leanux.Proofs.WG.TransmitSecurity.CompletionOriginFrames

/-! Allocation and queue creation cannot manufacture a TX completion entry.
The frame follows the native creation source, including both refusal arms. -/
namespace Leanux.Proofs.WG.TransmitSecurity.PacketOrigins
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues

theorem history_map {S E F G α : Type} {decode : E → Option F} {g : PrefixT E S α}
    (f : F → G) (frame : HistoryFrame decode g) :
    HistoryFrame (fun e => (decode e).map f) g := by
  have mapped (events : List E) :
      events.filterMap (fun e => (decode e).map f) = (events.filterMap decode).map f := by
    induction events with
    | nil => rfl
    | cons e rest ih => cases found : decode e <;> simp [found,ih]
  intro w h
  rw [mapped,mapped,frame w h]

theorem creation_watched (pid : PeerId) (items : List SkbId) :
    HistoryFrame watched?
      (focusPrefix Journal.Event.disposition Journal.disposition? (TxDisposition.create pid items)) := by
  apply CompletionOrigin.focus_frame _ _ _ _ (CompletionOrigin.create_appends pid items)
  have equal : (fun e => watched? (.disposition e)) =
      (fun e => (CompletionOrigin.txEntry? e).map (fun _ => ())) := by
    funext e
    cases e <;> rfl
  rw [equal]
  exact history_map _ (CompletionOrigin.create_frame pid items)

end Leanux.Proofs.WG.TransmitSecurity.PacketOrigins
