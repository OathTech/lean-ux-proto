import Leanux.Proofs.WG.TransmitSecurity.StagedFocusedProduct
import Leanux.Proofs.WG.TransmitSecurity.StagedWorkerFrames

/-! The actual decrypt, ring-consume and encryption hooks preserve staged
origins. Their focused events cannot create a staged-selection certificate. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open AuthenticatedEffects AuthenticatedEffects.CausalJournal

theorem poll : ProductSafe hooks.poll := by
  apply product_focused_quiet Event.old old? Journal.poll
  · exact Appends.receiptObserved (Appends.focus _ _ _)
  · exact HistoryFrame.receiptObserved
      (focusPrefix_other Journal.Event.ring Journal.ring? (selection? ∘ Event.old) (fun _ => rfl) _) (fun _ => rfl)
  · intro w h
    have projected := congrArg Prod.fst (Journal.poll_projects w h)
    have maps : (fun x : Option (List SkbId) × World => (id x.1,x.2)) = id := by funext ⟨value,v⟩; rfl
    rw [maps,Except.map_id] at projected
    exact projected.symm
  · intro h
    exact Native.product _ Native.poll

theorem encrypt (item : Option (List SkbId)) : ProductSafe (hooks.encrypt item) := by
  apply product_focused_quiet Event.old old? (Journal.encrypt item)
  · exact Appends.receiptObserved (Appends.focus _ _ _)
  · exact HistoryFrame.receiptObserved
      (focusPrefix_other Journal.Event.encrypted Journal.encryption? (selection? ∘ Event.old) (fun _ => rfl) _) (fun _ => rfl)
  · intro w h
    have projected := congrArg Prod.fst (Journal.encrypt_projects item w h)
    have maps : (fun x : Bool × World => (id x.1,x.2)) = id := by funext ⟨value,v⟩; rfl
    rw [maps,Except.map_id] at projected
    exact projected.symm
  · exact Native.encrypt item

theorem decrypt_prepare : ProductSafe hooks.prepare := by
  apply product_focused_quiet Event.old old? (TransportDriver.prepare Journal.Event.rxOrigin Journal.origin?)
  · exact Appends.focus _ _ _
  · exact focusPrefix_other Journal.Event.rxOrigin Journal.origin? (selection? ∘ Event.old) (fun _ => rfl) _
  · exact TransportDriver.prepare_erases _ _
  · intro h
    exact Native.product _ Native.decrypt_prepare

end Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
