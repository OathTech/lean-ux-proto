import Leanux.Proofs.WG.Roaming.RemoteChronologyPollHistorySource
import Leanux.Proofs.WG.Roaming.RemoteChronologyCaptureSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteChronology.Driver
open Leanux Leanux.WG Noise Lifetimes Queues Std.Do
open Leanux.Proofs.Framing Leanux.Proofs.Logged

theorem safe (entry : RemoteMap) (h : List RemoteDriver.Event) (w : World)
    (pre : Inv entry h w) : RemoteDriver.Safe h := pre.2

/-- Only the actual fresh suffix of the lower call is mapped back. Earlier
configuration and birth events remain in the outer history. -/
theorem focus_relative {α : Type} (entry : RemoteMap) (observed : RxHistory.Obs α)
    (relative : Poll.Relative Poll.historyEffect observed) :
    PrefixPreserves (Inv entry) RemoteDriver.Safe (RemoteDriver.focus observed) := by
  intro w h prior
  obtain ⟨suffix,appended,normal⟩ := relative w (h.filterMap RemoteDriver.rxEvent)
  have actual := focusPrefix_suffix RemoteDriver.Event.rx RemoteDriver.rxEvent observed w h
    _ suffix (Prod.ext rfl appended)
  have valid : RemoteDriver.Safe (h ++ suffix.map RemoteDriver.Event.rx) := by
    apply prior.2.append
    intro event member
    obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
    trivial
  change runPrefix (RemoteDriver.focus observed) w h = _ at actual
  rw [actual]
  refine ⟨suffix.map RemoteDriver.Event.rx,rfl,valid,?_⟩
  cases run : (runPrefix observed w (h.filterMap RemoteDriver.rxEvent)).1 with
  | error stop => trivial
  | ok out =>
    simp only [run] at normal
    exact ⟨append prior.1 (map_last effect RemoteDriver.Event.rx normal),valid⟩

theorem focus_retained {α : Type} (entry : RemoteMap) (observed : RxHistory.Obs α)
    (action : Leanux.M α) (appends : Appends observed) (erase : ErasesPrefix observed action)
    (inert : ∀ w h pid, (runPrefix observed w h).2.filterMap (fun e => Poll.historyEffect e pid) =
      h.filterMap (fun e => Poll.historyEffect e pid))
    (kept : ∀ initial, Preserves (RemotePoll.ProductRetained initial) action) :
    PrefixPreserves (Inv entry) RemoteDriver.Safe (RemoteDriver.focus observed) :=
  focus_relative entry observed (Poll.quiet_relative Poll.historyEffect observed action appends erase inert kept)

theorem focus_mixed {α : Type} (entry : RemoteMap) (observed : PrefixM LifetimeEvent α)
    (action : Leanux.M α) (erase : ErasesPrefix observed action)
    (kept : ∀ initial, Preserves (RemotePoll.ProductRetained initial) action) :
    PrefixPreserves (Inv entry) RemoteDriver.Safe (RemoteDriver.focus (RxHistory.mixed observed)) :=
  focus_relative entry _ (Poll.mixed_relative observed action erase kept)

theorem focus_audit {α : Type} (entry : RemoteMap) (observed : AuditM α)
    (action : Leanux.M α) (erase : ErasesPrefix observed action)
    (kept : ∀ initial, Preserves (RemotePoll.ProductRetained initial) action) :
    PrefixPreserves (Inv entry) RemoteDriver.Safe (RemoteDriver.focus (RxHistory.audit observed)) :=
  focus_relative entry _ (Poll.audit_relative observed action erase kept)

theorem mixed_store {α : Type} (entry : RemoteMap) (observed : PrefixM LifetimeEvent α)
    (action : Leanux.M α) (erase : ErasesPrefix observed action) (frame : SameProductStore action) :
    PrefixPreserves (Inv entry) RemoteDriver.Safe (RemoteDriver.focus (RxHistory.mixed observed)) :=
  focus_mixed entry observed action erase (fun initial => RemoteWorkers.product_store initial action frame)

theorem audit_store {α : Type} (entry : RemoteMap) (observed : AuditM α)
    (action : Leanux.M α) (erase : ErasesPrefix observed action) (frame : SameProductStore action) :
    PrefixPreserves (Inv entry) RemoteDriver.Safe (RemoteDriver.focus (RxHistory.audit observed)) :=
  focus_audit entry observed action erase (fun initial => RemoteWorkers.product_store initial action frame)

theorem mixed_native {α : Type} (entry : RemoteMap) (observed : MixedM α)
    (action : WG.M α) (erase : ErasesStatePrefix observed action)
    (kept : ∀ initial, Ensures action (RemoteSilent.Retained initial) (fun _ => RemoteSilent.Retained initial)) :
    PrefixPreserves (Inv entry) RemoteDriver.Safe
      (RemoteDriver.focus (RxHistory.mixed (liftWGObserver observed))) :=
  focus_mixed entry _ _ (liftWGObserver_erases erase)
    (fun initial => PublicationPoll.native_product _ _ ((ensures_iff _ _ _).mp (kept initial)))

theorem receiveIteration_preserves (entry : RemoteMap) :
    PrefixPreserves (Inv entry) RemoteDriver.Safe RemoteDriver.receiveIterationObserved := by
  apply workerIterPrefix_preserves _ _ (safe entry) (receive_preserves entry)
  apply PrefixEnsures.lift
  · exact safe entry
  · intro h w value final pre run
    exact ⟨retained pre.1 ((hoare_iff_run _ _ _).mp
      (RemoteWorkers.product_store (destinationAt w.wg) _ (condResched_sameKernel _))
      w value final (.refl _) run),pre.2⟩


end Leanux.Proofs.WG.Roaming.RemoteChronology.Driver
