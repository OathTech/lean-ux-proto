import Leanux.Proofs.WG.Roaming.PollAuthenticationFrames
import Leanux.Proofs.WG.Roaming.PollAuthenticationCertificateSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.PollAuthentication
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Queues Lifetimes
variable {α : Type}

theorem reached_safe (h : List RxHistory.Event) (w : World) (hi : Reached h w) :
    PublicSafe h := ⟨hi.1.safe,hi.2⟩

theorem safe_quiet {h suffix : List RxHistory.Event} (hi : Safe h)
    (empty : suffix.filterMap endpointSensitive = []) : Safe (h ++ suffix) := by
  apply safe_append hi
  intro pre n id stamp pkt r post position
  have member : RxHistory.Event.checkedEndpoint n id stamp pkt r ∈ suffix := by
    rw [position]
    simp
  have present : () ∈ suffix.filterMap endpointSensitive :=
    List.mem_filterMap.mpr ⟨_,member,rfl⟩
  simp [empty] at present

/-- The original result-dependent contract is retained at its actual cut.
The added certificate predicate is history-only and survives a later Stop. -/
theorem quiet_ensures
    {P : List RxHistory.Event → World → Prop}
    {Q : α → List RxHistory.Event → World → Prop}
    (action : RxHistory.Obs α)
    (original : PrefixEnsures P PublicationJoint.Safe action Q)
    (frame : HistoryFrame endpointSensitive action) :
    PrefixEnsures (fun h w => P h w ∧ Safe h) PublicSafe action
      (fun x h w => Q x h w ∧ Safe h) := by
  intro w h hi
  obtain ⟨suffix,appended,publicationSafe,normal⟩ := original w h hi.1
  have kept := frame w h
  rw [appended,List.filterMap_append] at kept
  have empty : suffix.filterMap endpointSensitive = [] := by simpa using kept
  have certified : Safe (runPrefix action w h).2 := by
    rw [appended]
    exact safe_quiet hi.2 empty
  refine ⟨suffix,appended,⟨publicationSafe,certified⟩,?_⟩
  cases result : (runPrefix action w h).1 with
  | error stop => trivial
  | ok out => exact ⟨by simpa only [result] using normal,certified⟩

theorem quiet (action : RxHistory.Obs α)
    (original : PublicationJoint.Preserves action)
    (frame : HistoryFrame endpointSensitive action) :
    PrefixPreserves Reached PublicSafe action :=
  (quiet_ensures action original frame).preserves

theorem audit (action : AuditM α)
    (original : PublicationJoint.Preserves (RxHistory.audit action)) :
    PrefixPreserves Reached PublicSafe (RxHistory.audit action) :=
  quiet _ original
    (focusPrefix_other RxHistory.Event.audit RxHistory.auditEvent
      endpointSensitive (fun _ => rfl) action)

theorem mixed (action : PrefixM LifetimeEvent α)
    (original : PublicationJoint.Preserves (RxHistory.mixed action)) :
    PrefixPreserves Reached PublicSafe (RxHistory.mixed action) :=
  audit _ original

theorem origin (action : PrefixM Origins.Event α)
    (original : PublicationJoint.Preserves (Origins.HistoryAdapters.focus action)) :
    PrefixPreserves Reached PublicSafe (Origins.HistoryAdapters.focus action) :=
  quiet _ original
    (Origins.HistoryAdapters.focus_other endpointSensitive
      (by intro event; cases event <;> rfl) action)

theorem quiet_lift (action : Leanux.M α)
    (original : PublicationJoint.Preserves (liftPrefix action)) :
    PrefixPreserves Reached PublicSafe (liftPrefix action) :=
  quiet _ original (by intro w h; rfl)

theorem quiet_store (action : Leanux.M α) (frame : SameProductStore action) :
    PrefixPreserves Reached PublicSafe (liftPrefix action) :=
  quiet_lift action (PublicationJoint.lift_store action frame)

theorem audit_ensures
    {P : List RxHistory.Event → World → Prop}
    {Q : α → List RxHistory.Event → World → Prop}
    (action : AuditM α)
    (original : PrefixEnsures P PublicationJoint.Safe (RxHistory.audit action) Q) :
    PrefixEnsures (fun h w => P h w ∧ Safe h) PublicSafe (RxHistory.audit action)
      (fun x h w => Q x h w ∧ Safe h) :=
  quiet_ensures _ original
    (focusPrefix_other RxHistory.Event.audit RxHistory.auditEvent
      endpointSensitive (fun _ => rfl) action)

end Leanux.Proofs.WG.Roaming.PollAuthentication
