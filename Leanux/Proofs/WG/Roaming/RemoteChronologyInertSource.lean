import Leanux.Proofs.WG.Roaming.RemoteChronologyModel
import Leanux.Proofs.WG.Roaming.RemoteConfigurationCaptureSource
import Leanux.Proofs.WG.Origins.HistoryAdapters

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteChronology
open Leanux Leanux.WG Noise Lifetimes Queues Leanux.Proofs.Logged

theorem untouched_of_filterMap_nil {E : Type} (effect : Effect E)
    (events : List E) (pid : PeerId)
    (empty : events.filterMap (fun e => effect e pid) = []) :
    Untouched effect events pid := by
  intro event member
  cases selected : effect event pid with
  | none => rfl
  | some value =>
    have found : value ∈ events.filterMap (fun e => effect e pid) :=
      List.mem_filterMap.mpr ⟨event,member,selected⟩
    rw [empty] at found
    cases found

theorem untouched_suffix {E : Type} (effect : Effect E)
    (before suffix after : List E) (appended : after = before ++ suffix)
    (same : ∀ pid, after.filterMap (fun e => effect e pid) =
      before.filterMap (fun e => effect e pid)) :
    ∀ pid, Untouched effect suffix pid := by
  intro pid
  apply untouched_of_filterMap_nil effect suffix pid
  have filtered := same pid
  rw [appended,List.filterMap_append] at filtered
  simpa using congrArg (List.drop (before.filterMap (fun e => effect e pid)).length) filtered

theorem inert_suffix {E State α : Type} (effect : Effect E)
    (observed : PrefixT E State α) (appends : Appends observed)
    (inert : ∀ w h pid, (runPrefix observed w h).2.filterMap (fun e => effect e pid) =
      h.filterMap (fun e => effect e pid)) (w : State) (h : List E) :
    ∃ suffix, (runPrefix observed w h).2 = h ++ suffix ∧
      ∀ pid, Untouched effect suffix pid := by
  obtain ⟨suffix,append⟩ := appends w h
  exact ⟨suffix,append,untouched_suffix effect h suffix _ append (inert w h)⟩

theorem focused_history_inert {E F State α : Type} (effect : Effect E)
    (encode : F → E) (decode : E → Option F) (observed : PrefixT F State α)
    (appends : Appends observed)
    (inert : ∀ w h pid, (runPrefix observed w h).2.filterMap (fun e => effect (encode e) pid) =
      h.filterMap (fun e => effect (encode e) pid)) :
    ∀ w h pid, (runPrefix (focusPrefix encode decode observed) w h).2.filterMap
      (fun e => effect e pid) = h.filterMap (fun e => effect e pid) := by
  intro w h pid
  obtain ⟨suffix,appended⟩ := appends w (h.filterMap decode)
  have quiet := untouched_suffix (fun e target => effect (encode e) target)
    (h.filterMap decode) suffix _ appended (inert w (h.filterMap decode))
  rw [focusPrefix_suffix encode decode observed w h _ suffix (Prod.ext rfl appended)]
  rw [List.filterMap_append]
  have none : (suffix.map encode).filterMap (fun e => effect e pid) = [] := by
    clear appended
    induction suffix with
    | nil => rfl
    | cons e rest ih =>
      have head := quiet pid e (by simp)
      have tail : ∀ target, Untouched (fun e target => effect (encode e) target) rest target :=
        fun target item member => quiet target item (List.mem_cons_of_mem _ member)
      simp only [List.map_cons,List.filterMap_cons,head,ih tail]
  rw [none,List.append_nil]

theorem nativeRx_history_inert {α : Type} (effect : Effect RxHistory.Event)
    (inert : ∀ e pid, effect (.audit e) pid = none) (observed : MixedM α) :
    ∀ g ambient h pid,
      (runWGPrefix (RoutingJoint.nativeRx observed) g ambient h).2.filterMap
        (fun e => effect e pid) = h.filterMap (fun e => effect e pid) := by
  intro g ambient h pid
  exact focusPrefix_other RxHistory.Event.audit RxHistory.auditEvent
    (fun e => effect e pid) (fun e => inert e pid)
    ((focusStatePrefix AuditEvent.lifetime AuditEvent.lifetime? observed).run g) ambient h

theorem historyFocus_history_inert {α : Type} (effect : Effect RxHistory.Event)
    (inert : ∀ e pid, effect (Origins.HistoryAdapters.encode e) pid = none)
    (observed : PrefixM Origins.Event α) :
    ∀ w h pid, (runPrefix (Origins.HistoryAdapters.focus observed) w h).2.filterMap
      (fun e => effect e pid) = h.filterMap (fun e => effect e pid) := by
  intro w h pid
  exact Origins.HistoryAdapters.focus_other (fun e => effect e pid)
    (fun e => inert e pid) observed w h

theorem configurationAccess_history_inert {E α : Type} (effect : Effect E)
    (encode : RxHistory.Event → E) (decode : E → Option RxHistory.Event)
    (inert : ∀ e pid, effect (encode (.audit e)) pid = none)
    (observed : MixedM α) :
    ∀ g ambient h pid,
      (runWGPrefix (RemoteConfiguration.access encode decode observed) g ambient h).2.filterMap
        (fun e => effect e pid) = h.filterMap (fun e => effect e pid) := by
  intro g
  exact focused_history_inert effect encode decode ((RoutingJoint.nativeRx observed).run g)
    (StateAppends.focus _ _ _ g)
    (nativeRx_history_inert (fun e pid => effect (encode e) pid) inert observed g)

end Leanux.Proofs.WG.Roaming.RemoteChronology
