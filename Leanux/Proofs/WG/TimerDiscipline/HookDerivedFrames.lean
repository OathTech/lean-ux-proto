import Leanux.Proofs.WG.TimerDiscipline.HookTransmitWorkerSource
import Leanux.Proofs.WG.TimerDiscipline.HookSendEnvironmentSource
import Leanux.Proofs.WG.TimerDiscipline.ReceiveHookSource

/-! These actual caller journals do not add session-derived receipts.
The frame is unconditional and retains the filtered prior history on Stop. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.HookJournal
open Leanux Leanux.WG Leanux.Proofs.Logged

def derivedReceipt (r : Receipt) : Option Unit :=
  match r.hook with
  | .sessionDerived => some ()
  | _ => none

theorem observed_derived_frame (hook : Hook) (pid : PeerId)
    (other : hook ≠ .sessionDerived) :
    StateHistoryFrame derivedReceipt (observed hook pid) := by
  intro g ambient history
  change (runWGPrefix (observed hook pid) g ambient history).2.filterMap derivedReceipt =
    history.filterMap derivedReceipt
  rw [observed_exact]
  cases hook <;> first
    | exact False.elim (other rfl)
    | simp only [derivedReceipt, List.filterMap_append,
        List.filterMap_cons, List.filterMap_nil, List.append_nil]

theorem lift_derived_frame {α : Type} (action : WG.M α) :
    StateHistoryFrame derivedReceipt (liftWGPrefix action) :=
  fun _ => HistoryFrame.lift _ _

theorem pure_derived_frame {α : Type} (x : α) :
    StateHistoryFrame derivedReceipt (pure x : WGPrefix Receipt α) :=
  fun _ => HistoryFrame.pure _ _

theorem transmit_derived_frame (pid : PeerId) (items : List SkbId) :
    StateHistoryFrame derivedReceipt (Transmit.observed pid items) := by
  unfold Transmit.observed Transmit.withHooks
  apply (observed_derived_frame .traversal pid (by intro h; cases h)).bind
  intro _
  apply (observed_derived_frame .authenticatedSent pid (by intro h; cases h)).bind
  intro _
  apply (lift_derived_frame _).bind
  intro sent
  apply (lift_derived_frame _).bind
  intro _
  apply (lift_derived_frame _).bind
  intro selected
  cases selected
  · exact lift_derived_frame _
  · exact (observed_derived_frame .dataSent pid (by intro h; cases h)).bind
      (fun _ => lift_derived_frame _)

theorem initiation_derived_frame (pid : PeerId) :
    StateHistoryFrame derivedReceipt (Initiation.observed pid) := by
  unfold Initiation.observed Initiation.withHooks
  repeat' first
    | exact observed_derived_frame _ _ (by intro impossible; cases impossible)
    | exact lift_derived_frame _
    | exact pure_derived_frame _
    | apply StateHistoryFrame.bind
    | split
    | (intro x; try dsimp only)

theorem initiation_worker_derived_frame (pid : PeerId) :
    StateHistoryFrame derivedReceipt (Initiation.workerObserved pid) :=
  (initiation_derived_frame pid).bind (fun _ => lift_derived_frame _)

theorem receive_prepare_derived_frame (pid : PeerId) (pkt : RxPacket) :
    StateHistoryFrame derivedReceipt (ReceiveHookJournal.prepare pid pkt) := by
  unfold ReceiveHookJournal.prepare ReceiveHookJournal.prepareWith
  apply (lift_derived_frame _).bind
  intro _
  apply (observed_derived_frame .authenticatedReceived pid (by intro h; cases h)).bind
  intro _
  apply (observed_derived_frame .traversal pid (by intro h; cases h)).bind
  intro _
  apply (lift_derived_frame _).bind
  intro keepalive
  cases keepalive
  · exact (observed_derived_frame .dataReceived pid (by intro h; cases h)).bind
      (fun _ => lift_derived_frame _)
  · exact (lift_derived_frame _).bind (fun _ => pure_derived_frame _)

theorem receive_after_derived_frame (pid : PeerId) (pkt : RxPacket) (confirmed : Bool) :
    StateHistoryFrame derivedReceipt (ReceiveHookJournal.after pid pkt confirmed) := by
  have tail : StateHistoryFrame derivedReceipt
      (do let ready ← ReceiveHookJournal.prepare pid pkt
          match ready with
          | none => pure none
          | some ready => liftWGPrefix (Leanux.Proofs.WG.Packets.rxFinish pid ready)) := by
    apply (receive_prepare_derived_frame pid pkt).bind
    intro ready
    cases ready
    · exact pure_derived_frame _
    · exact lift_derived_frame _
  unfold ReceiveHookJournal.after ReceiveHookJournal.afterWith
  dsimp only
  apply (lift_derived_frame _).bind
  intro received
  cases received
  · exact tail
  · exact (observed_derived_frame (.handshakeComplete .walltimeLastHandshakeData) pid
      (by intro impossible; cases impossible)).bind
        (fun _ => (lift_derived_frame _).bind (fun _ => tail))

theorem receive_consume_derived_frame (pid : PeerId) (pkt : RxPacket) (ep : Endpoint) :
    StateHistoryFrame derivedReceipt (ReceiveHookJournal.consume pid pkt ep) := by
  unfold ReceiveHookJournal.consume ReceiveHookJournal.consumeWith
  exact (lift_derived_frame _).bind (fun _ =>
    (lift_derived_frame _).bind (fun confirmed => receive_after_derived_frame pid pkt confirmed))

theorem transmit_worker_derived_frame (pid : PeerId) :
    StateHistoryFrame derivedReceipt (TransmitWorker.observed pid) := by
  unfold TransmitWorker.observed TransmitWorker.stepWith
  apply (lift_derived_frame _).bind
  rintro (_ | ⟨item,key,crypted⟩)
  · exact pure_derived_frame _
  · cases crypted
    · exact lift_derived_frame _
    · exact (transmit_derived_frame pid item).bind (fun _ => lift_derived_frame _)

/-- Fixing the projected prefix is a history-only invariant. -/
theorem frame_preserves_filtered {E F State α : Type} (ρ : E → Option F)
    {action : PrefixT E State α} (appends : Appends action)
    (frame : HistoryFrame ρ action) (before : List F) :
    PrefixPreserves (fun h _ => h.filterMap ρ = before)
      (fun h => h.filterMap ρ = before) action := by
  intro w h pre
  obtain ⟨added,history⟩ := appends w h
  have post := (frame w h).trans pre
  refine ⟨added,history,post,?_⟩
  cases run : (runPrefix action w h).1 with
  | error stop => trivial
  | ok out => exact post

theorem frame_of_preserves_filtered {E F State α : Type} (ρ : E → Option F)
    {action : PrefixT E State α}
    (preserves : ∀ before : List F, PrefixPreserves
      (fun h _ => h.filterMap ρ = before) (fun h => h.filterMap ρ = before) action) :
    HistoryFrame ρ action := by
  intro w h
  obtain ⟨_,_,post,_⟩ := preserves (h.filterMap ρ) w h rfl
  exact post

theorem transmit_iteration_derived_frame (pid : PeerId) :
    HistoryFrame derivedReceipt (TransmitWorker.iteration pid) := by
  apply frame_of_preserves_filtered
  intro before
  apply workerIterPrefix_preserves (I := fun h _ => h.filterMap derivedReceipt = before)
    (S := fun h => h.filterMap derivedReceipt = before) _ _ (fun _ _ pre => pre)
  · exact frame_preserves_filtered derivedReceipt
      (TransmitWorker.appends pid).liftWGObserver
      (transmit_worker_derived_frame pid).liftWGObserver before
  · exact frame_preserves_filtered derivedReceipt
      ((Appends.lift _).bind (fun _ => Appends.lift _))
      ((HistoryFrame.lift _ _).bind (fun _ => HistoryFrame.lift _ _)) before

theorem send_environment_derived_frame :
    HistoryFrame derivedReceipt SendEnvironment.one := by
  unfold SendEnvironment.one
  apply (HistoryFrame.lift _ _).bind
  intro selected
  apply (HistoryFrame.lift _ _).bind
  intro _
  apply frame_of_preserves_filtered
  intro before
  apply runWorkerPrefix_preserves (I := fun h _ => h.filterMap derivedReceipt = before)
    (S := fun h => h.filterMap derivedReceipt = before) (fun _ _ pre => pre)
    (fun _ _ _ _ pre => pre) .sendWorker
  exact frame_preserves_filtered derivedReceipt
    (Initiation.worker_appends selected.2).liftWGObserver
    (initiation_worker_derived_frame selected.2).liftWGObserver before


end Leanux.Proofs.WG.TimerDiscipline.HookJournal
