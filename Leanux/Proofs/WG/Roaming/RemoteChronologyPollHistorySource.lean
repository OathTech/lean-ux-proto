import Leanux.Proofs.WG.Roaming.RemoteChronologyWorkerFrames
import Leanux.Proofs.WG.Roaming.RemoteChronologyPollSource
import Leanux.Proofs.WG.Roaming.RemoteDriverSchedulerSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteChronology.Poll
open Leanux Leanux.WG Noise Lifetimes Queues Std.Do
open Leanux.Proofs.Framing Leanux.Proofs.Logged

theorem mixed_inert {α : Type} (observed : PrefixM LifetimeEvent α) :
    ∀ w h pid, (runPrefix (RxHistory.mixed observed) w h).2.filterMap
      (fun e => historyEffect e pid) = h.filterMap (fun e => historyEffect e pid) :=
  fun w h pid => focusPrefix_other RxHistory.Event.audit RxHistory.auditEvent
    (fun e => historyEffect e pid) (fun _ => rfl) (auditFocus observed) w h

theorem audit_inert {α : Type} (observed : AuditM α) :
    ∀ w h pid, (runPrefix (RxHistory.audit observed) w h).2.filterMap
      (fun e => historyEffect e pid) = h.filterMap (fun e => historyEffect e pid) :=
  fun w h pid => focusPrefix_other RxHistory.Event.audit RxHistory.auditEvent
    (fun e => historyEffect e pid) (fun _ => rfl) observed w h

theorem mixed_relative {α : Type} (observed : PrefixM LifetimeEvent α)
    (action : Leanux.M α) (erase : ErasesPrefix observed action)
    (kept : ∀ initial, Preserves (RemotePoll.ProductRetained initial) action) :
    Relative historyEffect (RxHistory.mixed observed) :=
  quiet_relative historyEffect _ action (Appends.focus _ _ _)
    (RxHistory.mixed_erases erase) (mixed_inert observed) kept

theorem audit_relative {α : Type} (observed : AuditM α)
    (action : Leanux.M α) (erase : ErasesPrefix observed action)
    (kept : ∀ initial, Preserves (RemotePoll.ProductRetained initial) action) :
    Relative historyEffect (RxHistory.audit observed) :=
  quiet_relative historyEffect _ action (Appends.focus _ _ _)
    (RxHistory.audit_erases erase) (audit_inert observed) kept

theorem history_native_relative {α : Type} (observed : MixedM α) (action : WG.M α)
    (erase : ErasesStatePrefix observed action)
    (kept : ∀ initial, Preserves (RemoteSilent.Retained initial) action) :
    Relative historyEffect (RxHistory.audit (auditFocus (liftWGObserver observed))) :=
  mixed_relative _ _ (liftWGObserver_erases erase)
    (fun initial => PublicationPoll.native_product _ _ (kept initial))

theorem pending_relative :
    Relative historyEffect (RxHistory.audit (auditFocus (liftWGObserver RxNapi.pendingPrefix))) := by
  apply history_native_relative _ _ RxNapi.pending_erases
  intro initial
  apply SameView.wp (P := RemoteRetained initial)
  apply RemoteCompletion.store_remotes
  unfold RxNapi.pendingSource
  exact getDev_sameWGStore.bind (fun _ => SameView.pure _ _)

theorem scheduled_relative :
    Relative historyEffect (RxHistory.audit (auditFocus (liftWGObserver RxNapi.scheduledPrefix))) := by
  apply history_native_relative _ _ RxNapi.scheduled_erases
  intro initial
  apply SameView.wp (P := RemoteRetained initial)
  apply RemoteCompletion.store_remotes
  unfold RxNapi.scheduledSource
  exact getDev_sameWGStore.bind (fun _ => SameView.pure _ _)

theorem softirq_relative : Relative historyEffect RxHistory.napiSoftirq := by
  apply relative_of_suffixTracks
  intro entry base
  rw [NapiSource.softirq_factor]
  exact RxNapi.softirq_preserves (fun _ _ _ => True.intro)
    (suffixTracks_product_store historyEffect entry base)
    (relative_suffixTracks pending_relative entry base)
    (fun pid budget => relative_suffixTracks (history_poll_relative pid budget) entry base)

theorem inline_relative : Relative historyEffect RxHistory.pollScheduledInline := by
  apply relative_of_suffixTracks
  intro entry base
  rw [NapiSource.inline_factor]
  exact RxNapi.inline_preserves (fun _ _ _ => True.intro)
    (suffixTracks_product_store historyEffect entry base)
    (relative_suffixTracks pending_relative entry base)
    (fun pid budget => relative_suffixTracks (history_poll_relative pid budget) entry base)

theorem irqExit_relative : Relative historyEffect RxHistory.napiIrqExit := by
  apply relative_of_suffixTracks
  intro entry base
  rw [NapiSource.irqExit_factor]
  exact RxNapi.irqExit_preserves (fun _ _ _ => True.intro)
    (suffixTracks_product_store historyEffect entry base)
    (relative_suffixTracks scheduled_relative entry base)
    (relative_suffixTracks softirq_relative entry base)

theorem prepare_relative : Relative historyEffect Origins.HistoryAdapters.prepare :=
  quiet_relative historyEffect _ _ (Appends.focus _ _ _)
    Origins.HistoryAdapters.prepare_erases
    (historyFocus_history_inert historyEffect (by intro e pid; cases e <;> rfl) _)
    (fun initial => PublicationPoll.native_product _ _ (RemotePoll.prepare_retained initial))

theorem decrypt_relative : Relative historyEffect RxHistory.decryptStep := by
  apply relative_of_suffixTracks
  intro entry base
  rw [NapiSource.decrypt_factor]
  exact NapiSource.decrypt_preserves (fun _ _ _ => True.intro)
    (relative_suffixTracks prepare_relative entry base)
    (fun pid => relative_suffixTracks
      (mixed_relative _ _ (liftWGObserver_erases (peerPutMixed_erases _))
        (fun initial => PublicationPoll.native_product _ _
          ((ensures_iff _ _ _).mp (peerPut_remotes (some pid) initial)))) entry base)
    (relative_suffixTracks softirq_relative entry base)
    (relative_suffixTracks irqExit_relative entry base)

theorem decryptIteration_relative : Relative historyEffect RxHistory.decryptIteration := by
  apply relative_of_suffixTracks
  intro entry base
  rw [NapiSource.decryptIteration_factor]
  apply workerIterPrefix_preserves _ _ (fun _ _ _ => True.intro)
    (relative_suffixTracks decrypt_relative entry base)
  exact (viewLiftPrefix_preserves productStoreView (fun _ _ _ => True.intro)
    (suffixTracks_product_store historyEffect entry base) (condResched_sameKernel .decryptWorker)).bind
      (fun b => relative_suffixTracks
        (quiet_relative historyEffect _ _ (Appends.lift _) (erasesPrefix_lift _) (fun _ _ _ => rfl)
          (fun _ => productAmbient_spec (AmbientM.branch .decWorkerNeedResched b) _ (fun _ _ prior => prior)))
        entry base)

theorem encryptIteration_relative : Relative historyEffect RxHistory.encryptIteration := by
  apply relative_of_suffixTracks
  intro entry base
  unfold RxHistory.encryptIteration
  apply PrefixPreserves.bind (relative_suffixTracks
    (mixed_relative _ _ (liftWGObserver_erases (erasesStatePrefix_lift _))
      (fun initial => PublicationPoll.native_product _ _
        (RemoteWorkers.encryptPoll_frame.wp (RemoteRetained initial)))) entry base)
  intro item
  exact (relative_suffixTracks softirq_relative entry base).bind (fun _ => relative_suffixTracks
    (mixed_relative _ _ (RxWorkers.encryptTail_erases item)
      (fun initial => RemoteWorkers.encryptTail initial item)) entry base)


end Leanux.Proofs.WG.Roaming.RemoteChronology.Poll
