import Leanux.Proofs.WG.Roaming.RemotePollSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemotePoll
open Leanux Leanux.WG Noise Lifetimes Queues Std.Do
open Leanux.Proofs.Framing Leanux.Proofs.Logged

theorem history_poll_covered (entry : RemoteMap) (pid : PeerId) (budget : Nat) :
    PrefixPreserves (Covered entry rxCause) (fun _=>True) (RxHistory.observePoll pid budget) := by
  intro w h hi
  let seeded := RxJoint.seed (RxHistory.prior h)
  obtain ⟨suffix,append⟩:=RxJoint.poll_appends pid budget w seeded
  have actual:=RxHistory.observePoll_suffix pid budget w h _ suffix (Prod.ext rfl append)
  rw [actual]
  refine ⟨suffix.map RxHistory.promote,rfl,True.intro,?_⟩
  have normal:=(poll_covered (destinationAt w.wg) pid budget w seeded
    (fun _ _ present=>Or.inl present)).choose_spec.2.2
  cases run:(runPrefix (RxJoint.poll pid budget) w seeded).1 with
  | error stop=>trivial
  | ok out=>
    obtain ⟨value,v⟩:=out
    simp only [run] at normal
    intro target remote present
    rcases normal target remote present with earlier | ⟨event,member,cause⟩
    · exact hi.append_history target remote earlier
    · rw [append] at member
      rcases List.mem_append.mp member with old | fresh
      · obtain ⟨original,_,rfl⟩:=List.mem_map.mp old
        exact False.elim cause
      · exact Or.inr ⟨RxHistory.promote event,
          List.mem_append_right _ (List.mem_map.mpr ⟨event,fresh,rfl⟩),cause⟩


theorem history_native {α : Type} (entry : RemoteMap) (g : MixedM α) (a : WG.M α)
    (erases : ErasesStatePrefix g a) (keep : ∀initial,Preserves (Retained initial) a) :
    PrefixPreserves (Covered entry rxCause) (fun _=>True)
      (RxHistory.audit (auditFocus (liftWGObserver g))) :=
  quiet entry rxCause _ _ (Appends.focus _ _ _)
    (RxHistory.audit_erases (auditFocus_erases (liftWGObserver_erases erases)))
    (fun initial=>PublicationPoll.native_product _ _ (keep initial))

theorem pending_covered (entry : RemoteMap) :
    PrefixPreserves (Covered entry rxCause) (fun _=>True)
      (RxHistory.audit (auditFocus (liftWGObserver RxNapi.pendingPrefix))) := by
  apply history_native entry _ _ RxNapi.pending_erases
  intro initial
  apply SameView.wp (P:=RemoteRetained initial)
  apply RemoteCompletion.store_remotes
  unfold RxNapi.pendingSource
  exact getDev_sameWGStore.bind (fun _=>SameView.pure _ _)

theorem scheduled_covered (entry : RemoteMap) :
    PrefixPreserves (Covered entry rxCause) (fun _=>True)
      (RxHistory.audit (auditFocus (liftWGObserver RxNapi.scheduledPrefix))) := by
  apply history_native entry _ _ RxNapi.scheduled_erases
  intro initial
  apply SameView.wp (P:=RemoteRetained initial)
  apply RemoteCompletion.store_remotes
  unfold RxNapi.scheduledSource
  exact getDev_sameWGStore.bind (fun _=>SameView.pure _ _)

theorem softirq_covered (entry : RemoteMap) :
    PrefixPreserves (Covered entry rxCause) (fun _=>True) RxHistory.napiSoftirq := by
  rw [NapiSource.softirq_factor]
  exact RxNapi.softirq_preserves (fun _ _ _=>True.intro)
    (covered_product_store entry rxCause) (pending_covered entry) (history_poll_covered entry)

theorem inline_covered (entry : RemoteMap) :
    PrefixPreserves (Covered entry rxCause) (fun _=>True) RxHistory.pollScheduledInline := by
  rw [NapiSource.inline_factor]
  exact RxNapi.inline_preserves (fun _ _ _=>True.intro)
    (covered_product_store entry rxCause) (pending_covered entry) (history_poll_covered entry)

theorem irqExit_covered (entry : RemoteMap) :
    PrefixPreserves (Covered entry rxCause) (fun _=>True) RxHistory.napiIrqExit := by
  rw [NapiSource.irqExit_factor]
  exact RxNapi.irqExit_preserves (fun _ _ _=>True.intro)
    (covered_product_store entry rxCause) (scheduled_covered entry) (softirq_covered entry)

theorem prepare_covered (entry : RemoteMap) :
    PrefixPreserves (Covered entry rxCause) (fun _=>True) Origins.HistoryAdapters.prepare :=
  quiet entry rxCause _ _ (Appends.focus _ _ _)
    Origins.HistoryAdapters.prepare_erases
    (fun initial=>PublicationPoll.native_product _ _ (prepare_retained initial))

theorem decrypt_covered (entry : RemoteMap) :
    PrefixPreserves (Covered entry rxCause) (fun _=>True) RxHistory.decryptStep := by
  rw [NapiSource.decrypt_factor]
  exact NapiSource.decrypt_preserves (fun _ _ _=>True.intro) (prepare_covered entry)
    (fun pid=>quiet entry rxCause _ _ (Appends.focus _ _ _)
      (RxHistory.mixed_erases (liftWGObserver_erases (peerPutMixed_erases _)))
      (fun initial=>PublicationPoll.native_product _ _
        ((ensures_iff _ _ _).mp (peerPut_remotes (some pid) initial))))
    (softirq_covered entry) (irqExit_covered entry)

theorem decryptIteration_covered (entry : RemoteMap) :
    PrefixPreserves (Covered entry rxCause) (fun _=>True) RxHistory.decryptIteration := by
  rw [NapiSource.decryptIteration_factor]
  apply workerIterPrefix_preserves _ _ (fun _ _ _=>True.intro) (decrypt_covered entry)
  exact (viewLiftPrefix_preserves productStoreView (fun _ _ _=>True.intro)
    (covered_product_store entry rxCause) (condResched_sameKernel .decryptWorker)).bind
      (fun b=>ambient entry rxCause (AmbientM.branch .decWorkerNeedResched b))

end Leanux.Proofs.WG.Roaming.RemotePoll
