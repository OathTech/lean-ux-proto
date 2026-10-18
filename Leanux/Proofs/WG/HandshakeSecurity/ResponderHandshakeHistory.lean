import Leanux.Proofs.WG.HandshakeSecurity.ResponderHandshakeActor

namespace Leanux.Proofs.WG.HandshakeSecurity.Responder.Joint
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues Queues.RxCredits

theorem Inv.handshake (hi : Inv h w) :
    HandshakeControl.Inv (Confirmation.completedLabels h) w.wg :=
  ⟨hi.2.1.1, HandshakeEntry.of_owner hi.1.1 hi.2.1.2⟩

/-- Native actors may use C1's configured/owner/slot entry carrier, provided
it is derived at this actual journal boundary. They append no confirmations. -/
theorem quiet_handshake (g : RxHistory.Obs α) (a : WG.M α)
    (inherited : PublicationJoint.Preserves g) (appends : Appends g)
    (erases : ErasesPrefix g (liftWG a)) (frame : HistoryFrame Global.consumer g)
    (preserves : ∀ confirmed, Framing.Preserves (HandshakeControl.Inv confirmed) a) :
    Preserves g := by
  apply combine _ inherited
  intro w h hi
  obtain ⟨suffix, append⟩ := appends w h
  have empty : suffix.filterMap Global.consumer = [] := by
    have same := frame w h
    rw [append, List.filterMap_append] at same
    simpa using same
  have safe : Global.Safe (runPrefix g w h).2 := append ▸ hi.2.2.quiet empty
  have labels : Confirmation.completedLabels (runPrefix g w h).2 = Confirmation.completedLabels h := by
    rw [Global.labels_consumer, Global.labels_consumer, frame w h]
  refine ⟨suffix, append, safe, ?_⟩
  cases run : (runPrefix g w h).1 with
  | error stop => trivial
  | ok out =>
    refine ⟨?_, safe⟩
    rw [labels]
    have native := (erases w h).symm.trans run
    rw [liftWG_run] at native
    cases source : (a.run w.wg).run w.ambient with
    | error stop => simp [source, Except.map] at native
    | ok returned =>
      rcases returned with ⟨⟨value, world⟩, ambient⟩
      simp only [source, Except.map, Except.ok.injEq] at native
      obtain ⟨rfl, rfl⟩ := native
      have post := (hoare_iff_run_ambient _ _ _).mp (preserves _)
        w.wg w.ambient value world ambient hi.handshake source
      exact ⟨post.1, post.2.2⟩

/-- The original session observer and all native handshake branches share the
persistent C1 receive journal, including its real stopped-prefix behavior. -/
theorem receiveStep (H1 : H1ResponderCurrentEdges) :
    Preserves Origins.HistoryAdapters.receiveStep :=
  quiet_handshake _ WG.receiveStep PublicationJoint.receiveStep (Appends.focus _ _ _)
    Origins.HistoryAdapters.receiveStep_erases
    (Origins.HistoryAdapters.focus_other Global.consumer (by intro e; cases e <;> rfl) _)
    (fun _ => HandshakeControl.step H1)

theorem receiveIteration (H1 : H1ResponderCurrentEdges) :
    Preserves Origins.HistoryAdapters.receiveIteration := by
  apply workerIterPrefix_preserves _ _ (fun _ _ hi => hi.safe) (receiveStep H1)
  exact from_global _ (PublicationJoint.lift_store _ (condResched_sameKernel .receiveWorker))
    (Global.lift_store _ (condResched_sameKernel .receiveWorker))

end Leanux.Proofs.WG.HandshakeSecurity.Responder.Joint
