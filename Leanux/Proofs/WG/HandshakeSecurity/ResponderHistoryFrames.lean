import Leanux.Proofs.WG.HandshakeSecurity.ResponderHistory

namespace Leanux.Proofs.WG.HandshakeSecurity.Responder.History
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues

theorem quiet (g : RxJoint.Obs α) (a : Leanux.M α) (base : List Nat)
    (appends : Appends g) (erases : ErasesPrefix g a)
    (frame : HistoryFrame consumer g)
    (preserves : ∀ confirmed, Preserves (fun w : World => Native confirmed w.wg) a) :
    PrefixPreserves (State base) (Checks base) g := by
  intro w h hi
  obtain ⟨s, hs⟩ := appends w h
  have same := frame w h
  have empty : s.filterMap consumer = [] := by
    rw [hs, List.filterMap_append] at same
    simpa using same
  have safe : Checks base (runPrefix g w h).2 := hs ▸ hi.2.quiet empty
  have labelFrame : labels (runPrefix g w h).2 = labels h := by
    rw [labels_consumer, labels_consumer, frame w h]
  refine ⟨s, hs, safe, ?_⟩
  cases result : (runPrefix g w h).1 with
  | error stop => trivial
  | ok out =>
    refine ⟨?_, safe⟩
    rw [labelFrame]
    exact (hoare_iff_run _ _ _).mp (preserves _) w out.1 out.2 hi.1
      ((erases w h).symm.trans result)

end Leanux.Proofs.WG.HandshakeSecurity.Responder.History
