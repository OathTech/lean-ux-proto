import Leanux.Proofs.WG.TimerDiscipline.HandshakeJournalModel

/-! Pure per-counter equality between successful-session receipts and derived-hook invocation receipts. This is not an enqueue, firing, or global uniqueness bound. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.HandshakeJournal
open Leanux Leanux.WG

theorem Paired.counts {h : List Event} (paired : Paired h) (serial : Nat) :
    h.countP (fun e=>e.sessionId==some serial)=h.countP (fun e=>e.derivedId==some serial) := by
  induction paired with
  | nil => rfl
  | quiet r prior other ih =>
    have empty : (Event.hook r).derivedId=none := by
      cases kind : r.hook <;> simp_all [Event.derivedId]
    rw [List.countP_append,List.countP_append,ih]
    congr 1
    simp [Event.sessionId,empty]
  | refused s prior notBegun ih =>
    rw [List.countP_append,List.countP_append,ih]
    congr 1
    simp [Event.sessionId,Event.derivedId,notBegun]
  | derived s r prior link ih =>
    obtain ⟨begun,kind,_,same,_⟩:=link
    rw [List.countP_append,List.countP_append,ih]
    congr 1
    simp [List.countP_cons,Event.sessionId,Event.derivedId,begun,kind,same]

end Leanux.Proofs.WG.TimerDiscipline.HandshakeJournal
