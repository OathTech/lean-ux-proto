import Leanux.Proofs.WG.TimerDiscipline.HandshakeJournalModel

/-! A state-indexed allocation frontier for completed successful sessions. Ordering concerns allocation stamps, with a separate normal final-counter bound; no successor state is attached to Stop. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.HandshakeJournal
open Leanux Leanux.WG

def sessionIds (h : List Event) : List Nat := h.filterMap Event.sessionId
def Ordered (h : List Event) : Prop := (sessionIds h).Pairwise (·<·)
def Frontier (h : List Event) (counter : Nat) : Prop :=
  Ordered h ∧ ∀serial∈sessionIds h,serial≤counter

def AllocationFacts {α : Type} (result : Inspection α) : Prop :=
  Ordered result.2 ∧ (sessionIds result.2).Nodup ∧
    (∀serial,result.2.countP (fun e=>e.sessionId==some serial)≤1 ∧
      result.2.countP (fun e=>e.derivedId==some serial)≤1) ∧
    match result.1 with
    | .error _ => True
    | .ok (_,last) => Frontier result.2 last.wg.keypairCounter

end Leanux.Proofs.WG.TimerDiscipline.HandshakeJournal
