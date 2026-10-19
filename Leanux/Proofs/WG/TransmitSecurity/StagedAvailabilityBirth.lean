import Leanux.Proofs.WG.TransmitSecurity.StagedAvailabilityFrames

/-! A fresh native birth is later than every allocation so far. Ordered
append, prefix removal and restoration do not manufacture a fresh credit. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
open Leanux Leanux.WG Leanux.Proofs.Logged
open AuthenticatedEffects.CausalJournal Leanux.Proofs.WG.TransmitSecurity.Staged.Origins

theorem Aligned.append_history
    (before : Origins.Aligned (Live history generation pid stamp) tickets packets)
    (quiet : Quiet pid suffix) :
    Origins.Aligned (Live (history ++ suffix) generation pid stamp) tickets packets := by
  induction before with
  | nil => exact .nil
  | cons head tail ih => exact .cons ⟨head.1.append _,head.2.append quiet⟩ ih

theorem fresh_live
    (born : Origins.Aligned (Born (history ++ [event]) generation pid stamp)
      (freshTickets history.length first packets) packets)
    (quiet : Quiet pid [event]) :
    Origins.Aligned (Live (history ++ [event]) generation pid stamp)
      (freshTickets history.length first packets) packets := by
  induction packets generalizing first with
  | nil => exact .nil
  | cons packet rest ih =>
    cases born with
    | cons head tail => exact .cons ⟨head,Available.fresh quiet⟩ (ih tail)

theorem Batch.append_births (old : Batch history generation pid stamp packets)
    (quiet : Quiet pid [event])
    (fresh : Origins.Aligned (Born (history ++ [event]) generation pid stamp)
      (freshTickets history.length 0 added) added) :
    Batch (history ++ [event]) generation pid stamp (packets ++ added) := by
  obtain ⟨tickets,unique,born⟩ := old
  refine ⟨tickets ++ freshTickets history.length 0 added,?_,
    (Aligned.append_history born quiet).append (fresh_live fresh quiet)⟩
  apply List.nodup_append.mpr
  refine ⟨unique,freshTickets_unique _ _ _,?_⟩
  intro first firstMember second secondMember equal
  have earlier := (Aligned.forget born).position_lt firstMember
  have atEnd := (freshTickets_fields secondMember).1
  subst second
  omega

theorem consumed_not_available
    (born : Born before generation pid stamp ticket packet) (used : Uses pid event) :
    ¬ Available (before ++ event :: after) pid ticket := by
  intro available
  have earlier := born.position_lt
  have later := available before.length event (by simp) used
  omega

end Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
