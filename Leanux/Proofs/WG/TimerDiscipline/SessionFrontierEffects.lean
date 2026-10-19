import Leanux.Proofs.WG.TimerDiscipline.SessionFrontierModel
import Leanux.Proofs.WG.TimerDiscipline.HandshakeJournalEffects

/-! Pure frontier extension and per-stamp receipt counts. Paired history is used only for the derived-hook count; arbitrary valid history does not imply ordering. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.HandshakeJournal
open Leanux Leanux.WG

theorem frontier_nil (counter : Nat) : Frontier [] counter := by
  exact ⟨List.Pairwise.nil,by intro serial member;cases member⟩
theorem Frontier.mono {h : List Event} {before after : Nat}
    (prior : Frontier h before) (grow : before≤after) : Frontier h after :=
  ⟨prior.1,fun _ member=>Nat.le_trans (prior.2 _ member) grow⟩
theorem Ordered.nodup {h : List Event} (ordered : Ordered h) : (sessionIds h).Nodup :=
  ordered.imp (fun less=>Nat.ne_of_lt less)
theorem Frontier.hook {h : List Event} {counter : Nat} (prior : Frontier h counter)
    (r : HookJournal.Receipt) : Frontier (h++[.hook r]) counter := by
  have ids : sessionIds (h++[.hook r])=sessionIds h := by
    simp only [sessionIds,List.filterMap_append,List.filterMap_cons,Event.sessionId,List.filterMap_nil,
      List.append_nil]
  simpa only [Frontier,Ordered,ids] using prior
theorem Frontier.session {h : List Event} {r : SessionReceipt}
    (prior : Frontier h r.before.wg.keypairCounter)
    (counter : r.after.wg.keypairCounter=r.before.wg.keypairCounter+(if r.begun then 1 else 0)) :
    Frontier (h++[.session r]) r.after.wg.keypairCounter := by
  cases begun : r.begun with
  | false =>
    simp only [begun,Bool.false_eq_true,ite_false,Nat.add_zero] at counter
    simpa [Frontier,Ordered,sessionIds,Event.sessionId,begun,counter] using prior
  | true =>
    simp only [begun,ite_true] at counter
    change (sessionIds (h++[.session r])).Pairwise (·<·) ∧ _
    have ids : sessionIds (h++[.session r])=sessionIds h++[r.after.wg.keypairCounter] := by
      simp [sessionIds,Event.sessionId,begun]
    rw [ids]
    refine ⟨List.pairwise_append.mpr ⟨prior.1,List.pairwise_singleton _ _,?_⟩,?_⟩
    · intro old member fresh only
      simp only [List.mem_singleton] at only
      subst fresh
      have bound:=prior.2 old member
      omega
    · intro serial member
      rcases List.mem_append.mp member with old|fresh
      · have bound:=prior.2 serial old
        omega
      · simp only [List.mem_singleton] at fresh
        omega

theorem Ordered.session_count {h : List Event} (ordered : Ordered h) (serial : Nat) :
    h.countP (fun e=>e.sessionId==some serial)≤1 := by
  have bound:=List.nodup_iff_count.mp ordered.nodup serial
  simpa only [sessionIds,List.count_filterMap] using bound

theorem Ordered.derived_count {h : List Event} (ordered : Ordered h) (paired : Paired h)
    (serial : Nat) : h.countP (fun e=>e.derivedId==some serial)≤1 := by
  rw [←paired.counts serial]
  exact ordered.session_count serial

end Leanux.Proofs.WG.TimerDiscipline.HandshakeJournal
