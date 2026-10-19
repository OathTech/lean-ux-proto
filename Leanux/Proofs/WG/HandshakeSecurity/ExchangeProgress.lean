import Leanux.Proofs.WG.HandshakeSecurity.ExchangeHistory

/-! Fresh native start positions and strictly advancing phases distinguish
repeated exchanges at a reused peer slot. Progress is a history property; the
native tag carrier is proved separately. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.Exchange
open Leanux Leanux.WG Leanux.Proofs.Logged

private theorem rank_le (p : Phase) : p.rank ≤ 2 := by cases p <;> decide

theorem Bounded.mono {n m : Nat} {l : Ledger} (h : Bounded n l) (le : n ≤ m) : Bounded m l :=
  fun pid entry found => ⟨(h pid entry found).1,Nat.le_trans (h pid entry found).2 le⟩

private theorem bounded_set {n : Nat} {l : Ledger} (h : Bounded n l) (pid : PeerId) (p : Phase) :
    Bounded (n+1) (set l pid ⟨n+1,p⟩) := by
  intro target entry found
  by_cases same : target = pid
  · have equal : entry = ⟨n+1,p⟩ := by simpa [set,same] using found.symm
    subst entry
    exact ⟨Nat.zero_lt_succ _,Nat.le_refl _⟩
  · exact h.mono (Nat.le_succ _) target entry (by simpa [set,same] using found)

private theorem bounded_advance {n : Nat} {l : Ledger} (h : Bounded n l) (pid : PeerId) (p : Phase) :
    Bounded n (advance l pid p) := by
  intro target entry found
  by_cases same : target = pid
  · subst target
    obtain ⟨old,ho,equal⟩ := Option.map_eq_some_iff.mp (by simpa [advance] using found)
    subst entry
    exact h pid old ho
  · exact h target entry (by simpa [advance,same] using found)

theorem bounded_transition {n : Nat} {l : Ledger} (h : Bounded n l) (event : Event) :
    Bounded (n+1) (transition n l event) := by
  cases event with
  | createInitiation pid r =>
    cases hr : r.value <;> simp only [transition,hr,Option.isSome_none,Option.isSome_some,Bool.false_eq_true,↓reduceIte]
    · exact h.mono (Nat.le_succ _)
    · exact bounded_set h _ _
  | consumeInitiation msg r =>
    cases hr : r.value <;> simp only [transition,hr]
    · exact h.mono (Nat.le_succ _)
    · exact bounded_set h _ _
  | createResponse pid r =>
    cases hr : r.value <;> simp only [transition,hr,Option.isSome_none,Option.isSome_some,Bool.false_eq_true,↓reduceIte]
    · exact h.mono (Nat.le_succ _)
    · exact (bounded_advance h _ _).mono (Nat.le_succ _)
  | consumeResponse msg r =>
    cases hr : r.value <;> simp only [transition,hr]
    · exact h.mono (Nat.le_succ _)
    · exact (bounded_advance h _ _).mono (Nat.le_succ _)
  | session pid r =>
    cases hr : r.value <;> simp only [transition,hr,Bool.false_eq_true,↓reduceIte]
    · exact h.mono (Nat.le_succ _)
    · exact (bounded_advance h _ _).mono (Nat.le_succ _)

theorem History.bounded {h : List Event} {l : Ledger} (valid : History h l) : Bounded h.length l := by
  induction valid with
  | nil => intro pid entry impossible; cases impossible
  | snoc prior event _ _ ih => simpa only [List.length_append,List.length_singleton] using bounded_transition ih event

theorem score_bound {n : Nat} {l : Ledger} (h : Bounded n l) (pid : PeerId) : l.score pid ≤ 3*n+2 := by
  cases found : l pid with
  | none => simp [Ledger.score,found]
  | some entry =>
    have bound := (h pid entry found).2
    have rank := rank_le entry.phase
    simp only [Ledger.score,found,Option.elim_some,Entry.score]
    omega

private theorem set_increases {n : Nat} {l : Ledger} (h : Bounded n l) (pid : PeerId) (phase : Phase) :
    l.score pid < (set l pid ⟨n+1,phase⟩).score pid := by
  have bound := score_bound h pid
  simp only [Ledger.score,set,↓reduceIte,Option.elim_some,Entry.score]
  change l.score pid < 3*(n+1)+phase.rank
  omega

private theorem advance_increases {l : Ledger} {pid : PeerId} {old next : Phase}
    (h : HasPhase l pid old) (rank : old.rank < next.rank) :
    l.score pid < (advance l pid next).score pid := by
  obtain ⟨entry,found,equal⟩ := h
  simp only [Ledger.score,advance,↓reduceIte,found,Option.map_some,Option.elim_some,Entry.score,equal]
  omega

theorem successful_increases {n : Nat} {l : Ledger} (h : Bounded n l) (event : Event)
    (allowed : Allowed l event) (pid : PeerId) (success : event.peer = some pid) :
    l.score pid < (transition n l event).score pid := by
  cases event with
  | createInitiation peer r =>
    cases hr : r.value with
    | none => simp [Event.peer,hr] at success
    | some msg =>
      have same : peer = pid := by simpa [Event.peer,hr] using success
      subst peer
      simpa [transition,hr] using set_increases h pid .initiationCreated
  | consumeInitiation msg r =>
    change r.value = some pid at success
    simpa [transition,success] using set_increases h pid .initiationConsumed
  | createResponse peer r =>
    cases hr : r.value with
    | none => simp [Event.peer,hr] at success
    | some msg =>
      have same : peer = pid := by simpa [Event.peer,hr] using success
      subst peer
      have prior := allowed (by simp [hr])
      simpa [transition,hr] using advance_increases prior (show Phase.initiationConsumed.rank < Phase.responseCreated.rank by decide)
  | consumeResponse msg r =>
    change r.value = some pid at success
    simpa [transition,success] using advance_increases (allowed pid success)
      (show Phase.initiationCreated.rank < Phase.responseConsumed.rank by decide)
  | session peer r =>
    cases hr : r.value with
    | false => simp [Event.peer,hr] at success
    | true =>
      have same : peer = pid := by simpa [Event.peer,hr] using success
      subst peer
      rcases allowed hr with created | consumed
      · simpa [transition,hr] using advance_increases created (show Phase.responseCreated.rank < Phase.installed.rank by decide)
      · simpa [transition,hr] using advance_increases consumed (show Phase.responseConsumed.rank < Phase.installed.rank by decide)

theorem transition_other (n : Nat) (l : Ledger) (event : Event) (pid : PeerId)
    (different : event.peer ≠ some pid) : transition n l event pid = l pid := by
  cases event <;> rename_i arg r <;> cases hr : r.value <;>
    simp_all [Event.peer,transition,set,advance]
  all_goals intro same; exact False.elim (different same.symm)

theorem transition_mono {n : Nat} {l : Ledger} (h : Bounded n l) (event : Event)
    (allowed : Allowed l event) (pid : PeerId) : l.score pid ≤ (transition n l event).score pid := by
  by_cases success : event.peer = some pid
  · exact Nat.le_of_lt (successful_increases h event allowed pid success)
  · simp only [Ledger.score,transition_other n l event pid success]
    exact Nat.le_refl _

end Leanux.Proofs.WG.HandshakeSecurity.Exchange
