import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCryptPollPointFrames

/-! A closed fixed-source point family for ring polling. A right point uses
the actual successful left run; a later Stop does not invalidate earlier cuts.
No arbitrary factorization or incoming coverage certificate creates a point. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CryptPoll.Points
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal CompleteCarrier

inductive Site where
  | entry | returned | device
  | left (site : Site)
  | right (site : Site)

inductive Point : {α : Type} → {action : PrefixM Event α} → Shape action →
    World → History → Site → World → History → Prop where
  | entry (shape : Shape action) : Point shape w h .entry w h
  | returned (shape : Shape action) (performed : runPrefix action w h = (.ok (value,u),middle)) :
      Point shape w h .returned u middle
  | device {w : World} (point : ReadAccess.Point ReadAccess.deviceShape w.wg w.ambient v b) :
      Point (.native .device) w h .device {w with wg:=v,ambient:=b} h
  | left {body : PrefixM Event α} {next : α → PrefixM Event β} {head : Shape body}
      (tail : ∀value,Shape (next value)) (point : Point head w h site u middle) :
      Point (.bind head tail) w h (.left site) u middle
  | right {body : PrefixM Event α} {next : α → PrefixM Event β}
      (head : Shape body) (tail : ∀value,Shape (next value))
      (leading : runPrefix body w h = (.ok (value,u),middle))
      (point : Point (tail value) u middle site v last) :
      Point (.bind head tail) w h (.right site) v last

theorem Point.accounted (point : Point shape w h site u middle)
    (before : Accounted h ledger debts locals w.wg) : Accounted middle ledger debts locals u.wg := by
  induction point with
  | entry shape => exact before
  | device point => exact before.same_view point.frame
  | returned shape performed => exact shape.accounted before performed
  | left tail point ih => exact ih before
  | right head tail leading point ih => exact ih (head.accounted before leading)

theorem Point.remaining {action : PrefixM Event α} {shape : Shape action}
    (point : Point shape w h site u middle) :
    ∃remaining,runPrefix action w h = runPrefix remaining u middle := by
  induction point with
  | entry shape => exact ⟨_,rfl⟩
  | device point => exact ⟨_,ProductRead.remainder_run _ (.wg point)⟩
  | returned shape performed => exact ⟨pure _,performed.trans (runPrefix_pure _ _ _).symm⟩
  | left tail point ih =>
      rename_i body next head
      obtain ⟨remaining,continued⟩ := ih
      exact ⟨remaining >>= next,by simp only [runPrefix_bind,continued]⟩
  | right head tail leading point ih =>
      obtain ⟨remaining,continued⟩ := ih
      exact ⟨remaining,by rw [runPrefix_bind,leading]; exact continued⟩

inductive Execution : {α : Type} → {action : PrefixM Event α} → Shape action →
    World → History → Result α → History → Prop where
  | pure (value : α) : Execution (.pure value) w h (.ok (value,w)) h
  | native (token : Native) {result : Result token.Result}
      (performed : runPrefix token.action w h = (result,last)) :
      Execution (.native token) w h result last
  | stopped {body : PrefixM Event α} {next : α → PrefixM Event β} {head : Shape body}
      (tail : ∀value,Shape (next value)) (first : Execution head w h (.error reason) last) :
      Execution (.bind head tail) w h (.error reason) last
  | continued {body : PrefixM Event α} {next : α → PrefixM Event β}
      {head : Shape body} {tail : ∀value,Shape (next value)}
      (first : Execution head w h (.ok (value,u)) middle)
      (rest : Execution (tail value) u middle result last) :
      Execution (.bind head tail) w h result last

theorem Execution.run {action : PrefixM Event α} {shape : Shape action}
    (execution : Execution shape w h result last) :
    runPrefix action w h = (result,last) := by
  induction execution with
  | pure value => rfl
  | native token performed => exact performed
  | stopped tail first ih => simp only [runPrefix_bind,ih]
  | continued first rest ihFirst ihRest => rw [runPrefix_bind,ihFirst]; exact ihRest

theorem execution_cases {action : PrefixM Event α} (shape : Shape action)
    (performed : runPrefix action w h = (result,last)) : Execution shape w h result last := by
  induction shape generalizing w h last with
  | pure value => cases performed; exact .pure value
  | native token => exact .native token performed
  | bind head tail ihHead ihTail =>
      rename_i body next
      rw [runPrefix_bind] at performed
      cases leading : runPrefix body w h with
      | mk first middle =>
        cases first with
        | error reason => simp only [leading] at performed; cases performed; exact .stopped tail (ihHead leading)
        | ok pair =>
          obtain ⟨value,u⟩ := pair
          simp only [leading] at performed
          exact .continued (ihHead leading) (ihTail value performed)

def RootPoints (w : World) (h : History) (u : World) (middle : History) : Prop :=
  ∃site,Point canonical w h site u middle

noncomputable def remainder (w : World) (h : History) (u : World) (middle : History)
    (point : RootPoints w h u middle) : PrefixM Event (Option (List SkbId)) :=
  Classical.choose (Classical.choose_spec point).remaining

theorem remainder_run (point : RootPoints w h u middle) :
    runPrefix hooks.poll w h = runPrefix (remainder w h u middle point) u middle :=
  Classical.choose_spec (Classical.choose_spec point).remaining

/-- Polling neither duplicates nor disposes a packet obligation. Every fixed
source point retains the same ledger and literal original continuation. -/
theorem source_accounted (before : Accounted h ledger debts locals w.wg)
    (point : RootPoints w h u middle) :
    Accounted middle ledger debts locals u.wg ∧
      runPrefix hooks.poll w h = runPrefix (remainder w h u middle point) u middle :=
  ⟨(Classical.choose_spec point).accounted before,remainder_run point⟩

theorem source_cases (performed : runPrefix hooks.poll w h = (result,last)) :
    Execution canonical w h result last := execution_cases canonical performed

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CryptPoll.Points
