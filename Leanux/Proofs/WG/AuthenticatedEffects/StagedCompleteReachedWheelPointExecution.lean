import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedWheelPointFrames

/-! Exact executions of the fixed wheel body. Cache preservation is derived
from the original successful prefix; an error never supplies a returned world. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Wheel.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal

variable {pid : PeerId} {saved : Peer}

theorem Shape.normal (shape : Shape pid saved action) (cache : Cache pid saved w.wg)
    (run : runPrefix action w h = (.ok (value,v),last)) :
    last = h ∧ StagedEntry.view v.wg = StagedEntry.view w.wg ∧ Cache pid saved v.wg := by
  induction shape generalizing w h v last with
  | pure value => cases run; exact ⟨rfl,rfl,cache⟩
  | native token => exact token.normal cache run
  | failed failure next =>
    obtain ⟨reason,stopped⟩ := failure.run w h
    rw [runPrefix_bind,stopped] at run
    cases run
  | bind head tail ihHead ihTail =>
    rw [runPrefix_bind] at run
    cases leading : runPrefix _ w h with
    | mk out middle =>
      rw [leading] at run
      cases out with
      | error reason => cases run
      | ok pair =>
        obtain ⟨x,u⟩ := pair
        have first := ihHead cache leading
        have second := ihTail x first.2.2 run
        exact ⟨second.1.trans first.1,second.2.1.trans first.2.1,second.2.2⟩

inductive Execution : {α : Type} → {action : PrefixM Event α} →
    Shape pid saved action → World → History → Result α → History → Prop where
  | pure (value : α) : Execution (.pure value) w h (.ok (value,w)) h
  | native (token : Native pid saved) {result : Result token.Result}
      (run : runPrefix token.action w h = (result,last)) : Execution (.native token) w h result last
  | failed {α β : Type} {action : PrefixM Event α} (failure : Consume.Leaf.Failure action)
      (next : α → PrefixM Event β) {result : Result β}
      (run : runPrefix (action >>= next) w h = (result,last)) : Execution (.failed failure next) w h result last
  | stopped {action : PrefixM Event α} {next : α → PrefixM Event β}
      (head : Shape pid saved action) (tail : ∀ x, Shape pid saved (next x))
      (leading : Execution head w h (.error reason) last) : Execution (.bind head tail) w h (.error reason) last
  | continued {action : PrefixM Event α} {next : α → PrefixM Event β}
      (head : Shape pid saved action) (tail : ∀ x, Shape pid saved (next x))
      (leading : Execution head w h (.ok (value,u)) middle)
      (remaining : Execution (tail value) u middle result last) : Execution (.bind head tail) w h result last

theorem Execution.run {shape : Shape pid saved action} (execution : Execution shape w h result last) : runPrefix action w h = (result,last) := by
  induction execution with
  | pure value => rfl
  | native token run => exact run
  | failed failure next run => exact run
  | stopped head tail leading ih => rw [runPrefix_bind,ih]
  | continued head tail leading remaining ihLeading ihRemaining => rw [runPrefix_bind,ihLeading]; exact ihRemaining

theorem execution_cases (shape : Shape pid saved action) (run : runPrefix action w h = (result,last)) :
    Execution shape w h result last := by
  induction shape generalizing w h last with
  | pure value => cases run; exact .pure value
  | native token => exact .native token run
  | failed failure next => exact .failed failure next run
  | bind head tail ihHead ihTail =>
    rw [runPrefix_bind] at run
    cases leading : runPrefix _ w h with
    | mk out middle =>
      rw [leading] at run
      cases out with
      | error reason => cases run; exact .stopped head tail (ihHead leading)
      | ok pair =>
        obtain ⟨value,u⟩ := pair
        exact .continued head tail (ihHead leading) (ihTail value run)

theorem execution_iff (shape : Shape pid saved action) :
    Execution shape w h result last ↔ runPrefix action w h = (result,last) :=
  ⟨Execution.run,execution_cases shape⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Wheel.Points
