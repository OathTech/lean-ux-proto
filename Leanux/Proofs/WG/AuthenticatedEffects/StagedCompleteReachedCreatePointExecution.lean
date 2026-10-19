import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCreatePointCanonical

/-! Normal and stopped executions of the fixed original create tree. A
stopped bind keeps only its real failed child and journal, with no error
world. Successful bind prerequisites use the actual preceding native run. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CreatePoints
open Leanux Leanux.WG Leanux.Proofs.Logged CausalJournal
set_option maxHeartbeats 600000

inductive Execution : {α : Type} → {action : PrefixM Event α} →
    Shape action → World → History → Result α → History → Prop where
  | pure (value : α) : Execution (.pure value) w h (.ok (value,w)) h
  | atom (token : Atom α) (performed : runPrefix token.action w h=(result,last)) :
      Execution (.atom token) w h result last
  | child (token : Child action) (performed : runPrefix action w h=(result,last)) :
      Execution (.child token) w h result last
  | stopped {body : PrefixM Event α} {next : α → PrefixM Event β}
      (head : Shape body) (tail : ∀ value, Shape (next value))
      (leading : Execution head w h (.error reason) last) :
      Execution (.bind head tail) w h (.error reason) last
  | continued {body : PrefixM Event α} {next : α → PrefixM Event β}
      (head : Shape body) (tail : ∀ value, Shape (next value))
      (leading : Execution head w h (.ok (value,u)) middle)
      (remaining : Execution (tail value) u middle result last) :
      Execution (.bind head tail) w h result last
  | marked (label : Label) (trace : Execution shape w h result last) :
      Execution (.marked label shape) w h result last

theorem Execution.run {shape : Shape action} (trace : Execution shape w h result last) :
    runPrefix action w h=(result,last) := by
  induction trace with
  | pure=>rfl
  | atom token performed=>exact performed
  | child token performed=>exact performed
  | stopped head tail leading ih=>rw [runPrefix_bind,ih]
  | continued head tail leading remaining ihLeading ihRemaining=>rw [runPrefix_bind,ihLeading]; exact ihRemaining
  | marked label trace ih=>exact ih

theorem execution_cases (shape : Shape action)
    (performed : runPrefix action w h=(result,last)) : Execution shape w h result last := by
  induction shape generalizing w h last with
  | pure value=>cases performed; exact .pure value
  | atom token=>exact .atom token performed
  | child token=>exact .child token performed
  | bind head tail ihHead ihTail=>
    rw [runPrefix_bind] at performed
    cases leading : runPrefix _ w h with
    | mk out middle=>
      rw [leading] at performed
      cases out with
      | error reason=>cases performed; exact .stopped head tail (ihHead leading)
      | ok pair=>
        obtain ⟨value,u⟩:=pair
        exact .continued head tail (ihHead leading) (ihTail value performed)
  | marked label shape ih=>exact .marked label (ih performed)

theorem execution_iff (shape : Shape action) :
    Execution shape w h result last ↔ runPrefix action w h=(result,last) :=
  ⟨Execution.run,execution_cases shape⟩

theorem create_cases (pid : PeerId) (items : List SkbId) (w : World) (h : History) :
    let actual:=runPrefix (body pid items) w h
    Execution (createShape pid items) w h actual.1 actual.2 := execution_cases _ rfl

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CreatePoints
