import Leanux.Proofs.WG.HandshakeSecurity.StagedConservationCompletionSource

/-! Forward progress of the actual completion loop, including stopped local
packets. A completed iteration is an execution witness, not by itself a claim
that a socket accepted the packet; terminal attribution uses its send result. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.StagedConservation.CompletionFrontier
open Leanux Leanux.WG Leanux.Proofs.Logged AuthenticatedEffects

/-- The same ordered item is traversed with the actual intermediate world,
history and data-sent flag at every iteration. -/
inductive Steps (o : CompletionEffects.Ops E) (pid : PeerId) :
    List SkbId → Bool → World → List E → Bool → World → List E → Prop
  | nil : Steps o pid [] flag w h flag w h
  | cons {id : SkbId} (run : runPrefix (iteration o pid id flag) w h = (.ok (next,v),tail))
      (rest : Steps o pid ids next v tail final last history) :
      Steps o pid (id :: ids) flag w h final last history

theorem Steps.run (steps : Steps o pid item flag w h final v tail) :
    runPrefix (walk o pid item flag) w h = (.ok (final,v),tail) := by
  induction steps with
  | nil => rfl
  | cons first _ ih => rw [walk_cons,runPrefix_bind,first]; exact ih

theorem walk_normal (o : CompletionEffects.Ops E) (pid : PeerId) (item : List SkbId)
    (flag final : Bool) (w v : World) (h tail : List E)
    (run : runPrefix (walk o pid item flag) w h = (.ok (final,v),tail)) :
    Steps o pid item flag w h final v tail := by
  induction item generalizing flag w h with
  | nil =>
    simp only [walk_nil,runPrefix_pure,Prod.mk.injEq,Except.ok.injEq] at run
    obtain ⟨⟨rfl,rfl⟩,rfl⟩ := run
    exact .nil
  | cons id ids ih =>
    rw [walk_cons,runPrefix_bind] at run
    cases first : runPrefix (iteration o pid id flag) w h with
    | mk result history =>
      cases result with
      | error stop => simp [first] at run
      | ok out =>
        rcases out with ⟨next,middle⟩
        simp only [first] at run
        exact .cons first (ih next middle history run)

/-- A stopped walk has one exact current native iteration. Every preceding
iteration completed, and the remaining suffix was never entered. -/
theorem walk_stopped (o : CompletionEffects.Ops E) (pid : PeerId) (item : List SkbId)
    (flag : Bool) (w : World) (h tail : List E) (stop : Stop)
    (run : runPrefix (walk o pid item flag) w h = (.error stop,tail)) :
    ∃ done id remaining current middle history,
      item = done ++ id :: remaining ∧
      Steps o pid done flag w h current middle history ∧
      runPrefix (iteration o pid id current) middle history = (.error stop,tail) := by
  induction item generalizing flag w h with
  | nil => simp [walk_nil] at run
  | cons id ids ih =>
    rw [walk_cons,runPrefix_bind] at run
    cases first : runPrefix (iteration o pid id flag) w h with
    | mk result history =>
      cases result with
      | error failed =>
        simp only [first,Prod.mk.injEq,Except.error.injEq] at run
        obtain ⟨rfl,rfl⟩ := run
        exact ⟨[],id,ids,flag,w,h,rfl,.nil,first⟩
      | ok out =>
        rcases out with ⟨next,middle⟩
        simp only [first] at run
        obtain ⟨done,current,remaining,last,state,events,split,steps,failed⟩ :=
          ih next middle history run
        exact ⟨id :: done,current,remaining,last,state,events,
          by simp only [split,List.cons_append],.cons first steps,failed⟩

/-- Stops in the completion prelude and final timer suffix are kept distinct
from a stopped packet iteration. The final case has traversed the whole item. -/
inductive Stopped (o : CompletionEffects.Ops E) (pid : PeerId) (item : List SkbId)
    (w : World) (h : List E) (stop : Stop) (tail : List E) : Prop
  | prelude (run : runPrefix (before o pid item) w h = (.error stop,tail)) :
      Stopped o pid item w h stop tail
  | current {id : SkbId} (entered : runPrefix (before o pid item) w h = (.ok ((),start),initial))
      (split : item = done ++ id :: remaining)
      (steps : Steps o pid done false start initial flag middle history)
      (run : runPrefix (iteration o pid id flag) middle history = (.error stop,tail)) :
      Stopped o pid item w h stop tail
  | final (entered : runPrefix (before o pid item) w h = (.ok ((),start),initial))
      (steps : Steps o pid item false start initial flag middle history)
      (run : runPrefix (after o pid flag) middle history = (.error stop,tail)) :
      Stopped o pid item w h stop tail

/-- Every stopped native completion has a forward frontier, without an
incoming reachability hypothesis or an inference from queue disappearance. -/
theorem complete_stopped (o : CompletionEffects.Ops E) (pid : PeerId) (item : List SkbId)
    (w : World) (h tail : List E) (stop : Stop)
    (run : runPrefix (CompletionEffects.completeWith o pid item) w h = (.error stop,tail)) :
    Stopped o pid item w h stop tail := by
  rw [complete_factor,runPrefix_bind] at run
  cases enter : runPrefix (before o pid item) w h with
  | mk result initial =>
    cases result with
    | error failed =>
      simp only [enter,Prod.mk.injEq,Except.error.injEq] at run
      obtain ⟨rfl,rfl⟩ := run
      exact .prelude enter
    | ok out =>
      rcases out with ⟨⟨⟩,start⟩
      simp only [enter] at run
      rw [runPrefix_bind] at run
      cases walkRun : runPrefix (walk o pid item false) start initial with
      | mk result history =>
        cases result with
        | error failed =>
          simp only [walkRun,Prod.mk.injEq,Except.error.injEq] at run
          obtain ⟨rfl,rfl⟩ := run
          obtain ⟨done,id,remaining,flag,middle,events,split,steps,failed⟩ :=
            walk_stopped o pid item false start initial _ _ walkRun
          exact .current enter split steps failed
        | ok out =>
          rcases out with ⟨flag,middle⟩
          simp only [walkRun] at run
          exact .final enter (walk_normal o pid item false flag start middle initial history walkRun) run

/-- Normal completion traverses the whole native item and runs the actual
final suffix. This does not classify either true or false sends as an extra
terminal event. -/
theorem complete_normal (o : CompletionEffects.Ops E) (pid : PeerId) (item : List SkbId)
    (w v : World) (h tail : List E)
    (run : runPrefix (CompletionEffects.completeWith o pid item) w h = (.ok ((),v),tail)) :
    ∃ start initial flag middle history,
      runPrefix (before o pid item) w h = (.ok ((),start),initial) ∧
      Steps o pid item false start initial flag middle history ∧
      runPrefix (after o pid flag) middle history = (.ok ((),v),tail) := by
  rw [complete_factor,runPrefix_bind] at run
  cases enter : runPrefix (before o pid item) w h with
  | mk result initial =>
    cases result with
    | error failed => simp [enter] at run
    | ok out =>
      rcases out with ⟨⟨⟩,start⟩
      simp only [enter] at run
      rw [runPrefix_bind] at run
      cases walkRun : runPrefix (walk o pid item false) start initial with
      | mk result history =>
        cases result with
        | error failed => simp [walkRun] at run
        | ok out =>
          rcases out with ⟨flag,middle⟩
          simp only [walkRun] at run
          exact ⟨start,initial,flag,middle,history,rfl,
            walk_normal o pid item false flag start middle initial history walkRun,run⟩

end Leanux.Proofs.WG.HandshakeSecurity.StagedConservation.CompletionFrontier
