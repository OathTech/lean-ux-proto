import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedProtocolSendComposition

/-! The actual fixture wrapper has one enter, the original body and one
successful exit. Source points keep the original entry token; an internally
stopped body cannot manufacture an exit. The body's point family is supplied
by its fixed source, never by an arbitrary factorization equation. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.FixtureScope
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal
abbrev History := List Event
abbrev BodyPoints := World → History → World → History → Prop

def action (trigger : FixtureEffects.Trigger) (body : WGPrefix Event Unit) : PrefixM Event Unit :=
  liftWGObserver (FixtureEffects.runWith (Driver.fixtureOps hooks) trigger body)

def entered (trigger : FixtureEffects.Trigger) (h : History) : History :=
  h ++ [.scope (.entered ⟨h.length,.fixture trigger⟩)]

def finish (position : Nat) : PrefixM Event Unit := emitPrefix (.scope (.exited position))

theorem source (trigger : FixtureEffects.Trigger) (body : WGPrefix Event Unit) :
    action trigger body = CausalScope.prefixScope Event.scope (.fixture trigger)
      (fun _=>liftWGObserver body) := by
  change liftWGObserver (FixtureEffects.runWith (FixtureEffects.scopeHooks Event.scope CausalSources.Cause.fixture) trigger body)=_
  rw [FixtureEffects.run_scope]
  funext w h
  change runPrefix (liftWGObserver (CausalScope.scope Event.scope (.fixture trigger) body)) w h =
    runPrefix (CausalScope.prefixScope Event.scope (.fixture trigger) (fun _=>liftWGObserver body)) w h
  rw [liftWGObserver_run,CausalScope.scope,CausalScope.withToken_run,CausalScope.prefix_run,liftWGObserver_run]
  cases performed : runWGPrefix body w.wg w.ambient
      (h ++ [.scope (.entered ⟨h.length,.fixture trigger⟩)]) with
  | mk result last=>
    cases result with
    | error reason=>rfl
    | ok pair=>rcases pair with ⟨⟨value,v⟩,a⟩;rfl

theorem after_enter (trigger : FixtureEffects.Trigger) (body : WGPrefix Event Unit)
    (w : World) (h : History) :
    runPrefix (action trigger body) w h=
      runPrefix (liftWGObserver body >>= fun _=>finish h.length) w (entered trigger h) := by
  rw [source,CausalScope.prefix_run,runPrefix_bind]
  simp only [entered]
  cases performed : runPrefix (liftWGObserver body) w
      (h ++ [.scope (.entered ⟨h.length,.fixture trigger⟩)]) with
  | mk result last=>
    cases result with
    | error reason=>rfl
    | ok pair=>rcases pair with ⟨⟨⟩,u⟩;rfl

inductive Point (trigger : FixtureEffects.Trigger) (body : WGPrefix Event Unit)
    (inside : BodyPoints) (w : World) (h : History) : World → History → Prop where
  | entry : Point trigger body inside w h w h
  | entered : Point trigger body inside w h w (FixtureScope.entered trigger h)
  | interior (point : inside w (FixtureScope.entered trigger h) u middle) :
      Point trigger body inside w h u middle
  | exit (performed : runPrefix (liftWGObserver body) w (FixtureScope.entered trigger h)=(.ok ((),u),middle)) :
      Point trigger body inside w h u middle
  | returned (performed : runPrefix (action trigger body) w h=(.ok ((),u),middle)) :
      Point trigger body inside w h u middle

variable {body : WGPrefix Event Unit} {inside : BodyPoints}

theorem Point.remaining
    (bodyRemaining : ∀w h u middle,inside w h u middle →
      ∃remaining : PrefixM Event Unit,runPrefix (liftWGObserver body) w h=runPrefix remaining u middle)
    (point : Point trigger body inside w h u middle) :
    ∃remaining : PrefixM Event Unit,runPrefix (action trigger body) w h=runPrefix remaining u middle := by
  cases point with
  | entry=>exact ⟨_,rfl⟩
  | entered=>exact ⟨_,after_enter trigger body w h⟩
  | interior point=>
    obtain ⟨remaining,continued⟩:=bodyRemaining _ _ _ _ point
    exact ⟨remaining >>= fun _=>finish h.length,(after_enter trigger body w h).trans
      (Scheduler.bind_run_equal _ continued)⟩
  | exit performed=>
    exact ⟨finish h.length,by rw [after_enter,runPrefix_bind,performed]⟩
  | returned performed=>exact ⟨pure (),performed⟩

noncomputable def remainder
    (bodyRemaining : ∀w h u middle,inside w h u middle →
      ∃remaining : PrefixM Event Unit,runPrefix (liftWGObserver body) w h=runPrefix remaining u middle)
    (point : Point trigger body inside w h u middle) : PrefixM Event Unit :=
  Classical.choose (point.remaining bodyRemaining)

theorem remainder_run
    (bodyRemaining : ∀w h u middle,inside w h u middle →
      ∃remaining : PrefixM Event Unit,runPrefix (liftWGObserver body) w h=runPrefix remaining u middle)
    (point : Point trigger body inside w h u middle) :
    runPrefix (action trigger body) w h=runPrefix (remainder bodyRemaining point) u middle :=
  Classical.choose_spec (point.remaining bodyRemaining)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.FixtureScope
