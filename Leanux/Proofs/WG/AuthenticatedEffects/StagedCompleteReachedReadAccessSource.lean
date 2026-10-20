import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryKeyFrames

namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ReadAccess
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

inductive Shape : {α : Type} → WG.M α → Type 1 where
  | pure (value : α) : Shape (pure value)
  | read : Shape (get : WG.M WGWorld)
  | ambient (action : AmbientM α) : Shape (monadLift action)
  | bind {body : WG.M α} {next : α → WG.M β} (head : Shape body) (tail : ∀value,Shape (next value)) :
      Shape (body >>= next)

inductive Point : {α : Type} → {action : WG.M α} → Shape action →
    WGWorld → Ambient → WGWorld → Ambient → Prop where
  | entry (source : Shape action) : Point source w a w a
  | returned (source : Shape action) (performed : ((action.run w).run a)=.ok ((value,v),b)) : Point source w a v b
  | left {body : WG.M α} {next : α → WG.M β} {head : Shape body}
      (tail : ∀value,Shape (next value)) (point : Point head w a v b) : Point (.bind head tail) w a v b
  | right {body : WG.M α} {next : α → WG.M β} (head : Shape body) (tail : ∀value,Shape (next value))
      (leading : ((body.run w).run a)=.ok ((value,u),c)) (point : Point (tail value) u c v b) :
      Point (.bind head tail) w a v b

theorem Point.remaining {α : Type} {action : WG.M α} {source : Shape action}
    (point : Point source w a v b) : ∃remaining : WG.M α,((action.run w).run a)=((remaining.run v).run b) := by
  induction point with
  | entry source=>exact ⟨_,rfl⟩
  | returned source performed=>exact ⟨pure _,performed⟩
  | @left α β w a v b body next head tail point ih=>
      obtain ⟨rest,same⟩:=ih
      exact ⟨rest >>= next,by simp only [StateT.run_bind,same]⟩
  | right head tail leading point ih=>
      obtain ⟨rest,same⟩:=ih
      exact ⟨rest,by simp only [StateT.run_bind,leading];exact same⟩

theorem Point.observed_remaining {α E : Type} {action : WG.M α} {source : Shape action}
    {w : World} (point : Point source w.wg w.ambient v b) (h : List E) :
    ∃remaining : PrefixM E α,runPrefix (liftWGObserver (liftWGPrefix action)) w h=
      runPrefix remaining {w with wg:=v,ambient:=b} h := by
  obtain ⟨rest,same⟩:=point.remaining
  refine ⟨liftWGObserver (liftWGPrefix rest),?_⟩
  simp only [liftWGObserver_run,runWGPrefix_lift,same]

macro "readonly_source_step" : tactic => `(tactic| first
  | exact Shape.pure _
  | exact Shape.read
  | exact Shape.ambient _
  | apply Shape.bind
  | maintenance_intro
  | dsimp (config := {failIfUnchanged := true}) only
  | split)

noncomputable def peerShape (pid : PeerId) : Shape (getPeer pid) := by
  simp only [getPeer,getDev,invariant]
  repeat' readonly_source_step

noncomputable def deviceShape : Shape getDev := by
  simp only [getDev,invariant]
  repeat' readonly_source_step

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ReadAccess
