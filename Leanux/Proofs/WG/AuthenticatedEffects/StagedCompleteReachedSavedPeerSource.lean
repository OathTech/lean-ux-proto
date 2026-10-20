import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedAccessCanonical

/-! A saved-peer source permits native reads, Ambient decisions and metadata
writes to that same saved peer. Every write retains its identity and TX queues. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SavedPeer
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

inductive Shape (pid : PeerId) (saved : Peer) : {α : Type} → WG.M α → Type 1 where
  | pure (value : α) : Shape pid saved (pure value)
  | read : Shape pid saved (get : WG.M WGWorld)
  | ambient (body : AmbientM α) : Shape pid saved (monadLift body)
  | write (value : Peer)
      (same : value.internalId=saved.internalId ∧ value.staged=saved.staged ∧ value.txQueue=saved.txQueue) :
      Shape pid saved (setPeer pid value)
  | bind {body : WG.M α} {next : α → WG.M β}
      (head : Shape pid saved body) (tail : ∀value,Shape pid saved (next value)) : Shape pid saved (body >>= next)

inductive Point : {α : Type} → {body : WG.M α} → Shape pid saved body →
    WGWorld → Ambient → WGWorld → Ambient → Prop where
  | entry (source : Shape pid saved body) : Point source w a w a
  | returned (source : Shape pid saved body) (performed : (body.run w).run a=.ok ((value,v),b)) : Point source w a v b
  | left {body : WG.M α} {next : α → WG.M β} {head : Shape pid saved body}
      (tail : ∀value,Shape pid saved (next value)) (point : Point head w a v b) : Point (.bind head tail) w a v b
  | right {body : WG.M α} {next : α → WG.M β}
      (head : Shape pid saved body) (tail : ∀value,Shape pid saved (next value))
      (leading : (body.run w).run a=.ok ((value,u),c)) (point : Point (tail value) u c v b) :
      Point (.bind head tail) w a v b

theorem Point.remaining {α : Type} {body : WG.M α} {source : Shape pid saved body}
    (point : Point source w a v b) : ∃rest : WG.M α,(body.run w).run a=(rest.run v).run b := by
  induction point with
  | entry source=>exact ⟨_,rfl⟩
  | returned source performed=>exact ⟨pure _,performed⟩
  | @left α β pid saved w a v b body next head tail point ih=>
      obtain ⟨rest,same⟩:=ih
      exact ⟨rest >>= next,by simp only [StateT.run_bind,same]⟩
  | right head tail leading point ih=>
      obtain ⟨rest,same⟩:=ih
      exact ⟨rest,by simp only [StateT.run_bind,leading];exact same⟩

macro "saved_peer_source_step" : tactic => `(tactic| first
  | exact Shape.pure _
  | exact Shape.read
  | exact Shape.ambient _
  | (apply Shape.write; exact ⟨rfl,rfl,rfl⟩)
  | apply Shape.bind
  | maintenance_intro
  | dsimp (config := {failIfUnchanged := true}) only
  | split
  | unfold getDev
  | unfold invariant
  | unfold unsupported
  | unfold WG.andM
  | unfold WG.orM)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SavedPeer
