import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedReadGetterFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryAllocatedFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryQueuedFrames

/-! Fixed metadata source steps preserve packet contents and allocation
geometry. Peer updates retain the same invocation's actual getter result. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.AccountMetadata
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

def view (w : WGWorld) := (StagedEntry.view w,identityView w,allocationMetadata w)

inductive Shape : {α : Type} → WG.M α → Type 1 where
  | pure (value : α) : Shape (pure value)
  | reading (source : ReadGetter.Shape body) : Shape body
  | ambient (body : AmbientM α) : Shape (monadLift body)
  | write (update : WGWorld → WGWorld) (same : ∀ w,view (update w)=view w) : Shape (modify update)
  | update (pid : PeerId) (f : Peer → Peer)
      (same : ∀ p,(f p).internalId=p.internalId ∧ (f p).staged=p.staged ∧ (f p).txQueue=p.txQueue) :
      Shape (getPeer pid >>= fun p=>setPeer pid (f p))
  | bind {body : WG.M α} {next : α → WG.M β}
      (head : Shape body) (tail : ∀ value,Shape (next value)) : Shape (body >>= next)

inductive Point : {α : Type} → {action : WG.M α} → Shape action →
    WGWorld → Ambient → WGWorld → Ambient → Prop where
  | entry (source : Shape action) : Point source w a w a
  | returned (source : Shape action) (performed : (action.run w).run a=.ok ((value,v),b)) :
      Point source w a v b
  | reading (point : ReadGetter.Point source w a v b) : Point (.reading source) w a v b
  | updateRead (same : ∀ p,(f p).internalId=p.internalId ∧ (f p).staged=p.staged ∧ (f p).txQueue=p.txQueue)
      (point : ReadGetter.Point (ReadGetter.peer pid) w a v b) : Point (.update pid f same) w a v b
  | left {body : WG.M α} {next : α → WG.M β} {head : Shape body}
      (tail : ∀ value,Shape (next value)) (point : Point head w a v b) : Point (.bind head tail) w a v b
  | right {body : WG.M α} {next : α → WG.M β} (head : Shape body)
      (tail : ∀ value,Shape (next value)) (leading : (body.run w).run a=.ok ((value,u),c))
      (point : Point (tail value) u c v b) : Point (.bind head tail) w a v b

theorem Point.remaining {α : Type} {action : WG.M α} {source : Shape action}
    (point : Point source w a v b) : ∃ rest : WG.M α,(action.run w).run a=(rest.run v).run b := by
  induction point with
  | entry source => exact ⟨_,rfl⟩
  | returned source performed => exact ⟨pure _,performed⟩
  | reading point => exact point.remaining
  | @updateRead f pid w a v b same point =>
      obtain ⟨rest,run⟩ := point.remaining
      exact ⟨rest >>= fun p=>setPeer pid (f p),by simp only [StateT.run_bind,run]⟩
  | @left α β w a v b body next head tail point ih =>
      obtain ⟨rest,same⟩ := ih
      exact ⟨rest >>= next,by simp only [StateT.run_bind,same]⟩
  | right head tail leading point ih =>
      obtain ⟨rest,same⟩ := ih
      exact ⟨rest,by simp only [StateT.run_bind,leading];exact same⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.AccountMetadata
