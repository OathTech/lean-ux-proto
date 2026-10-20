import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedReadAccessSource

/-! Getter source syntax admits only reads, pure steps and fixed failures.
Both WG and Ambient state are consequently retained at every declared cut. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ReadGetter
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues

inductive Shape : {α : Type} → WG.M α → Type 1 where
  | pure (value : α) : Shape (pure value)
  | read : Shape (get : WG.M WGWorld)
  | invariant (message : String) : Shape (Leanux.invariant message : WG.M α)
  | unsupported (message : String) : Shape (Leanux.unsupported message : WG.M α)
  | bind {body : WG.M α} {next : α → WG.M β}
      (head : Shape body) (tail : ∀ value,Shape (next value)) : Shape (body >>= next)

inductive Point : {α : Type} → {action : WG.M α} → Shape action →
    WGWorld → Ambient → WGWorld → Ambient → Prop where
  | entry (source : Shape action) : Point source w a w a
  | returned (source : Shape action) (performed : (action.run w).run a=.ok ((value,v),b)) :
      Point source w a v b
  | left {body : WG.M α} {next : α → WG.M β} {head : Shape body}
      (tail : ∀ value,Shape (next value)) (point : Point head w a v b) : Point (.bind head tail) w a v b
  | right {body : WG.M α} {next : α → WG.M β} (head : Shape body)
      (tail : ∀ value,Shape (next value)) (leading : (body.run w).run a=.ok ((value,u),c))
      (point : Point (tail value) u c v b) : Point (.bind head tail) w a v b

def device : Shape getDev := by
  unfold getDev
  apply Shape.bind .read
  intro w
  cases w.dev with
  | some d => exact .pure d
  | none => exact .invariant _

def peer (pid : PeerId) : Shape (getPeer pid) := by
  unfold getPeer
  apply Shape.bind device
  intro d
  cases d.peers.get? pid with
  | some p => exact .pure p
  | none => exact .invariant _

def key (kid : KeypairId) : Shape (getKeypair kid) := by
  unfold getKeypair
  apply Shape.bind device
  intro d
  cases d.keypairs.get? kid with
  | some k => exact .pure k
  | none => exact .invariant _

def owner (kid : KeypairId) : Shape (IndexOwner.peerDeref (.keypair kid)) := by
  unfold IndexOwner.peerDeref IndexOwner.peerWord
  apply Shape.bind (.bind (key kid) (fun k=>.pure k.peer))
  intro pointer
  cases pointer with
  | some pid => exact .pure pid
  | none => exact .unsupported _

theorem Point.remaining {α : Type} {action : WG.M α} {source : Shape action}
    (point : Point source w a v b) : ∃ rest : WG.M α,(action.run w).run a=(rest.run v).run b := by
  induction point with
  | entry source => exact ⟨_,rfl⟩
  | returned source performed => exact ⟨pure _,performed⟩
  | @left α β w a v b body next head tail point ih =>
      obtain ⟨rest,same⟩ := ih
      exact ⟨rest >>= next,by simp only [StateT.run_bind,same]⟩
  | right head tail leading point ih =>
      obtain ⟨rest,same⟩ := ih
      exact ⟨rest,by simp only [StateT.run_bind,leading];exact same⟩

noncomputable def prefixRemainder {α E : Type} {action : WG.M α} {source : Shape action}
    (point : Point source w a v b) : WGPrefix E α :=
  liftWGPrefix (Classical.choose point.remaining)

theorem prefixRemainder_run {α E : Type} {action : WG.M α} {source : Shape action}
    (h : List E) (point : Point source w a v b) :
    runWGPrefix (liftWGPrefix action) w a h=runWGPrefix (prefixRemainder point) v b h := by
  simp only [prefixRemainder,runWGPrefix_lift]
  exact congrArg (fun out=>(out,h)) (Classical.choose_spec point.remaining)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ReadGetter
