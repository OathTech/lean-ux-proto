import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSkbAccessSource

/-! RX access syntax expands the packet-store adapter and atomic world accesses, retaining the actual remaining native computation. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.RxAccess
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

inductive Shape : {α : Type} → WG.M α → Type 1 where
  | access (source : Access.Shape action) : Shape action
  | skb (action : SkbM α) (frame : SameView StagedEntry.view (liftSkb action)) : Shape (liftSkb action)
  | bind {body : WG.M α} {next : α → WG.M β} (head : Shape body) (tail : ∀value,Shape (next value)) : Shape (body >>= next)

inductive Point : {α : Type} → {action : WG.M α} → Shape action →
    WGWorld → Ambient → WGWorld → Ambient → Prop where
  | entry (source : Shape action) : Point source w a w a
  | returned (source : Shape action) (performed : ((action.run w).run a)=.ok ((value,v),b)) : Point source w a v b
  | access (point : Access.Point source w a v b) : Point (.access source) w a v b
  | skb (frame : SameView StagedEntry.view (liftSkb action)) (point : SkbAccess.Point action w a v b) :
      Point (.skb action frame) w a v b
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
  | access point=>exact point.remaining
  | skb frame point=>exact point.remaining
  | @left α β w a v b body next head tail point ih=>
      obtain ⟨rest,same⟩:=ih
      exact ⟨rest >>= next,by simp only [StateT.run_bind,same]⟩
  | right head tail leading point ih=>
      obtain ⟨rest,same⟩:=ih
      exact ⟨rest,by simp only [StateT.run_bind,leading];exact same⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.RxAccess
