import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedRoutingListSource

namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Routing
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

inductive Shape : {α : Type} → WG.M α → Type 1 where
  | metadata (source : PeerMetadata.Shape action) : Shape action
  | delete (node : NodeId) : Shape (listDel node)
  | bind {body : WG.M α} {next : α → WG.M β} (head : Shape body) (tail : ∀value,Shape (next value)) : Shape (body >>= next)

noncomputable def conditionalShape (test : Prop) [Decidable test] {left right : WG.M α}
    (yes : test → Shape left) (no : ¬test → Shape right) : Shape (if test then left else right) := by
  split
  · exact yes ‹_›
  · exact no ‹_›

noncomputable def listShape (xs : List ι) (initial : σ) (body : ι → σ → WG.M (ForInStep σ))
    (shapes : ∀value acc,Shape (body value acc)) : Shape (forIn xs initial body) :=
  List.rec (motive:=fun values=>∀acc,Shape (forIn values acc body))
    (fun acc=>.metadata (.access (.pure acc)))
    (fun value rest ih acc=>(List.forIn_cons body value rest acc).symm ▸
      Shape.bind (shapes value acc) (fun decision=>match decision with
        | .done final=>.metadata (.access (.pure final))
        | .yield next=>ih next)) xs initial

noncomputable def rangeShape (range : Std.Legacy.Range) (initial : σ)
    (body : Nat → σ → WG.M (ForInStep σ)) (shapes : ∀value acc,Shape (body value acc)) : Shape (forIn range initial body) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact listShape _ _ _ shapes

inductive Point : {α : Type} → {action : WG.M α} → Shape action →
    WGWorld → Ambient → WGWorld → Ambient → Prop where
  | entry (source : Shape action) : Point source w a w a
  | returned (source : Shape action) (performed : ((action.run w).run a)=.ok ((value,v),b)) : Point source w a v b
  | metadata (point : PeerMetadata.Point source w a v b) : Point (.metadata source) w a v b
  | delete (point : RoutingList.Point node w a v b) : Point (.delete node) w a v b
  | left {body : WG.M α} {next : α → WG.M β} {head : Shape body}
      (tail : ∀value,Shape (next value)) (point : Point head w a v b) : Point (.bind head tail) w a v b
  | right {body : WG.M α} {next : α → WG.M β} (head : Shape body) (tail : ∀value,Shape (next value))
      (leading : ((body.run w).run a)=.ok ((value,u),c)) (point : Point (tail value) u c v b) : Point (.bind head tail) w a v b

theorem Point.remaining {α : Type} {action : WG.M α} {source : Shape action}
    (point : Point source w a v b) : ∃remaining : WG.M α,((action.run w).run a)=((remaining.run v).run b) := by
  induction point with
  | entry source=>exact ⟨_,rfl⟩
  | returned source performed=>exact ⟨pure _,performed⟩
  | metadata point=>exact point.remaining
  | delete point=>exact point.remaining
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

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Routing
