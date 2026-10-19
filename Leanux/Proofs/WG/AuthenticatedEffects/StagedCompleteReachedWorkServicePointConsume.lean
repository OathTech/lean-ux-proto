import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedWorkServicePointCoverage

/-! The receive queued child is replaced structurally by the fixed queued
source. Only original staging and peer repayment stay with the caller;
flushed protocol sending is not a dependency of queued initiation. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.WorkService.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal

abbrev ReleasePoints := Option PeerId → World → History → World → History → Prop

def releasePoints (inside : ReleasePoints) : ChildPoints := fun token w h u middle => match token with
  | .release peer => inside peer w h u middle
  | .flushedSend _ => False

noncomputable def release_contracts {native inside : ReleasePoints} {Good : History → World → Prop}
    (release : ∀ peer, ChildSourceContract (releasePoints native) (releasePoints inside) Good (.release peer)) :
    ChildContracts (releasePoints native) (releasePoints inside) Good where
  contract := by
    intro token
    cases token with
    | release peer => exact release peer
    | flushedSend pid =>
      exact {
        remainder := fun _ _ _ _ point => False.elim point
        continuation := fun _ _ _ _ point => False.elim point
        coverage := fun _ _ _ _ point => False.elim point
        safe := fun _ _ _ _ _ point => False.elim point }

def otherPoints (work : ChildPoints) (other : Consume.Points.ChildPoints) : Consume.Points.ChildPoints :=
  fun token w h u middle => match token with
  | .queued pid => ∃ site, Point work (queuedShape pid false) w h site u middle
  | _ => other token w h u middle

abbrev consumePoints (work : ChildPoints) (other : Consume.Points.ChildPoints) : Consume.Points.ChildPoints :=
  Wheel.Points.consumePoints (otherPoints work other)

noncomputable def queued_contract {native inside : ChildPoints} {Good : History → World → Prop}
    {nativeOther insideOther : Consume.Points.ChildPoints}
    (carrierGood : ∀ h w, Carrier h w → Good h w) (children : ChildContracts native inside Good)
    (pid : PeerId) : Consume.Points.ChildSourceContract (consumePoints native nativeOther)
      (consumePoints inside insideOther) Good (.queued pid) where
  remainder := fun _ _ _ _ point => Classical.choose ((Classical.choose_spec point).residual children)
  continuation := by
    intro w h u middle point
    exact (Classical.choose_spec ((Classical.choose_spec point).residual children)).run
  coverage := by
    intro w h u middle point
    obtain ⟨site,point⟩ := point
    exact ⟨site,point.coverage children⟩
  safe := by
    intro w h u middle before point
    obtain ⟨site,point⟩ := point
    exact point.safe carrierGood children before

noncomputable def receive_children {native inside : ChildPoints} {Good : History → World → Prop}
    {nativeOther insideOther : Consume.Points.ChildPoints}
    (carrierGood : ∀ h w, Carrier h w → Good h w) (children : ChildContracts native inside Good)
    (staging : ∀ pid, Consume.Points.ChildSourceContract (consumePoints native nativeOther)
      (consumePoints inside insideOther) Good (.staging pid))
    (release : ∀ peer, Consume.Points.ChildSourceContract (consumePoints native nativeOther)
      (consumePoints inside insideOther) Good (.release peer)) :
    Consume.Points.ChildContracts (consumePoints native nativeOther) (consumePoints inside insideOther) Good :=
  Wheel.Points.receive_children carrierGood (queued_contract carrierGood children) staging release

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.WorkService.Points
