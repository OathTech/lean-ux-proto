import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedWheelPointCoverage

/-! The wheel child is now a concrete fixed source family. The receive join
requires only its distinct queued, staging and peer-release children. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Wheel.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal

def children : Consume.Leaf.ChildPoints := fun token w h u middle => match token with
  | .arm .. => False
  | .wheel pid timer expires clock unit => ∃ site, SourcePoint pid timer expires clock unit w h site u middle

noncomputable def wheel_contract {Good : History → World → Prop}
    (carrierGood : ∀ h w, Consume.Leaf.Carrier h w → Good h w)
    (pid : PeerId) (timer : PeerTimer) (expires clock : UInt64) (unit : Option Nat) :
    Consume.Leaf.ChildSourceContract children children Good (.wheel pid timer expires clock unit) where
  remainder := fun _ _ _ _ point => Classical.choose ((Classical.choose_spec point).residual)
  continuation := by
    intro w h u middle point
    exact (Classical.choose_spec ((Classical.choose_spec point).residual)).run
  coverage := fun _ _ _ _ point => point
  safe := by
    intro w h u middle before point
    obtain ⟨site,point⟩ := point
    exact carrierGood _ _ (point.carrier before)

abbrev consumePoints (other : Consume.Points.ChildPoints) : Consume.Points.ChildPoints :=
  Consume.Leaf.consumePoints (Consume.Leaf.armPoints children) other

noncomputable def receive_children {Good : History → World → Prop}
    {nativeOther insideOther : Consume.Points.ChildPoints}
    (carrierGood : ∀ h w, Consume.Leaf.Carrier h w → Good h w)
    (queued : ∀ pid, Consume.Points.ChildSourceContract (consumePoints nativeOther)
      (consumePoints insideOther) Good (.queued pid))
    (staging : ∀ pid, Consume.Points.ChildSourceContract (consumePoints nativeOther)
      (consumePoints insideOther) Good (.staging pid))
    (release : ∀ peer, Consume.Points.ChildSourceContract (consumePoints nativeOther)
      (consumePoints insideOther) Good (.release peer)) :
    Consume.Points.ChildContracts (consumePoints nativeOther) (consumePoints insideOther) Good :=
  Consume.Leaf.receive_children carrierGood (wheel_contract carrierGood) queued staging release

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Wheel.Points
