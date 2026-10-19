import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedConsumeLeafPointArm

/-! Refine only the original arm child into its fixed source tree. The wheel
child stays explicit; no hypothesis about the whole arm is used to close it. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Consume.Leaf
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal

def wheelPoints (inside : ChildPoints) : ChildPoints := fun token w h u middle => match token with
  | .arm .. => False
  | .wheel .. => inside token w h u middle

def armPoints (inside : ChildPoints) : ChildPoints := fun token w h u middle => match token with
  | .arm pid timer delay clock => ∃ site, Point (wheelPoints inside) (armShape pid timer delay clock) w h site u middle
  | .wheel .. => inside token w h u middle

variable {native inside : ChildPoints} {Good : History → World → Prop}

noncomputable def wheel_contracts
    (wheel : ∀ pid timer expires clock unit,
      ChildSourceContract native inside Good (.wheel pid timer expires clock unit)) :
    ChildContracts (wheelPoints native) (wheelPoints inside) Good where
  contract := by
    intro token
    cases token with
    | arm pid timer delay clock =>
      exact {
        remainder := fun _ _ _ _ point => False.elim point
        continuation := fun _ _ _ _ point => False.elim point
        coverage := fun _ _ _ _ point => False.elim point
        safe := fun _ _ _ _ _ point => False.elim point }
    | wheel pid timer expires clock unit =>
      let source := wheel pid timer expires clock unit
      exact {
        remainder := source.remainder
        continuation := source.continuation
        coverage := source.coverage
        safe := source.safe }

noncomputable def arm_contract
    (carrierGood : ∀ h w, Carrier h w → Good h w)
    (wheel : ∀ pid timer expires clock unit,
      ChildSourceContract native inside Good (.wheel pid timer expires clock unit))
    (pid : PeerId) (timer : PeerTimer) (delay : Nat) (clock : Option UInt64) :
    ChildSourceContract (armPoints native) (armPoints inside) Good (.arm pid timer delay clock) where
  remainder := fun _ _ _ _ point =>
    Classical.choose ((Classical.choose_spec point).residual (wheel_contracts wheel))
  continuation := by
    intro w h u middle point
    exact (Classical.choose_spec ((Classical.choose_spec point).residual (wheel_contracts wheel))).run
  coverage := by
    intro w h u middle point
    obtain ⟨site,point⟩ := point
    exact ⟨site,point.coverage (wheel_contracts wheel)⟩
  safe := by
    intro w h u middle before point
    obtain ⟨site,point⟩ := point
    exact point.safe carrierGood (wheel_contracts wheel) before

noncomputable def arm_children
    (carrierGood : ∀ h w, Carrier h w → Good h w)
    (wheel : ∀ pid timer expires clock unit,
      ChildSourceContract native inside Good (.wheel pid timer expires clock unit)) :
    ChildContracts (armPoints native) (armPoints inside) Good where
  contract := by
    intro token
    cases token with
    | arm pid timer delay clock => exact arm_contract carrierGood wheel pid timer delay clock
    | wheel pid timer expires clock unit =>
      let source := wheel pid timer expires clock unit
      exact {
        remainder := source.remainder
        continuation := source.continuation
        coverage := source.coverage
        safe := source.safe }

noncomputable def receive_children
    {nativeOther insideOther : Points.ChildPoints}
    (carrierGood : ∀ h w, Carrier h w → Good h w)
    (wheel : ∀ pid timer expires clock unit,
      ChildSourceContract native inside Good (.wheel pid timer expires clock unit))
    (queued : ∀ pid, Points.ChildSourceContract (consumePoints (armPoints native) nativeOther)
      (consumePoints (armPoints inside) insideOther) Good (.queued pid))
    (staging : ∀ pid, Points.ChildSourceContract (consumePoints (armPoints native) nativeOther)
      (consumePoints (armPoints inside) insideOther) Good (.staging pid))
    (release : ∀ peer, Points.ChildSourceContract (consumePoints (armPoints native) nativeOther)
      (consumePoints (armPoints inside) insideOther) Good (.release peer)) :
    Points.ChildContracts (consumePoints (armPoints native) nativeOther)
      (consumePoints (armPoints inside) insideOther) Good :=
  consume_children carrierGood (arm_children carrierGood wheel) queued staging release

theorem arm_cases (pid : PeerId) (timer : PeerTimer) (delay : Nat) (clock : Option UInt64)
    (performed : runPrefix (liftWGObserver (effects.arm pid timer delay clock)) w h = (result,last)) :
    Execution (armShape pid timer delay clock) w h result last :=
  execution_cases _ performed

theorem arm_boundary (pid : PeerId) (timer : PeerTimer) (delay : Nat) (clock : Option UInt64)
    (before : Carrier h w) (point : Point Boundary (armShape pid timer delay clock) w h site u middle) :
    Carrier middle u := boundary_carrier point before

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Consume.Leaf
