import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTimerPointZeroSource

/-! Zero-key points include its actual pre-repayment source subtree. The
only deeper child is raw peerPut at the same invocation's acquired loan. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Timer.Points.Zero
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal
abbrev RawPoints := PeerId → World → History → World → History → Prop

inductive Point (raw : RawPoints) (pid : PeerId) : World → History → World → History → Prop where
  | entry : Point raw pid w h w h
  | beforeCut (point : WorkService.Points.Point (WorkService.Points.releasePoints (fun _ _ _ _ _ => False))
      (beforeShape pid) w h site u middle) : Point raw pid w h u middle
  | repayment (leading : runPrefix (wg (beforeRepay pid)) w h = (.ok (true,u),middle))
      (point : raw pid u middle v last) : Point raw pid w h v last
  | returned (performed : runPrefix (wg (expiredZeroKeyMaterial pid)) w h = (.ok ((),u),middle)) :
      Point raw pid w h u middle

noncomputable def quietChildren : WorkService.Points.ChildContracts
    (WorkService.Points.releasePoints (fun _ _ _ _ _ => False))
    (WorkService.Points.releasePoints (fun _ _ _ _ _ => False)) Carrier :=
  WorkService.Points.release_contracts (fun _ => {
    remainder := fun _ _ _ _ point => False.elim point
    continuation := fun _ _ _ _ point => False.elim point
    coverage := fun _ _ _ _ point => False.elim point
    safe := fun _ _ _ _ _ point => False.elim point })

/-- The raw release contract is contextual: its entry is the successful
borrow/test prefix of this zero timer. It is not a frame for arbitrary put. -/
structure ReleaseContract (raw : RawPoints) (Good : History → World → Prop) where
  remainder : ∀ pid u middle v last, raw pid u middle v last → PrefixM Event Unit
  continuation : ∀ pid u middle v last (point : raw pid u middle v last),
    runPrefix (wg (peerPut (some pid))) u middle = runPrefix (remainder pid u middle v last point) v last
  safe : ∀ pid w h u middle v last, Carrier h w →
    runPrefix (wg (beforeRepay pid)) w h = (.ok (true,u),middle) →
    raw pid u middle v last → Good last v

theorem remainder_exists (child : ReleaseContract raw Good) (point : Point raw pid w h u middle) :
    ∃ rest : PrefixM Event Unit,
      runPrefix (wg (expiredZeroKeyMaterial pid)) w h = runPrefix rest u middle := by
  cases point with
  | entry => exact ⟨_,rfl⟩
  | beforeCut point =>
    obtain ⟨rest,residual⟩ := point.residual quietChildren
    refine ⟨rest >>= fun repay => wg (afterRepay pid repay),?_⟩
    rw [product_factor]
    exact Scheduler.bind_run_equal _ residual.run
  | repayment leading point =>
    refine ⟨child.remainder _ _ _ _ _ point,?_⟩
    rw [product_factor,runPrefix_bind,leading]
    exact child.continuation _ _ _ _ _ point
  | returned performed => exact ⟨pure (),performed.trans (runPrefix_pure _ _ _).symm⟩

noncomputable def remainder (child : ReleaseContract raw Good) (point : Point raw pid w h u middle) : PrefixM Event Unit :=
  Classical.choose (remainder_exists child point)

theorem continuation (child : ReleaseContract raw Good) (point : Point raw pid w h u middle) :
    runPrefix (wg (expiredZeroKeyMaterial pid)) w h = runPrefix (remainder child point) u middle :=
  Classical.choose_spec (remainder_exists child point)

theorem safe (carrierGood : ∀ h w, Carrier h w → Good h w)
    (child : ReleaseContract raw Good) (before : Carrier h w) (point : Point raw pid w h u middle) : Good middle u := by
  cases point with
  | entry => exact carrierGood _ _ before
  | beforeCut point => exact carrierGood _ _ (point.safe (fun _ _ h => h) quietChildren before)
  | repayment leading point => exact child.safe _ _ _ _ _ _ _ before leading point
  | returned performed => exact carrierGood _ _ ((Shape.child (.zero pid)).normal before performed)

/-- The actual whole result has its exact prefix result and, only when
selected, the real raw repayment result. No failed World is introduced. -/
theorem cases (pid : PeerId) (w : World) (h : History) :
    (∃ reason last, runPrefix (wg (beforeRepay pid)) w h = (.error reason,last) ∧
      runPrefix (wg (expiredZeroKeyMaterial pid)) w h = (.error reason,last)) ∨
    (∃ repay u middle, runPrefix (wg (beforeRepay pid)) w h = (.ok (repay,u),middle) ∧
      runPrefix (wg (expiredZeroKeyMaterial pid)) w h = runPrefix (wg (afterRepay pid repay)) u middle) := by
  rw [product_factor]
  cases leading : runPrefix (wg (beforeRepay pid)) w h with
  | mk result middle =>
    cases result with
    | error reason => exact Or.inl ⟨reason,middle,rfl,by rw [runPrefix_bind,leading]⟩
    | ok out => obtain ⟨repay,u⟩ := out; exact Or.inr ⟨repay,u,middle,rfl,by rw [runPrefix_bind,leading]⟩
end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Timer.Points.Zero
