import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedDrainPointCoverage

/-! Exact original continuations at every fixed drain point. A continuation
is obtained from an existing source point; equality never constructs a point.
The three deeper source contracts supply only their own native remainders. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SendDrain.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Queues TransmitSecurity CausalJournal
variable {native inside : ChildPoints} {Good : History → World → Prop}

def readTail (device : Device) : PrefixM Event (ForInStep LoopState) := do
  if device.sendWorkQueue.isEmpty then
    hooks.deliver
    return .done (some (),())
  Driver.sendWorkerObserved hooks
  Driver.scheduleObserved hooks none
  return .yield (none,())

theorem step_read_factor (index : Nat) (acc : LoopState) :
    step index acc = (liftPrefix (liftWG getDev) >>= readTail) := rfl

/-- Every fixed point, including a prefix of a later stopped drain, retains
the original remaining source and its actual world and receipt history. -/
theorem Point.remaining (children : ChildContracts native inside Good)
    (point : Point native w history site u middle) :
    ∃remaining : PrefixM Event Unit,
      runPrefix (Driver.sendWorkersObserved hooks) w history = runPrefix remaining u middle := by
  cases point with
  | front path =>
      obtain ⟨tail,_,continued⟩ := path.continuation
      exact ⟨tail.action,continued⟩
  | loop path => exact ⟨_,path.continuation⟩
  | read path performed =>
      rename_i device
      refine ⟨readTail device >>= afterStep path.rest,?_⟩
      rw [path.continuation,step_read_factor,bind_assoc,runPrefix_bind,performed]
  | childEntry path => exact ⟨_,path.continuation⟩
  | childReturn path performed => exact ⟨_,path.return_continuation performed⟩
  | childInterior path nativePoint => exact ⟨_,path.interior_continuation children nativePoint⟩
  | finish path => exact ⟨_,path.continuation⟩
  | returned performed => exact ⟨pure (),performed.trans (runPrefix_pure _ _ _).symm⟩

def RootPoints (points : ChildPoints) (w : World) (h : History) (u : World) (middle : History) : Prop :=
  ∃site,Point points w h site u middle

noncomputable def remainder (children : ChildContracts native inside Good)
    (w : World) (h : History) (u : World) (middle : History)
    (point : RootPoints native w h u middle) : PrefixM Event Unit :=
  Classical.choose ((Classical.choose_spec point).remaining children)

theorem remainder_run (children : ChildContracts native inside Good)
    (point : RootPoints native w h u middle) :
    runPrefix (Driver.sendWorkersObserved hooks) w h =
      runPrefix (remainder children w h u middle point) u middle :=
  Classical.choose_spec ((Classical.choose_spec point).remaining children)

theorem root_coverage (children : ChildContracts native inside Good)
    (point : RootPoints native w h u middle) : RootPoints inside w h u middle := by
  obtain ⟨site,point⟩ := point
  exact ⟨site,point.coverage children⟩

theorem root_safe (carrierGood : ∀h w,CompleteProduct.Carrier h w → Good h w)
    (children : ChildContracts native inside Good) (before : CompleteProduct.Carrier h w)
    (point : RootPoints inside w h u middle) : Good middle u := by
  obtain ⟨site,point⟩ := point
  exact point_safe carrierGood children before point

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SendDrain.Points
