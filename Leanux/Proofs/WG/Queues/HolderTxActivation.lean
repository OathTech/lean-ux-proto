import Leanux.Proofs.WG.Queues.HolderTxHistory

/-! The actual bounded TX activation retains the journal's fixed accounting
cut; its crypt-ahead encryption may append real RX removal events. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.HolderTxActivation
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open DurableHolders

private theorem raw (action : Leanux.M α) (frame : SameProductStore action) :
    PrefixPreserves (HolderNapi.At initial loans before) (fun _ => True) (liftPrefix action) :=
  viewLiftPrefix_preserves productStoreView (fun _ _ _ => True.intro)
    (fun _ _ _ same hi => HolderNapi.store hi same) frame

private theorem occupancy (a : Activation) :
    PrefixPreserves (HolderNapi.At initial loans before) (fun _ => True)
      (RxHistory.mixed (activationOccupancyPrefix a)) := by
  apply NapiCarrier.normal_spec (Appends.focus _ _ _)
  intro w h x v hi run
  exact HolderEncrypt.mixed_at _ _ (activationOccupancyPrefix_erases a)
    (fun _ => HolderEncrypt.product_store_boundary (activationOccupancy_sameKernel a)) hi (Prod.ext run rfl)

private theorem with_pure (P : Prop) {action : RxHistory.Obs α}
    (keeps : P → PrefixPreserves (HolderNapi.At initial loans before) (fun _ => True) action) :
    PrefixEnsures (fun h w => P ∧ HolderNapi.At initial loans before h w) (fun _ => True) action
      (fun _ h w => P ∧ HolderNapi.At initial loans before h w) := by
  intro w h hi
  obtain ⟨suffix,history,safe,post⟩ := keeps hi.1 w h hi.2
  refine ⟨suffix,history,safe,?_⟩
  cases run : (runPrefix action w h).1 with
  | error e => trivial
  | ok out => exact ⟨hi.1,by simpa only [run] using post⟩

/-- The occupancy-derived bound and the exact activation accumulator are the
ones in the original observer. -/
theorem activationRun_preserves (initial : Ledger) (loans : Reservations)
    (before : List RxHistory.Event) (a : Activation) (worker : a.worker = .txWorker) :
    PrefixPreserves (HolderNapi.At initial loans before) (fun _ => True) (RxHistory.activationRun a) := by
  let I := fun z : Option Unit × Activation => fun h w =>
    z.2.worker = Worker.txWorker ∧ HolderNapi.At initial loans before h w
  have ambient {α : Type} (p : Prop) (action : AmbientM α) :
      PrefixEnsures (fun h w => p ∧ HolderNapi.At initial loans before h w) (fun _ => True)
        (liftPrefix (monadLift action : Leanux.M α))
        (fun _ h w => p ∧ HolderNapi.At initial loans before h w) :=
    with_pure p (fun _ => raw _ (fun _ => productAmbient_spec action _ (fun _ _ hi => hi)))
  unfold RxHistory.activationRun
  apply PrefixPreserves.bind (occupancy a)
  intro count
  apply PrefixEnsures.preserves
  apply PrefixEnsures.bind (Q := I)
  · refine PrefixEnsures.consequence
      (PrefixEnsures.rangeInvariant _ _ _ I _ (fun _ _ _ _ => True.intro) ?_)
      (fun _ _ hi => ⟨worker,hi⟩) (fun _ _ _ hi => hi)
    intro n z
    apply PrefixEnsures.bind (Q := fun _ => I z)
      (with_pure (z.2.worker = .txWorker)
        (fun worker => HolderTxHistory.activationIteration_preserves initial loans before z.2 worker))
    intro result
    cases result with
    | ended =>
      apply PrefixEnsures.bind (Q := fun _ => I z) (ambient _ (AmbientM.hidden _))
      intro _
      exact PrefixEnsures.pure (fun _ _ _ => True.intro) (fun _ _ hi => hi)
    | continued =>
      exact PrefixEnsures.pure (fun _ _ _ => True.intro) (fun _ _ hi => hi)
    | yielded =>
      apply PrefixEnsures.bind (Q := fun _ => I z) (ambient _ (modify _ : AmbientM Unit))
      intro _
      exact PrefixEnsures.pure (fun _ _ _ => True.intro) (fun _ _ hi => hi)
  · intro result
    cases hx : result.1 with
    | some u =>
      exact PrefixEnsures.pure (fun _ _ _ => True.intro) (fun _ _ hi => hi.2)
    | none =>
      apply PrefixEnsures.lift _ (fun _ _ _ => True.intro)
      intro h w x v hi run
      cases run

/-- Actual dispatch resolves the recorded unit against the saved TX work list,
erases that alias once, and runs the original bounded activation. -/
theorem dispatch_preserves (initial : Ledger) (loans : Reservations)
    (before : List RxHistory.Event) :
    PrefixPreserves (HolderNapi.At initial loans before) (fun _ => True) (RxHistory.dispatch .txWorker) := by
  have safe : ∀ h w, HolderNapi.At initial loans before h w → True := fun _ _ _ => True.intro
  have store : ∀ h w v, productStoreView v = productStoreView w →
      HolderNapi.At initial loans before h w → HolderNapi.At initial loans before h v :=
    fun _ _ _ same hi => HolderNapi.store hi same
  have work (f : List PeerId → List PeerId) :
      PrefixPreserves (HolderNapi.At initial loans before) (fun _ => True)
        (RxHistory.mixed (liftWGObserver (liftWGPrefix
          (modifyDev fun d => {d with txWorkQueue := f d.txWorkQueue})))) := by
    apply PrefixEnsures.preserves
    apply NapiCarrier.normal_spec (Appends.focus _ _ _)
    intro w h x v hi run
    exact HolderEncrypt.mixed_at _ _ (liftWGObserver_erases (erasesStatePrefix_lift _))
      (fun _ => HolderEncrypt.lift_boundary (HolderEncrypt.native_boundary (HolderTxHistory.work_fields f)))
      hi (Prod.ext run rfl)
  unfold RxHistory.dispatch
  repeat' first
    | (scheduler_preserve_at RxHistory.activationRun; exact activationRun_preserves initial loans before _ rfl)
    | (scheduler_preserve_at modifyDev; exact work (fun q => q.erase _))
    | scheduler_raw_steps safe store

/-- The native TX activation's endpoint is accounted using this same observed
run's actual suffix, including any crypt-ahead NAPI removals. -/
theorem activationRun_normal (a : Activation) (worker : a.worker = .txWorker)
    (hi : Boundary cs loans w.wg)
    (run : (Env.Activation.run a).run w = .ok ((),v)) (h : List RxHistory.Event) :
    let k := (runPrefix (RxHistory.activationRun a) w h).2
    ∃ suffix, k = h ++ suffix ∧ Boundary (remaining cs (NapiCarrier.removedPackets suffix)) loans v.wg := by
  have actual := (RxHistory.activationRun_erases a w h).trans run
  have post := (activationRun_preserves cs loans h a worker w h (HolderNapi.at_start hi h)).choose_spec.2.2
  simpa only [actual,HolderNapi.At] using post

/-- A successful dispatcher result uses the selected actual activation; a
normal false result retains the account and its existing journal as well. -/
theorem dispatch_normal (hi : Boundary cs loans w.wg)
    (run : (Env.dispatch .txWorker).run w = .ok (result,v)) (h : List RxHistory.Event) :
    let k := (runPrefix (RxHistory.dispatch .txWorker) w h).2
    ∃ suffix, k = h ++ suffix ∧ Boundary (remaining cs (NapiCarrier.removedPackets suffix)) loans v.wg := by
  have actual := (RxHistory.dispatch_erases .txWorker w h).trans run
  have post := (dispatch_preserves cs loans h w h (HolderNapi.at_start hi h)).choose_spec.2.2
  simpa only [actual,HolderNapi.At] using post

end Leanux.Proofs.WG.Queues.RxCredits.HolderTxActivation
