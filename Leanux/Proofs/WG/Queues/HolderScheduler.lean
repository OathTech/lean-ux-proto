import Leanux.Proofs.WG.Queues.HolderTxHistory
import Leanux.Proofs.WG.Queues.RxRingScheduler

/-! Actual worker/scheduler composition of the complete holder account and
physical RX ring. The receive-worker account remains an explicit source
contract; copied consistency trials retain their original audit-only history. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.HolderScheduler
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open DurableHolders
open DecryptIteration (Physical)

/-- One fixed committed RX accounting cut and a real physical-ring witness. -/
def Inv (initial : Ledger) (loans : Reservations) (before h : List RxHistory.Event) (w : World) : Prop :=
  HolderNapi.At initial loans before h w ∧ Physical w

private theorem physical_cell (hi : Physical w) (same : RxRing.cell v = RxRing.cell w) : Physical v := by
  obtain ⟨epoch,n,h,ring,refines,cell⟩ := hi
  exact ⟨epoch,n,h,ring,refines,same.trans cell⟩

private theorem physical_store (hi : Physical w) (same : productStoreView v = productStoreView w) : Physical v := by
  apply physical_cell hi
  exact congrArg (fun p : ProductStore43 => p.2.2.2.dev.map fun d => (d.ifindex,d.decryptQueue)) same

/-- The existing physical observer is interpreted on this same actual run. -/
theorem physical_call (call : RxRing.SchedulerCall α) (hi : Physical w)
    (run : call.original.run w = .ok (x,v)) : Physical v := by
  obtain ⟨epoch,n,h,ring⟩ := hi
  have post := (call.preserves (deviceIndex := epoch) (initial := PtrRing.init n) w h ring).choose_spec.2.2
  have actual := (call.erases w h).trans run
  rw [actual] at post
  exact ⟨epoch,n,_,post⟩

private theorem combine {action : RxHistory.Obs α} {original : Leanux.M α}
    (account : PrefixPreserves (HolderNapi.At initial loans before) (fun _ => True) action)
    (erase : ErasesPrefix action original)
    (physical : ∀ w x v, Physical w → original.run w = .ok (x,v) → Physical v) :
    PrefixPreserves (Inv initial loans before) (fun _ => True) action := by
  intro w h hi
  obtain ⟨suffix,history,safe,post⟩ := account w h hi.1
  refine ⟨suffix,history,safe,?_⟩
  cases run : (runPrefix action w h).1 with
  | error e => trivial
  | ok out =>
    exact ⟨by simpa only [run] using post,
      physical w out.1 out.2 hi.2 ((erase w h).symm.trans run)⟩

theorem store (hi : Inv initial loans before h w) (same : productStoreView v = productStoreView w) :
    Inv initial loans before h v := ⟨HolderNapi.store hi.1 same,physical_store hi.2 same⟩

private theorem mixed (g : PrefixM LifetimeEvent α) (original : Leanux.M α)
    (erase : ErasesPrefix g original)
    (keeps : ∀ cs, Preserves (fun w : World => Boundary cs loans w.wg) original)
    (cell : SameView RxRing.cell original) :
    PrefixPreserves (Inv initial loans before) (fun _ => True) (RxHistory.mixed g) := by
  apply combine (original := original) ?_ (RxHistory.mixed_erases erase)
    (fun w x v hi run => physical_cell hi ((ProjectedAction.iff_run _ _ _).mp cell w x v run))
  apply PrefixEnsures.preserves
  apply NapiCarrier.normal_spec (Appends.focus _ _ _)
  intro w h x v hi run
  exact HolderEncrypt.mixed_at g original erase keeps hi (Prod.ext run rfl)

private theorem stored (g : PrefixM LifetimeEvent α) (original : Leanux.M α)
    (erase : ErasesPrefix g original) (frame : SameProductStore original) :
    PrefixPreserves (Inv initial loans before) (fun _ => True) (RxHistory.mixed g) :=
  mixed g original erase (fun _ => HolderEncrypt.product_store_boundary frame)
    (frame.of_factor (fun p : ProductStore43 => p.2.2.2.dev.map fun d => (d.ifindex,d.decryptQueue))
      RxRing.cell (fun _ => rfl))

/-- Every original scheduler atom is discharged from its actual source frame.
The consistency probe executes copied Worlds, retaining only its real marker. -/
theorem atoms (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event) :
    RxHistory.SchedulerSource.AtomContracts (Inv initial loans before) (fun _ => True) (fun {_} g => g) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro α a
    exact stored _ _ (erasesPrefix_lift _) (fun _ => productAmbient_spec a _ (fun _ _ hi => hi))
  · intro α e
    exact stored _ _ (erasesPrefix_throw e) (fun _ => hoare_throw e)
  · intro pid
    apply stored _ _ (liftWGObserver_erases (getPeerMixed_erases pid))
    apply liftWG_sameProductStore
    apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w a p v b run
    exact congrArg wgStoreView (getPeer_normal pid w v p a b run).1
  · intro id
    apply stored _ _ (liftWGObserver_erases (getTxSkbPrefix_erases id))
    apply liftWG_sameProductStore
    apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w a p v b run
    exact congrArg wgStoreView (Packets.getTxSkb_current id w v p a b run).1
  · intro f
    exact mixed _ _ (liftWGObserver_erases (erasesStatePrefix_lift _))
      (fun _ => HolderEncrypt.lift_boundary (HolderEncrypt.native_boundary (HolderTxHistory.work_fields f)))
      (sameView_liftWG RxRing.cell RxRing.nativeCell _
        (RxRing.modifyDev_cell _ (fun _ => rfl) (fun _ => rfl)) (fun _ _ _ h => h))
  · intro a
    exact stored _ _ (activationOccupancyPrefix_erases a) (activationOccupancy_sameKernel a)
  · exact stored _ _ activationRefillsPrefix_erases activationRefills_sameKernel
  · intro next
    exact stored _ _ (pendingNapiPrefix_erases next) (SourceScheduler.pendingNapi_kernel next)
  · intro a
    exact stored _ _ (activationHasWorkPrefix_erases a) (activationHasWork_sameKernel a)
  · have frame : SameProductStore (do
        let w ← getAmbient
        w.suspended.filterM Env.Activation.consistent) :=
      (show SameProductStore getAmbient from fun _ =>
        productAmbient_spec (get : AmbientM Ambient) _ (fun _ _ hi => hi)).bind
        (fun w => filterM_sameKernel productStoreView _ activationConsistent_sameKernel w.suspended)
    exact combine (HolderNapi.audit_frame _ _ consistentFilterAudit_erases frame)
      (RxHistory.audit_erases consistentFilterAudit_erases)
      (fun w x v hi run => physical_store hi ((ProjectedAction.iff_run _ _ _).mp frame w x v run))

theorem encrypt_preserves (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event) :
    PrefixPreserves (Inv initial loans before) (fun _ => True) RxHistory.encryptIteration := by
  apply PrefixEnsures.preserves
  apply NapiCarrier.normal_spec
    (pinned_const _private.Leanux.Proofs.WG.Queues.RxWaitAppends.«0».Leanux.Proofs.WG.Queues.RxHistory.encryptIteration_appends)
  intro w h x v hi run
  exact ⟨HolderEncrypt.iteration_normal hi.1 (Prod.ext run rfl),
    HolderEncrypt.physical_normal hi.2 ((RxHistory.encryptIteration_erases w h).symm.trans run)⟩

theorem decrypt_preserves (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event) :
    PrefixPreserves (Inv initial loans before) (fun _ => True) RxHistory.decryptIteration := by
  apply PrefixEnsures.preserves
  apply NapiCarrier.normal_spec
    (pinned_const _private.Leanux.Proofs.WG.Queues.RxWaitAppends.«0».Leanux.Proofs.WG.Queues.RxHistory.decryptIteration_appends)
  intro w h x v hi run
  refine ⟨HolderDecryptHistory.iteration_normal hi.1 hi.2 (Prod.ext run rfl),?_⟩
  obtain ⟨epoch,n,history,physical⟩ := hi.2
  exact ⟨epoch,n,_,DecryptConcrete.ring_normal physical ((RxHistory.decryptIteration_erases w h).symm.trans run)⟩

theorem tx_preserves (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event) (pid : PeerId) :
    PrefixPreserves (Inv initial loans before) (fun _ => True)
      (RxHistory.mixed (txIterPrefix pid (liftPrefix (Env.condResched .txWorker)))) :=
  mixed _ _ (txIterPrefix_erases pid (erasesPrefix_lift _))
    (fun _ => HolderTxHistory.txIter_boundary pid)
    (RxRing.txIter_cell pid _ ((condResched_sameKernel .txWorker).of_factor
      (fun p : ProductStore43 => p.2.2.2.dev.map fun d => (d.ifindex,d.decryptQueue)) RxRing.cell (fun _ => rfl)))

theorem ahead_preserves (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event) (pid : PeerId) :
    PrefixPreserves (Inv initial loans before) (fun _ => True) (RxHistory.cryptAhead pid) := by
  rw [RxHistory.SchedulerSource.cryptAhead_factor]
  exact RxHistory.SchedulerSource.cryptAhead_preserves (fun _ _ _ => True.intro) _
    (atoms initial loans before) _ (encrypt_preserves initial loans before) pid

/-- The receive-worker obligation names the original observer, not a substitute
callback or an initialized result. -/
theorem iteration_preserves (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event)
    (receive : PrefixPreserves (Inv initial loans before) (fun _ => True) Origins.HistoryAdapters.receiveIteration)
    (a : Activation) :
    PrefixPreserves (Inv initial loans before) (fun _ => True) (RxHistory.activationIteration a) := by
  rw [RxHistory.SchedulerSource.iteration_factor]
  exact RxHistory.SchedulerSource.iteration_preserves _ (atoms initial loans before) _ _ _ _ _
    (encrypt_preserves initial loans before) (ahead_preserves initial loans before)
    (tx_preserves initial loans before) (decrypt_preserves initial loans before) receive a

theorem run_preserves (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event)
    (receive : PrefixPreserves (Inv initial loans before) (fun _ => True) Origins.HistoryAdapters.receiveIteration)
    (a : Activation) :
    PrefixPreserves (Inv initial loans before) (fun _ => True) (RxHistory.activationRun a) := by
  rw [RxHistory.SchedulerSource.run_factor]
  exact RxHistory.SchedulerSource.run_preserves (I := Inv initial loans before) (fun _ _ _ => True.intro)
    (fun _ _ _ same hi => store hi same) _ (atoms initial loans before) _
    (iteration_preserves initial loans before receive) a

theorem dispatch_preserves (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event)
    (receive : PrefixPreserves (Inv initial loans before) (fun _ => True) Origins.HistoryAdapters.receiveIteration)
    (worker : Worker) :
    PrefixPreserves (Inv initial loans before) (fun _ => True) (RxHistory.dispatch worker) := by
  rw [RxHistory.SchedulerSource.dispatch_factor]
  exact RxHistory.SchedulerSource.dispatch_preserves (I := Inv initial loans before) (fun _ _ _ => True.intro)
    (fun _ _ _ same hi => store hi same) _ (atoms initial loans before) _
    (run_preserves initial loans before receive) worker

theorem softirq_preserves (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event) :
    PrefixPreserves (Inv initial loans before) (fun _ => True) RxHistory.napiSoftirq :=
  combine (HolderNapi.softirq_preserves initial loans before) RxHistory.napiSoftirq_erases
    (fun w x v hi run => physical_cell hi ((ProjectedAction.iff_run _ _ _).mp RxRing.napiSoftirq_cell w x v run))

theorem schedule_preserves (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event)
    (receive : PrefixPreserves (Inv initial loans before) (fun _ => True) Origins.HistoryAdapters.receiveIteration)
    (stack : Option Worker) :
    PrefixPreserves (Inv initial loans before) (fun _ => True) (RxHistory.schedule stack) := by
  rw [RxHistory.SchedulerSource.schedule_factor]
  exact RxHistory.SchedulerSource.schedule_preserves (I := Inv initial loans before) (fun _ _ _ => True.intro)
    (fun _ _ _ same hi => store hi same) _ (atoms initial loans before) _ _ _
    (dispatch_preserves initial loans before receive) (run_preserves initial loans before receive)
    (softirq_preserves initial loans before) stack

theorem nested_preserves (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event)
    (receive : PrefixPreserves (Inv initial loans before) (fun _ => True) Origins.HistoryAdapters.receiveIteration)
    (worker : Worker) :
    PrefixPreserves (Inv initial loans before) (fun _ => True) (RxHistory.nestedResched worker) := by
  rw [RxHistory.SchedulerSource.nested_factor]
  exact RxHistory.SchedulerSource.nested_preserves (I := Inv initial loans before) (fun _ _ _ => True.intro)
    (fun _ _ _ same hi => store hi same) _ (schedule_preserves initial loans before receive) worker

/-- No receive contract is needed for a different actual activation kind. -/
theorem iteration_nonreceive (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event)
    (a : Activation) (worker : a.worker ≠ .receiveWorker) :
    PrefixPreserves (Inv initial loans before) (fun _ => True) (RxHistory.activationIteration a) := by
  have atomic := atoms initial loans before
  unfold RxHistory.activationIteration
  cases actual : a.worker <;> simp only [actual] at worker ⊢
  all_goals first
    | contradiction
    | exact encrypt_preserves initial loans before
    | exact decrypt_preserves initial loans before
    | exact atomic.ambient (AmbientM.invariant _)
    | (cases pid : a.pid with
       | none => exact atomic.ambient (AmbientM.invariant _)
       | some p => exact (PrefixPreserves.bind (ahead_preserves initial loans before p)
           (fun _ => tx_preserves initial loans before p)))

private theorem raw (action : Leanux.M α) (frame : SameProductStore action) :
    PrefixPreserves (Inv initial loans before) (fun _ => True) (liftPrefix action) :=
  viewLiftPrefix_preserves productStoreView (fun _ _ _ => True.intro)
    (fun _ _ _ same hi => store hi same) frame

private theorem with_pure (P : Prop) {action : RxHistory.Obs α}
    (keeps : P → PrefixPreserves (Inv initial loans before) (fun _ => True) action) :
    PrefixEnsures (fun h w => P ∧ Inv initial loans before h w) (fun _ => True) action
      (fun _ h w => P ∧ Inv initial loans before h w) := by
  intro w h hi
  obtain ⟨suffix,history,safe,post⟩ := keeps hi.1 w h hi.2
  refine ⟨suffix,history,safe,?_⟩
  cases run : (runPrefix action w h).1 with
  | error e => trivial
  | ok out => exact ⟨hi.1,by simpa only [run] using post⟩

/-- The original loop preserves the non-receive worker tag as it updates only
the iteration count. Encrypt, decrypt and TX runs are therefore closed. -/
theorem run_nonreceive (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event)
    (a : Activation) (worker : a.worker ≠ .receiveWorker) :
    PrefixPreserves (Inv initial loans before) (fun _ => True) (RxHistory.activationRun a) := by
  let I := fun z : Option Unit × Activation => fun h w =>
    z.2.worker ≠ Worker.receiveWorker ∧ Inv initial loans before h w
  have ambient {α : Type} (p : Prop) (action : AmbientM α) :
      PrefixEnsures (fun h w => p ∧ Inv initial loans before h w) (fun _ => True)
        (liftPrefix (monadLift action : Leanux.M α))
        (fun _ h w => p ∧ Inv initial loans before h w) :=
    with_pure p (fun _ => raw _ (fun _ => productAmbient_spec action _ (fun _ _ hi => hi)))
  unfold RxHistory.activationRun
  apply PrefixPreserves.bind ((atoms initial loans before).occupancy a)
  intro count
  apply PrefixPreserves.bind (atoms initial loans before).refills
  intro refillCount
  apply PrefixEnsures.preserves
  apply PrefixEnsures.bind (Q := I)
  · refine PrefixEnsures.consequence
      (PrefixEnsures.rangeInvariant _ _ _ I _ (fun _ _ _ _ => True.intro) ?_)
      (fun _ _ hi => ⟨worker,hi⟩) (fun _ _ _ hi => hi)
    intro n z
    apply PrefixEnsures.bind (Q := fun _ => I z)
      (with_pure (z.2.worker ≠ .receiveWorker)
        (fun worker => iteration_nonreceive initial loans before z.2 worker))
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
    | some u => exact PrefixEnsures.pure (fun _ _ _ => True.intro) (fun _ _ hi => hi.2)
    | none =>
      apply PrefixEnsures.lift _ (fun _ _ _ => True.intro)
      intro h w x v hi run
      cases run

theorem dispatch_nonreceive (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event)
    (worker : Worker) (other : worker ≠ .receiveWorker) :
    PrefixPreserves (Inv initial loans before) (fun _ => True) (RxHistory.dispatch worker) := by
  have safe : ∀ h w, Inv initial loans before h w → True := fun _ _ _ => True.intro
  have saved : ∀ h w v, productStoreView v = productStoreView w →
      Inv initial loans before h w → Inv initial loans before h v :=
    fun _ _ _ same hi => store hi same
  have atomic := atoms initial loans before
  unfold RxHistory.dispatch
  cases worker <;> simp only at other ⊢
  all_goals repeat' first
    | contradiction
    | (scheduler_preserve_at RxHistory.activationRun; exact run_nonreceive initial loans before _ (by intro h; cases h))
    | (scheduler_preserve_at modifyDev; exact atomic.work (fun q => q.erase _))
    | scheduler_raw_steps safe saved

private theorem native_result {action : RxHistory.Obs α} {original : Leanux.M α}
    (keeps : PrefixPreserves (Inv cs loans h) (fun _ => True) action)
    (erase : ErasesPrefix action original) (funded : Boundary cs loans w.wg) (physical : Physical w)
    (run : original.run w = .ok (x,v)) :
    (∃ suffix, (runPrefix action w h).2 = h ++ suffix ∧
      Boundary (remaining cs (NapiCarrier.removedPackets suffix)) loans v.wg) ∧ Physical v := by
  have actual := (erase w h).trans run
  have post := (keeps w h ⟨HolderNapi.at_start funded h,physical⟩).choose_spec.2.2
  simpa only [actual,Inv,HolderNapi.At] using post

/-- Closed normal endpoints for encrypt/decrypt/TX and the original unsupported
activation cases, without a receive-worker account assumption. -/
theorem run_normal (a : Activation) (other : a.worker ≠ .receiveWorker)
    (funded : Boundary cs loans w.wg) (physical : Physical w)
    (run : (Env.Activation.run a).run w = .ok ((),v)) (h : List RxHistory.Event) :
    (∃ suffix, (runPrefix (RxHistory.activationRun a) w h).2 = h ++ suffix ∧
      Boundary (remaining cs (NapiCarrier.removedPackets suffix)) loans v.wg) ∧ Physical v :=
  native_result (run_nonreceive cs loans h a other) (RxHistory.activationRun_erases a) funded physical run

theorem dispatch_normal (worker : Worker) (other : worker ≠ .receiveWorker)
    (funded : Boundary cs loans w.wg) (physical : Physical w)
    (run : (Env.dispatch worker).run w = .ok (result,v)) (h : List RxHistory.Event) :
    (∃ suffix, (runPrefix (RxHistory.dispatch worker) w h).2 = h ++ suffix ∧
      Boundary (remaining cs (NapiCarrier.removedPackets suffix)) loans v.wg) ∧ Physical v :=
  native_result (dispatch_nonreceive cs loans h worker other) (RxHistory.dispatch_erases worker) funded physical run

/-- Full scheduling exposes exactly the remaining concrete receive-observer
contract. Copied trials do not contribute committed RX removals. -/
theorem schedule_normal (stack : Option Worker) (h : List RxHistory.Event)
    (receive : PrefixPreserves (Inv cs loans h) (fun _ => True) Origins.HistoryAdapters.receiveIteration)
    (funded : Boundary cs loans w.wg) (physical : Physical w)
    (run : (Env.schedule stack).run w = .ok ((),v)) :
    (∃ suffix, (runPrefix (RxHistory.schedule stack) w h).2 = h ++ suffix ∧
      Boundary (remaining cs (NapiCarrier.removedPackets suffix)) loans v.wg) ∧ Physical v :=
  native_result (schedule_preserves cs loans h receive stack) (RxHistory.schedule_erases stack) funded physical run

end Leanux.Proofs.WG.Queues.RxCredits.HolderScheduler
