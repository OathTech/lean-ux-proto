import Leanux.Proofs.WG.Lifetimes.BatchScheduler

/-! A callback-parameterized copy of the original scheduler control flow.
Only committed activation/NAPI calls use the supplied observers. Consistency
trials execute the original action on its copied World and emit no events. -/
set_option maxHeartbeats 2000000
namespace Leanux.Proofs.WG.Queues.SourceScheduler
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
variable {Event : Type}

theorem occupancy_kernel (a : Activation) : SameProductStore (Env.Activation.occupancy a) :=
  activationOccupancy_sameKernel a

theorem hasWork_kernel (a : Activation) : SameProductStore (Env.Activation.hasWork a) :=
  activationHasWork_sameKernel a

theorem pendingNapi_kernel (next : Option Nat) : SameProductStore (Lifetimes.pendingNapi next) := by
  unfold Lifetimes.pendingNapi
  exact (liftWG_sameProductStore getDev Lifetimes.getDev_sameWGStore).bind
    (fun _ => SameView.pure _ _)

def run (iteration : Activation → PrefixM Event IterResult) (a : Activation) : PrefixM Event Unit := do
  let occupancy ← liftPrefix (Env.Activation.occupancy a)
  let refills ← liftPrefix Env.Activation.refills
  let mut act := a
  for _ in [0:occupancy + refills + 1] do
    match ← iteration act with
    | .ended => _ ← liftPrefix (hidden (.sectionStop act.worker)); return
    | .continued => act := {act with iterations := act.iterations + 1}
    | .yielded =>
      liftPrefix (modifyAmbient fun s => {s with suspended := s.suspended ++ [{act with iterations := act.iterations + 1}]})
      return
  liftPrefix (invariant s!"{a.worker.symbol} consumed more items than its queue held ({occupancy}) plus the refills its run could take ({refills})")

def dispatch (iteration : Activation → PrefixM Event IterResult) (worker : Worker) : PrefixM Event Bool := do
  let d ← liftPrefix (liftWG getDev)
  let mut pid : Option Nat := none
  match worker with
  | .encryptWorker => if !(← liftPrefix (Env.pendingDevice worker !d.encryptQueue.empty)) then return false
  | .decryptWorker => if !(← liftPrefix (Env.pendingDevice worker !d.decryptQueue.empty)) then return false
  | .receiveWorker => if !(← liftPrefix (Env.pendingDevice worker !d.handshakeQueue.empty)) then return false
  | .txWorker =>
    let some headPid := d.txWorkQueue.head? | return false
    let p ← match ← liftPrefix (peekUnit .txWorker) with
      | some u => liftPrefix (resolveUnit .txWorker u d.txWorkQueue)
      | none => pure headPid
    liftPrefix (liftWG (modifyDev fun d => {d with txWorkQueue := d.txWorkQueue.erase p}))
    pid := some p
  | _ => return false
  _ ← liftPrefix (hidden (.sectionStart worker))
  run iteration {worker, pid}
  return true

def schedule (iteration : Activation → PrefixM Event IterResult) (napi : PrefixM Event Unit) (stack : Option Worker := none) : PrefixM Event Unit := do
  let netRx := (HiddenSite.sectionStart .netRx).info.id
  for _ in [0:(← liftPrefix recordBudget)] do
    if (← liftPrefix getAmbient).hidden.isNone then
      let d ← liftPrefix (liftWG getDev)
      let pending := (← liftPrefix getAmbient).pendingWork
      let next := [Worker.receiveWorker, .decryptWorker, .encryptWorker, .txWorker].find? fun w =>
        match w with
        | .receiveWorker => !d.handshakeQueue.empty || pending.contains w.index
        | .decryptWorker => !d.decryptQueue.empty || pending.contains w.index
        | .encryptWorker => !d.encryptQueue.empty || pending.contains w.index
        | _ => !d.txWorkQueue.isEmpty
      let some w := next | return
      if !(← dispatch iteration w) then liftPrefix (invariant s!"{w.symbol} has work but was not dispatched")
      continue
    let next ← liftPrefix peekHiddenSite
    if let some (w, true) := next.bind Env.sectionOf then
      if ← dispatch iteration w then continue else return
    if ← liftPrefix (Lifetimes.pendingNapi next) then
      napi
      if (← liftPrefix peekHiddenSite) == some netRx then return
      continue
    match ← liftPrefix ((← liftPrefix getAmbient).suspended.filterM Env.Activation.consistent) with
    | [] => return
    | [a] =>
      if let some w := stack then
        if ← liftPrefix (Env.Activation.hasWork {worker := w}) then
          liftPrefix (unsupported "the records do not determine which suspended worker resumed")
      liftPrefix (modifyAmbient fun s => {s with suspended := s.suspended.filter (· != a)})
      run iteration a
    | _ => liftPrefix (unsupported "the records do not determine which suspended worker resumed")
  liftPrefix (budgetExhausted "the scheduler loop")

theorem run_erases (iteration : Activation → PrefixM Event IterResult)
    (hi : ∀ a, ErasesPrefix (iteration a) (Env.Activation.iter a)) (a : Activation) :
    ErasesPrefix (run iteration a) (Env.Activation.run a) := by
  unfold run Env.Activation.run
  repeat' first
    | with_reducible exact hi _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_range
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split; all_goals try simp_all only []; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem dispatch_erases (iteration : Activation → PrefixM Event IterResult)
    (hi : ∀ a, ErasesPrefix (iteration a) (Env.Activation.iter a)) (worker : Worker) :
    ErasesPrefix (dispatch iteration worker) (Env.dispatch worker) := by
  unfold dispatch Env.dispatch
  repeat' first
    | with_reducible exact run_erases iteration hi _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split; all_goals try simp_all only []; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

  all_goals exact erasesPrefix_lift _

theorem schedule_erases (iteration : Activation → PrefixM Event IterResult) (napi : PrefixM Event Unit)
    (hi : ∀ a, ErasesPrefix (iteration a) (Env.Activation.iter a))
    (hn : ErasesPrefix napi Env.napiSoftirq) (stack : Option Worker) :
    ErasesPrefix (schedule iteration napi stack) (Env.schedule stack) := by
  rw [← Lifetimes.scheduleWithPending_eq]
  unfold schedule Lifetimes.scheduleWithPending
  repeat' first
    | with_reducible exact dispatch_erases iteration hi _
    | with_reducible exact run_erases iteration hi _
    | with_reducible exact hn
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_range
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split; all_goals try simp_all only []; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)
  all_goals first
    | exact erasesPrefix_lift _
    | grind only [dispatch_erases, erasesPrefix_lift]

variable {I : List Event → World → Prop} {S : List Event → Prop}

theorem run_preserves (hs : ∀ h w, I h w → S h)
    (hk : ∀ h w v, productStoreView v = productStoreView w → I h w → I h v)
    (iteration : Activation → PrefixM Event IterResult)
    (hi : ∀ a, PrefixPreserves I S (iteration a)) (a : Activation) :
    PrefixPreserves I S (run iteration a) := by
  have ambient {α : Type} (a : AmbientM α) :
      PrefixPreserves I S (liftPrefix (MonadLift.monadLift a : Leanux.M α)) := by
    apply viewLiftPrefix_preserves productStoreView hs hk
    apply SameView.of_wp
    intro initial
    exact productAmbient_spec a _ (fun _ _ hi => hi)
  apply PrefixEnsures.preserves
  unfold run
  repeat' first
    | exact hi _
    | (batch_lift_head Env.Activation.refills; exact viewLiftPrefix_preserves productStoreView hs hk activationRefills_sameKernel)
    | (batch_lift_head Env.Activation.occupancy; exact viewLiftPrefix_preserves productStoreView hs hk (occupancy_kernel _))
    | (first | batch_lift_head hidden | batch_lift_head invariant | batch_lift_head modifyAmbient
       exact ambient _)
    | (maintenance_head Pure.pure; exact PrefixEnsures.pure hs (fun _ _ hi => hi))
    | (maintenance_head ForIn.forIn; apply PrefixEnsures.rangeInvariant (State := World)
        (I := fun _ h w => I h w) (hs := fun _ h w hi => hs h w hi))
    | (maintenance_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ h w => I h w))
    | maintenance_reduce
    | (maintenance_head ite; split)
    | (maintenance_head dite; split)
    | (with_reducible split; all_goals try simp_all only []; all_goals try subst_vars)
    | (maintenance_intro; try dsimp only)

theorem dispatch_preserves (hs : ∀ h w, I h w → S h)
    (hk : ∀ h w v, productStoreView v = productStoreView w → I h w → I h v)
    (he : ∀ pid, PrefixPreserves I S (liftPrefix (liftWG (modifyDev fun d => {d with txWorkQueue := d.txWorkQueue.erase pid}))))
    (iteration : Activation → PrefixM Event IterResult)
    (hi : ∀ a, PrefixPreserves I S (iteration a)) (worker : Worker) :
    PrefixPreserves I S (dispatch iteration worker) := by
  have ambient {α : Type} (a : AmbientM α) :
      PrefixPreserves I S (liftPrefix (MonadLift.monadLift a : Leanux.M α)) := by
    apply viewLiftPrefix_preserves productStoreView hs hk
    apply SameView.of_wp
    intro initial
    exact productAmbient_spec a _ (fun _ _ hi => hi)
  apply PrefixEnsures.preserves
  unfold dispatch
  repeat' first
    | (batch_lift_head Env.pendingDevice; exact viewLiftPrefix_preserves productStoreView hs hk (pendingDevice_sameKernel _ _))
    | (maintenance_head run; exact run_preserves hs hk iteration hi _)
    | (batch_lift_head liftWG
       first
       | exact he _
       | exact viewLiftPrefix_preserves productStoreView hs hk
           (liftWG_sameProductStore getDev Lifetimes.getDev_sameWGStore))
    | (first | batch_lift_head peekUnit | batch_lift_head resolveUnit | batch_lift_head hidden
       exact ambient _)
    | (maintenance_head Pure.pure; exact PrefixEnsures.pure hs (fun _ _ hi => hi))
    | (maintenance_head ForIn.forIn; apply PrefixEnsures.rangeInvariant (State := World)
        (I := fun _ h w => I h w) (hs := fun _ h w hi => hs h w hi))
    | (maintenance_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ h w => I h w))
    | maintenance_reduce
    | (maintenance_head ite; split)
    | (maintenance_head dite; split)
    | (with_reducible split; all_goals try simp_all only []; all_goals try subst_vars)
    | (maintenance_intro; try dsimp only)

theorem schedule_preserves (hs : ∀ h w, I h w → S h)
    (hk : ∀ h w v, productStoreView v = productStoreView w → I h w → I h v)
    (he : ∀ pid, PrefixPreserves I S (liftPrefix (liftWG (modifyDev fun d => {d with txWorkQueue := d.txWorkQueue.erase pid}))))
    (iteration : Activation → PrefixM Event IterResult) (napi : PrefixM Event Unit)
    (hi : ∀ a, PrefixPreserves I S (iteration a)) (hn : PrefixPreserves I S napi) (stack : Option Worker) :
    PrefixPreserves I S (schedule iteration napi stack) := by
  have ambient {α : Type} (a : AmbientM α) :
      PrefixPreserves I S (liftPrefix (MonadLift.monadLift a : Leanux.M α)) := by
    apply viewLiftPrefix_preserves productStoreView hs hk
    apply SameView.of_wp
    intro initial
    exact productAmbient_spec a _ (fun _ _ hi => hi)
  apply PrefixEnsures.preserves
  unfold schedule
  repeat' first
    | (maintenance_head dispatch; exact dispatch_preserves hs hk he iteration hi _)
    | (maintenance_head run; exact run_preserves hs hk iteration hi _)
    | exact hn
    | (batch_lift_head liftWG
       exact viewLiftPrefix_preserves productStoreView hs hk
         (liftWG_sameProductStore getDev Lifetimes.getDev_sameWGStore))
    | (batch_lift_head Lifetimes.pendingNapi; exact viewLiftPrefix_preserves productStoreView hs hk (pendingNapi_kernel _))
    | (batch_lift_head Env.Activation.hasWork; exact viewLiftPrefix_preserves productStoreView hs hk (hasWork_kernel _))
    | (batch_lift_head List.filterM; exact viewLiftPrefix_preserves productStoreView hs hk
        (filterM_sameKernel productStoreView _ activationConsistent_sameKernel _))
    | (first
       | batch_lift_head peekHiddenSite | batch_lift_head recordBudget
       | batch_lift_head budgetExhausted | batch_lift_head invariant | batch_lift_head unsupported
       | batch_lift_head getAmbient | batch_lift_head modifyAmbient
       exact ambient _)
    | (maintenance_head Pure.pure; exact PrefixEnsures.pure hs (fun _ _ hi => hi))
    | (maintenance_head ForIn.forIn; apply PrefixEnsures.rangeInvariant (State := World)
        (I := fun _ h w => I h w) (hs := fun _ h w hi => hs h w hi))
    | (maintenance_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ h w => I h w))
    | maintenance_reduce
    | (maintenance_head ite; split)
    | (maintenance_head dite; split)
    | (with_reducible split; all_goals try simp_all only []; all_goals try subst_vars)
    | (maintenance_intro; try dsimp only)

end Leanux.Proofs.WG.Queues.SourceScheduler
