import Leanux.Proofs.WG.Queues.RxRingHandshake
import Leanux.Proofs.WG.Queues.SourceScheduler

/-! Concrete committed RX ring journals through original scheduler control.
All non-decrypt activations, NAPI and IRQ callbacks have discharged full-cell
frames. Copied consistency trials remain unobserved in committed histories;
their own reached histories are characterized separately below. -/
set_option maxHeartbeats 2000000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Queues.RxRing
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do

theorem receiveIter_cell : SameView cell
    (workerIter .receiveWorker none receiveStep (Env.condResched .receiveWorker)) := by
  apply SameView.of_wp
  intro s
  have hr := receiveStep_cell.wp (fun t => t = s)
  have hc := (kernel (condResched_sameKernel .receiveWorker)).wp (fun t => t = s)
  mvcgen [workerIter, hr, hc]

/-- The original non-decrypt activation includes cryptAhead's actual encrypt
iteration before TX. A malformed activation still executes its original Stop. -/
theorem otherIter_cell (a : Activation) (h : a.worker ≠ .decryptWorker) :
    SameView cell (Env.Activation.iter a) := by
  unfold Env.Activation.iter
  cases hw : a.worker <;> simp only [hw]
  all_goals try exact actualEncryptIter_cell
  all_goals try exact receiveIter_cell
  all_goals try exact invariant_frame _
  · split
    · exact (cryptAhead_cell _).bind (fun _ => txIter_cell _ _ (kernel (condResched_sameKernel _)))
    · exact invariant_frame _
  · exact False.elim (h hw)

def activationIter (a : Activation) : Obs IterResult :=
  if a.worker = .decryptWorker then
    iter (liftPrefix Env.napiSoftirq) (liftPrefix Env.napiIrqExit)
      (liftPrefix (Env.condResched .decryptWorker))
  else liftPrefix (Env.Activation.iter a)

def activationRun (a : Activation) : Obs Unit := SourceScheduler.run activationIter a

def dispatch (worker : Worker) : Obs Bool := SourceScheduler.dispatch activationIter worker

def schedule (stack : Option Worker := none) : Obs Unit :=
  SourceScheduler.schedule activationIter (liftPrefix Env.napiSoftirq) stack

def nestedResched (self : Worker) : Obs Unit := do
  if ← liftPrefix (Env.condResched self) then schedule (some self)

theorem activationIter_erases (a : Activation) :
    ErasesPrefix (activationIter a) (Env.Activation.iter a) := by
  unfold activationIter
  split
  · rename_i h
    simpa only [Env.Activation.iter, h] using
      iter_erases (erasesPrefix_lift Env.napiSoftirq) (erasesPrefix_lift Env.napiIrqExit)
        (erasesPrefix_lift (Env.condResched .decryptWorker))
  · exact erasesPrefix_lift _

theorem activationRun_erases (a : Activation) :
    ErasesPrefix (activationRun a) (Env.Activation.run a) :=
  SourceScheduler.run_erases activationIter activationIter_erases a

theorem dispatch_erases (worker : Worker) : ErasesPrefix (dispatch worker) (Env.dispatch worker) :=
  SourceScheduler.dispatch_erases activationIter activationIter_erases worker

theorem schedule_erases (stack : Option Worker) : ErasesPrefix (schedule stack) (Env.schedule stack) :=
  SourceScheduler.schedule_erases activationIter _ activationIter_erases (erasesPrefix_lift _) stack

theorem nestedResched_erases (self : Worker) : ErasesPrefix (nestedResched self) (Env.nestedResched self) := by
  unfold nestedResched Env.nestedResched
  apply erasesPrefix_bind (erasesPrefix_lift _)
  intro b
  split
  · exact schedule_erases _
  · exact erasesPrefix_pure _

theorem inv_kernel (h : v.k = w.k) (hi : Inv deviceIndex initial hist w) :
    Inv deviceIndex initial hist v := by
  obtain ⟨r, hj, hc⟩ := hi
  exact ⟨r, hj, by simpa [cell, h] using hc⟩

theorem activationIter_preserves (a : Activation) :
    PrefixPreserves (Inv deviceIndex initial) (Safe initial) (activationIter a) := by
  unfold activationIter
  split
  · exact iter_preserves (lift_frame napiSoftirq_cell) (lift_frame napiIrqExit_cell)
      (lift_frame (kernel (condResched_sameKernel _)))
  · exact lift_frame (otherIter_cell a (by assumption))

theorem activationRun_preserves (a : Activation) :
    PrefixPreserves (Inv deviceIndex initial) (Safe initial) (activationRun a) :=
  SourceScheduler.run_preserves (I := Inv deviceIndex initial) (S := Safe initial) (fun _ _ hi => hi.safe) (fun _ _ _ he hi => inv_kernel he hi)
    activationIter activationIter_preserves a

theorem txWorkErase_preserves (pid : PeerId) :
    PrefixPreserves (Inv deviceIndex initial) (Safe initial)
      (liftPrefix (modifyDev fun d => {d with txWorkQueue := d.txWorkQueue.erase pid})) :=
  lift_frame (modifyDev_cell _ (fun _ => rfl) (fun _ => rfl))

theorem dispatch_preserves (worker : Worker) :
    PrefixPreserves (Inv deviceIndex initial) (Safe initial) (dispatch worker) :=
  SourceScheduler.dispatch_preserves (I := Inv deviceIndex initial) (S := Safe initial) (fun _ _ hi => hi.safe) (fun _ _ _ he hi => inv_kernel he hi)
    txWorkErase_preserves activationIter activationIter_preserves worker

theorem schedule_preserves (stack : Option Worker) :
    PrefixPreserves (Inv deviceIndex initial) (Safe initial) (schedule stack) :=
  SourceScheduler.schedule_preserves (I := Inv deviceIndex initial) (S := Safe initial) (fun _ _ hi => hi.safe) (fun _ _ _ he hi => inv_kernel he hi)
    txWorkErase_preserves activationIter _ activationIter_preserves (lift_frame napiSoftirq_cell) stack

theorem nestedResched_preserves (self : Worker) :
    PrefixPreserves (Inv deviceIndex initial) (Safe initial) (nestedResched self) := by
  unfold nestedResched
  apply PrefixPreserves.bind (lift_frame (kernel (condResched_sameKernel self)))
  intro b
  split
  · exact schedule_preserves _
  · exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _

/-- Entry calls and committed scheduler calls share the checked invariant;
this family makes no enclosing runner/operation or lifecycle claim. -/
inductive SchedulerCall : Type → Type
  | consume (msg : List UInt8) (src : SkbSource) (ds : Nat) : SchedulerCall Unit
  | iteration (a : Activation) : SchedulerCall IterResult
  | run (a : Activation) : SchedulerCall Unit
  | dispatch (worker : Worker) : SchedulerCall Bool
  | schedule (stack : Option Worker) : SchedulerCall Unit
  | nested (self : Worker) : SchedulerCall Unit

def SchedulerCall.observe : SchedulerCall α → Obs α
  | .consume msg src ds => RxRing.consume msg src ds
  | .iteration a => activationIter a
  | .run a => activationRun a
  | .dispatch w => RxRing.dispatch w
  | .schedule stack => RxRing.schedule stack
  | .nested self => nestedResched self

def SchedulerCall.original : SchedulerCall α → M α
  | .consume msg src ds => consumeData msg src ds
  | .iteration a => Env.Activation.iter a
  | .run a => Env.Activation.run a
  | .dispatch w => Env.dispatch w
  | .schedule stack => Env.schedule stack
  | .nested self => Env.nestedResched self

theorem SchedulerCall.erases (c : SchedulerCall α) : ErasesPrefix c.observe c.original := by
  cases c with
  | consume msg src ds => exact consume_erases msg src ds
  | iteration a => exact activationIter_erases a
  | run a => exact activationRun_erases a
  | dispatch w => exact dispatch_erases w
  | schedule stack => exact schedule_erases stack
  | nested self => exact nestedResched_erases self

theorem SchedulerCall.preserves (c : SchedulerCall α) :
    PrefixPreserves (Inv deviceIndex initial) (Safe initial) c.observe := by
  cases c with
  | consume msg src ds => exact consume_preserves msg src ds
  | iteration a => exact activationIter_preserves a
  | run a => exact activationRun_preserves a
  | dispatch w => exact dispatch_preserves w
  | schedule stack => exact schedule_preserves stack
  | nested self => exact nestedResched_preserves self

/-- Start from an initialized journal prefix, not necessarily an empty
current ring. Normal completion links its replay endpoint to the returned
World. A Stop yields only the reached history and an existential replay ring. -/
theorem SchedulerCall.initialized (c : SchedulerCall α)
    (hi : Inv deviceIndex (PtrRing.init n) h w) :
    let out := runPrefix c.observe w h
    ∃ r, Initialized n out.2 r ∧
      match out.1 with
      | .error _ => True
      | .ok (_, v) => cell v = some (deviceIndex, r) := by
  obtain ⟨_, _, hs, ho⟩ := c.preserves w h hi
  cases hout : (runPrefix c.observe w h).1 with
  | error e =>
    obtain ⟨r, hr⟩ := hs
    exact ⟨r, hr.initialized, by simp [hout]⟩
  | ok out =>
    simp only [hout] at ho
    obtain ⟨r, hr, hc⟩ := ho
    exact ⟨r, hr.initialized, by simpa [hout] using hc⟩

end Leanux.Proofs.WG.Queues.RxRing
