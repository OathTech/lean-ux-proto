import Leanux.Proofs.WG.Noise.DriverTagSilentSource
import Leanux.Proofs.WG.Noise.DriverTagProductSource
import Leanux.Proofs.WG.Noise.DriverTagCallerSource
import Leanux.Proofs.WG.Queues.SchedulerPreservation
import Leanux.Proofs.WG.Queues.NapiSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.DriverTags.Scheduler
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues
open RxHistory.SchedulerSource

theorem native_observed {α : Type} (entry : TagMap) (g : Obs α)
    (proof : StatePrefixPreserves (fun h w _ => NativeInv entry h w) ValidHistory g) :
    PrefixPreserves (StateInv entry) ValidHistory (liftWGObserver g) :=
  proof.liftWGObserver.preserves

theorem lift_kept {α : Type} (entry : TagMap) (a : Leanux.M α)
    (kept : ∀ initial, Preserves (fun w : World => Silent.Retained initial w.wg) a) :
    PrefixPreserves (StateInv entry) ValidHistory (liftPrefix a) := by
  apply PrefixEnsures.preserves
  apply PrefixEnsures.lift a (safe entry)
  intro h w value final prior run
  exact ⟨prior.1.final_retained ((hoare_iff_run _ _ _).mp (kept (tagView w.wg))
    w value final (TagsRetained.refl _) run),prior.2⟩

/-- Every discarded observer is a specific read, retained queue edit, ambient
operation, or copied consistency probe. No worker is hidden in this family. -/
theorem atoms (entry : TagMap) :
    AtomContracts (StateInv entry) ValidHistory (fun {_} a => DriverTags.discard a) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro α a
    exact discard_store entry _ _ (RxHistory.mixed_erases (erasesPrefix_lift _))
      (fun _ => productAmbient_spec a _ (fun _ _ hi => hi))
  · intro α e
    exact discard_store entry _ _ (RxHistory.mixed_erases (erasesPrefix_throw e))
      (fun _ => hoare_throw e)
  · intro pid
    exact discard_native_frame entry _ _ (RxHistory.mixed_erases
      (liftWGObserver_erases (getPeerMixed_erases pid))) (getPeer_frame pid)
  · intro id
    exact discard_native_frame entry _ _ (RxHistory.mixed_erases
      (liftWGObserver_erases (getTxSkbPrefix_erases id))) (Silent.packet_frame (SkbStore.getTx id))
  · intro f
    exact discard_native_frame entry _ _ (RxHistory.mixed_erases
      (liftWGObserver_erases (erasesStatePrefix_lift _)))
      (modifyDev_frame (fun d => {d with txWorkQueue := f d.txWorkQueue}) (fun _ => rfl))
  · intro a
    exact discard_store entry _ _ (RxHistory.mixed_erases (activationOccupancyPrefix_erases a))
      (activationOccupancy_sameKernel a)
  · exact discard_store entry _ _ (RxHistory.mixed_erases activationRefillsPrefix_erases)
      activationRefills_sameKernel
  · intro next
    exact discard_store entry _ _ (RxHistory.mixed_erases (pendingNapiPrefix_erases next))
      (SourceScheduler.pendingNapi_kernel next)
  · intro a
    exact discard_store entry _ _ (RxHistory.mixed_erases (activationHasWorkPrefix_erases a))
      (activationHasWork_sameKernel a)
  · apply discard_store entry _ _ (RxHistory.audit_erases consistentFilterAudit_erases)
    exact (show SameProductStore getAmbient from fun initial =>
      productAmbient_spec (get : AmbientM Ambient) _ (fun _ _ hi => hi)).bind
      (fun w => filterM_sameKernel productStoreView _ activationConsistent_sameKernel w.suspended)

def encrypt (softirq : ProductObs Unit) : ProductObs IterResult := do
  let item ← liftWGObserver (liftWGPrefix TxRing.pollSource)
  softirq
  liftPrefix (RxWorkers.encryptTailSource item)

def decryptStep (softirq irq : ProductObs Unit) : ProductObs Bool :=
  RxWorkers.decryptWith (liftWGObserver (liftWGPrefix RxWorkers.prepareSource))
    (fun pid => liftWGObserver (liftWGPrefix (peerPut (some pid)))) softirq irq

def decrypt (softirq irq : ProductObs Unit) : ProductObs IterResult :=
  workerIterPrefix .decryptWorker none (decryptStep softirq irq)
    (do liftPrefix (branch .decWorkerNeedResched (← liftPrefix (Env.condResched .decryptWorker))))

def transmit (pid : PeerId) : ProductObs IterResult :=
  liftPrefix (txIter pid (Env.condResched .txWorker))

/-- Reception receipts have the existing completed-receive-step semantics:
an enclosing receiveStep Stop does not return an internal receipt bundle. -/
def receive : ProductObs IterResult :=
  workerIterPrefix .receiveWorker none (liftWGObserver receiveStepCompleted)
    (liftPrefix (Env.condResched .receiveWorker))

theorem encrypt_erases (softirq : ProductObs Unit) (hs : ErasesPrefix softirq Env.napiSoftirq) :
    ErasesPrefix (encrypt softirq)
      (encryptIter Env.checksumHelp Env.napiSoftirq (Env.condResched .encryptWorker)) := by
  rw [RxWorkers.encrypt_source]
  exact erasesPrefix_bind (liftWGObserver_erases (erasesStatePrefix_lift _))
    (fun _ => erasesPrefix_bind hs (fun _ => erasesPrefix_lift _))

theorem decryptStep_erases (softirq irq : ProductObs Unit)
    (hs : ErasesPrefix softirq Env.napiSoftirq) (hi : ErasesPrefix irq Env.napiIrqExit) :
    ErasesPrefix (decryptStep softirq irq) (WG.decryptStep Env.napiSoftirq Env.napiIrqExit) :=
  NapiSource.decrypt_erases (liftWGObserver_erases (erasesStatePrefix_lift _))
    (fun _ => liftWGObserver_erases (erasesStatePrefix_lift _)) hs hi

theorem decrypt_erases (softirq irq : ProductObs Unit)
    (hs : ErasesPrefix softirq Env.napiSoftirq) (hi : ErasesPrefix irq Env.napiIrqExit) :
    ErasesPrefix (decrypt softirq irq)
      (decryptIter Env.napiSoftirq Env.napiIrqExit (Env.condResched .decryptWorker)) :=
  workerIterPrefix_erases _ _ (decryptStep_erases softirq irq hs hi)
    (erasesPrefix_bind (erasesPrefix_lift _) (fun _ => erasesPrefix_lift _))

theorem transmit_erases (pid : PeerId) :
    ErasesPrefix (transmit pid) (txIter pid (Env.condResched .txWorker)) :=
  erasesPrefix_lift _

theorem receive_erases :
    ErasesPrefix receive (workerIter .receiveWorker none (liftWG WG.receiveStep) (Env.condResched .receiveWorker)) :=
  workerIterPrefix_erases _ _ (liftWGObserver_erases receiveStepCompleted_erases) (erasesPrefix_lift _)

theorem encrypt_preserves (entry : TagMap) (softirq : ProductObs Unit)
    (hs : PrefixPreserves (StateInv entry) ValidHistory softirq) :
    PrefixPreserves (StateInv entry) ValidHistory (encrypt softirq) :=
  PrefixPreserves.bind (native_observed entry _ (Silent.encryptPoll_preserves entry))
    (fun item => PrefixPreserves.bind hs (fun _ =>
      lift_kept entry _ (fun initial => Silent.encryptTail_retained initial item)))

theorem decryptStep_preserves (entry : TagMap) (softirq irq : ProductObs Unit)
    (hs : PrefixPreserves (StateInv entry) ValidHistory softirq)
    (hi : PrefixPreserves (StateInv entry) ValidHistory irq) :
    PrefixPreserves (StateInv entry) ValidHistory (decryptStep softirq irq) :=
  NapiSource.decrypt_preserves (safe entry)
    (native_observed entry _ (Silent.decryptPrepare_preserves entry))
    (fun pid => native_observed entry _ (Silent.lift_preserves entry _ (fun initial => Silent.peerPut initial (some pid))))
    hs hi

theorem decrypt_preserves (entry : TagMap) (softirq irq : ProductObs Unit)
    (hs : PrefixPreserves (StateInv entry) ValidHistory softirq)
    (hi : PrefixPreserves (StateInv entry) ValidHistory irq) :
    PrefixPreserves (StateInv entry) ValidHistory (decrypt softirq irq) :=
  workerIterPrefix_preserves _ _ (safe entry) (decryptStep_preserves entry softirq irq hs hi)
    (PrefixPreserves.bind (lift_product_store entry _ (condResched_sameKernel _))
      (fun result => lift_product_store entry _ (fun _ =>
        productAmbient_spec (AmbientM.branch _ result) _ (fun _ _ prior => prior))))

theorem transmit_preserves (entry : TagMap) (pid : PeerId) :
    PrefixPreserves (StateInv entry) ValidHistory (transmit pid) :=
  lift_kept entry _ (fun initial => Silent.txIter_retained initial pid _
    (Silent.product_store initial _ (condResched_sameKernel _)))

theorem receive_preserves (entry : TagMap) :
    PrefixPreserves (StateInv entry) ValidHistory receive :=
  workerIterPrefix_preserves _ _ (safe entry)
    (native_observed entry _ (receiveStepCompleted_preserves entry))
    (lift_product_store entry _ (condResched_sameKernel _))

/-- Callback factories reuse the existing control flow. The consistency probe
continues to run the original activation on copied Worlds. -/
def ahead (softirq : ProductObs Unit) (pid : PeerId) : ProductObs Unit :=
  cryptAheadWith (fun {_} a => DriverTags.discard a) (encrypt softirq) pid

def iteration (softirq irq : ProductObs Unit) (a : Activation) : ProductObs IterResult :=
  iterationWith (fun {_} x => DriverTags.discard x) (encrypt softirq) (ahead softirq)
    transmit (decrypt softirq irq) receive a

def run (softirq irq : ProductObs Unit) (a : Activation) : ProductObs Unit :=
  runWith (fun {_} x => DriverTags.discard x) (iteration softirq irq) a

def dispatch (softirq irq : ProductObs Unit) (worker : Worker) : ProductObs Bool :=
  dispatchWith (fun {_} x => DriverTags.discard x) (run softirq irq) worker

def schedule (softirq irq : ProductObs Unit) (stack : Option Worker := none) : ProductObs Unit :=
  scheduleWith (fun {_} x => DriverTags.discard x) (dispatch softirq irq) (run softirq irq) softirq stack

def nested (softirq irq : ProductObs Unit) (worker : Worker) : ProductObs Unit :=
  nestedWith (fun stack => schedule softirq irq stack) worker

theorem ahead_preserves (entry : TagMap) (softirq : ProductObs Unit)
    (hs : PrefixPreserves (StateInv entry) ValidHistory softirq) (pid : PeerId) :
    PrefixPreserves (StateInv entry) ValidHistory (ahead softirq pid) :=
  cryptAhead_preserves (safe entry) _ (atoms entry) _ (encrypt_preserves entry softirq hs) pid

theorem iteration_preserves (entry : TagMap) (softirq irq : ProductObs Unit)
    (hs : PrefixPreserves (StateInv entry) ValidHistory softirq)
    (hi : PrefixPreserves (StateInv entry) ValidHistory irq) (a : Activation) :
    PrefixPreserves (StateInv entry) ValidHistory (iteration softirq irq a) :=
  RxHistory.SchedulerSource.iteration_preserves _ (atoms entry) _ _ _ _ _
    (encrypt_preserves entry softirq hs) (ahead_preserves entry softirq hs)
    (transmit_preserves entry) (decrypt_preserves entry softirq irq hs hi) (receive_preserves entry) a

theorem run_preserves (entry : TagMap) (softirq irq : ProductObs Unit)
    (hs : PrefixPreserves (StateInv entry) ValidHistory softirq)
    (hi : PrefixPreserves (StateInv entry) ValidHistory irq) (a : Activation) :
    PrefixPreserves (StateInv entry) ValidHistory (run softirq irq a) :=
  RxHistory.SchedulerSource.run_preserves (safe entry) (state_product_store entry) _ (atoms entry) _
    (iteration_preserves entry softirq irq hs hi) a

theorem dispatch_preserves (entry : TagMap) (softirq irq : ProductObs Unit)
    (hs : PrefixPreserves (StateInv entry) ValidHistory softirq)
    (hi : PrefixPreserves (StateInv entry) ValidHistory irq) (worker : Worker) :
    PrefixPreserves (StateInv entry) ValidHistory (dispatch softirq irq worker) :=
  RxHistory.SchedulerSource.dispatch_preserves (safe entry) (state_product_store entry) _ (atoms entry) _
    (run_preserves entry softirq irq hs hi) worker

theorem schedule_preserves (entry : TagMap) (softirq irq : ProductObs Unit)
    (hs : PrefixPreserves (StateInv entry) ValidHistory softirq)
    (hi : PrefixPreserves (StateInv entry) ValidHistory irq) (stack : Option Worker) :
    PrefixPreserves (StateInv entry) ValidHistory (schedule softirq irq stack) :=
  RxHistory.SchedulerSource.schedule_preserves (safe entry) (state_product_store entry) _ (atoms entry) _ _ _
    (dispatch_preserves entry softirq irq hs hi) (run_preserves entry softirq irq hs hi) hs stack

theorem nested_preserves (entry : TagMap) (softirq irq : ProductObs Unit)
    (hs : PrefixPreserves (StateInv entry) ValidHistory softirq)
    (hi : PrefixPreserves (StateInv entry) ValidHistory irq) (worker : Worker) :
    PrefixPreserves (StateInv entry) ValidHistory (nested softirq irq worker) :=
  RxHistory.SchedulerSource.nested_preserves (safe entry) (state_product_store entry) _
    (schedule_preserves entry softirq irq hs hi) worker

theorem old_lift {α : Type} (a : Leanux.M α) :
    DriverTags.discard (RxHistory.mixed (liftPrefix a)) = liftPrefix a :=
  discard_eq _ a (RxHistory.mixed_erases (erasesPrefix_lift a))

theorem old_native {α : Type} (a : WG.M α) :
    DriverTags.discard (RxHistory.mixed (liftWGObserver (liftWGPrefix a))) = liftPrefix (liftWG a) :=
  discard_eq _ _ (RxHistory.mixed_erases (liftWGObserver_erases (erasesStatePrefix_lift a)))

theorem old_peer (pid : PeerId) :
    DriverTags.discard (RxHistory.mixed (liftWGObserver (getPeerMixed pid))) = liftPrefix (liftWG (getPeer pid)) :=
  discard_eq _ _ (RxHistory.mixed_erases (liftWGObserver_erases (getPeerMixed_erases pid)))

theorem old_packet (id : SkbId) :
    DriverTags.discard (RxHistory.mixed (liftWGObserver (getTxSkbPrefix id))) = liftPrefix (liftWG (getTxSkb id)) :=
  discard_eq _ _ (RxHistory.mixed_erases (liftWGObserver_erases (getTxSkbPrefix_erases id)))

theorem old_throw {α : Type} (stop : Stop) :
    DriverTags.discard (RxHistory.mixed (throw stop : PrefixM LifetimeEvent α)) = liftPrefix (throw stop) :=
  discard_eq _ _ (RxHistory.mixed_erases (erasesPrefix_throw stop))

theorem ahead_erases (softirq : ProductObs Unit) (hs : ErasesPrefix softirq Env.napiSoftirq) (pid : PeerId) :
    ErasesPrefix (ahead softirq pid) (Env.cryptAhead pid) := by
  unfold ahead cryptAheadWith Env.cryptAhead
  simp only [old_lift,old_native,old_peer,old_packet,old_throw]
  repeat' first
    | exact encrypt_erases softirq hs
    | (maintenance_head liftPrefix; exact erasesPrefix_lift _)
    | (maintenance_head Pure.pure; exact erasesPrefix_pure _)
    | (maintenance_head Bind.bind; apply erasesPrefix_bind)
    | (with_reducible split; all_goals try simp_all only []; all_goals try subst_vars)
    | maintenance_intro

theorem iteration_erases (softirq irq : ProductObs Unit)
    (hs : ErasesPrefix softirq Env.napiSoftirq) (hi : ErasesPrefix irq Env.napiIrqExit) (a : Activation) :
    ErasesPrefix (iteration softirq irq a) (Env.Activation.iter a) := by
  unfold iteration iterationWith Env.Activation.iter
  simp only [old_lift]
  repeat' first
    | exact encrypt_erases softirq hs
    | exact decrypt_erases softirq irq hs hi
    | exact ahead_erases softirq hs _
    | exact transmit_erases _
    | exact receive_erases
    | (maintenance_head liftPrefix; exact erasesPrefix_lift _)
    | (maintenance_head Bind.bind; apply erasesPrefix_bind)
    | (with_reducible split; all_goals try simp_all only []; all_goals try subst_vars)
    | maintenance_intro

theorem run_source (softirq irq : ProductObs Unit) (a : Activation) :
    run softirq irq a = SourceScheduler.run (iteration softirq irq) a := by
  unfold run runWith SourceScheduler.run
  simp only [discard_eq _ _ (RxHistory.mixed_erases (activationOccupancyPrefix_erases a)),
    discard_eq _ _ (RxHistory.mixed_erases activationRefillsPrefix_erases)]
  rfl

theorem dispatch_source (softirq irq : ProductObs Unit) (worker : Worker) :
    dispatch softirq irq worker = SourceScheduler.dispatch (iteration softirq irq) worker := by
  unfold dispatch dispatchWith SourceScheduler.dispatch
  simp only [old_native,run_source]
  rfl

theorem old_trial :
    DriverTags.discard (RxHistory.audit consistentFilterAudit) =
      (do let w ← liftPrefix getAmbient
          liftPrefix (w.suspended.filterM Env.Activation.consistent) : ProductObs (List Activation)) := by
  rw [discard_eq _ _ (RxHistory.audit_erases consistentFilterAudit_erases)]
  rfl

theorem schedule_source (softirq irq : ProductObs Unit) (stack : Option Worker) :
    schedule softirq irq stack = SourceScheduler.schedule (iteration softirq irq) softirq stack := by
  unfold schedule scheduleWith SourceScheduler.schedule
  simp only [dispatch_source,run_source,
    discard_eq _ _ (RxHistory.mixed_erases (pendingNapiPrefix_erases _)),
    discard_eq _ _ (RxHistory.mixed_erases (activationHasWorkPrefix_erases _)),
    old_trial,bind_assoc]
  rfl

theorem run_erases (softirq irq : ProductObs Unit)
    (hs : ErasesPrefix softirq Env.napiSoftirq) (hi : ErasesPrefix irq Env.napiIrqExit) (a : Activation) :
    ErasesPrefix (run softirq irq a) (Env.Activation.run a) := by
  rw [run_source]
  exact SourceScheduler.run_erases _ (iteration_erases softirq irq hs hi) a

theorem dispatch_erases (softirq irq : ProductObs Unit)
    (hs : ErasesPrefix softirq Env.napiSoftirq) (hi : ErasesPrefix irq Env.napiIrqExit) (worker : Worker) :
    ErasesPrefix (dispatch softirq irq worker) (Env.dispatch worker) := by
  rw [dispatch_source]
  exact SourceScheduler.dispatch_erases _ (iteration_erases softirq irq hs hi) worker

theorem schedule_erases (softirq irq : ProductObs Unit)
    (hs : ErasesPrefix softirq Env.napiSoftirq) (hi : ErasesPrefix irq Env.napiIrqExit) (stack : Option Worker) :
    ErasesPrefix (schedule softirq irq stack) (Env.schedule stack) := by
  rw [schedule_source]
  exact SourceScheduler.schedule_erases _ _ (iteration_erases softirq irq hs hi) hs stack

theorem nested_erases (softirq irq : ProductObs Unit)
    (hs : ErasesPrefix softirq Env.napiSoftirq) (hi : ErasesPrefix irq Env.napiIrqExit) (worker : Worker) :
    ErasesPrefix (nested softirq irq worker) (Env.nestedResched worker) := by
  unfold nested nestedWith Env.nestedResched
  apply erasesPrefix_bind (erasesPrefix_lift _)
  intro ready
  split
  · exact schedule_erases softirq irq hs hi _
  · exact erasesPrefix_pure _

end Leanux.Proofs.WG.Noise.DriverTags.Scheduler
