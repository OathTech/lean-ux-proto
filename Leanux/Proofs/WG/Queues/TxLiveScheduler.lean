import Leanux.Proofs.WG.Queues.TxLiveWorkers
import Leanux.Proofs.WG.Queues.TxLiveHandshake

/-! Concrete original worker and scheduler observers preserve Ready. The
scheduled receive path is the actual handshake consumer. Copied consistency
trials retain their original audit-only markers and are not committed steps. -/
namespace Leanux.Proofs.WG.Queues.TxDisposition.LiveScheduler
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open LiveFrontier LiveWorkers

abbrev Inv (_h : List RxHistory.Event) (w : World) : Prop := Ready w.wg

private theorem store (same : productStoreView v = productStoreView w) (hi : Inv h w) : Inv h v :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.TxLiveStack.«0».Leanux.Proofs.WG.Queues.TxDisposition.LiveFrontier.product_transport) same hi

private theorem mixed (g : PrefixM LifetimeEvent α) (original : Leanux.M α)
    (erase : ErasesPrefix g original) (keeps : Preserves (fun w : World=>Ready w.wg) original) :
    PrefixPreserves Inv (fun _=>True) (RxHistory.mixed g) :=
  observed _ _ (Appends.focus _ _ _) (RxHistory.mixed_erases erase) keeps

private theorem stored (g : PrefixM LifetimeEvent α) (original : Leanux.M α)
    (erase : ErasesPrefix g original) (frame : SameProductStore original) :
    PrefixPreserves Inv (fun _=>True) (RxHistory.mixed g) :=
  mixed g original erase (product_store frame)

theorem atoms : RxHistory.SchedulerSource.AtomContracts Inv (fun _=>True) (fun {_} g=>g) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro α a
    exact stored _ _ (erasesPrefix_lift _) (fun _=>productAmbient_spec a _ (fun _ _ hi=>hi))
  · intro α e
    exact stored _ _ (erasesPrefix_throw e) (fun _=>hoare_throw e)
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
      (PublicationPoll.native_product Ready _
        (modify_live (fun d=>{d with txWorkQueue:=f d.txWorkQueue}) (fun _=>rfl) (fun _=>rfl)))
  · intro a
    exact stored _ _ (activationOccupancyPrefix_erases a) (activationOccupancy_sameKernel a)
  · exact stored _ _ activationRefillsPrefix_erases activationRefills_sameKernel
  · intro next
    exact stored _ _ (pendingNapiPrefix_erases next) (SourceScheduler.pendingNapi_kernel next)
  · intro a
    exact stored _ _ (activationHasWorkPrefix_erases a) (activationHasWork_sameKernel a)
  · apply observed _ _ (Appends.focus _ _ _) (RxHistory.audit_erases consistentFilterAudit_erases)
    apply product_store
    exact (show SameProductStore getAmbient from fun _=>
      productAmbient_spec (get : AmbientM Ambient) _ (fun _ _ hi=>hi)).bind
        (fun w=>filterM_sameKernel productStoreView _ activationConsistent_sameKernel w.suspended)

theorem receive : PrefixPreserves Inv (fun _=>True) Origins.HistoryAdapters.receiveIteration := by
  unfold Origins.HistoryAdapters.receiveIteration
  apply workerIterPrefix_preserves _ _ (fun _ _ _=>True.intro)
  · exact observed _ _ (Appends.focus _ _ _) Origins.HistoryAdapters.receiveStep_erases
      (PublicationPoll.native_product Ready _ receive_step)
  · exact observed _ _ (Appends.lift _) (erasesPrefix_lift _)
      (product_store (condResched_sameKernel .receiveWorker))

theorem ahead (pid : PeerId) : PrefixPreserves Inv (fun _=>True) (RxHistory.cryptAhead pid) := by
  rw [RxHistory.SchedulerSource.cryptAhead_factor]
  exact RxHistory.SchedulerSource.cryptAhead_preserves (fun _ _ _=>True.intro) _ atoms _ encrypt_observed pid

theorem iteration (a : Activation) :
    PrefixPreserves Inv (fun _=>True) (RxHistory.activationIteration a) := by
  rw [RxHistory.SchedulerSource.iteration_factor]
  exact RxHistory.SchedulerSource.iteration_preserves _ atoms _ _ _ _ _
    encrypt_observed ahead tx_observed decrypt_observed receive a

theorem run (a : Activation) : PrefixPreserves Inv (fun _=>True) (RxHistory.activationRun a) := by
  rw [RxHistory.SchedulerSource.run_factor]
  exact RxHistory.SchedulerSource.run_preserves (I:=Inv) (fun _ _ _=>True.intro)
    (fun _ _ _ same hi=>store same hi) _ atoms _ iteration a

theorem dispatch (worker : Worker) : PrefixPreserves Inv (fun _=>True) (RxHistory.dispatch worker) := by
  rw [RxHistory.SchedulerSource.dispatch_factor]
  exact RxHistory.SchedulerSource.dispatch_preserves (I:=Inv) (fun _ _ _=>True.intro)
    (fun _ _ _ same hi=>store same hi) _ atoms _ run worker

theorem schedule (stack : Option Worker) : PrefixPreserves Inv (fun _=>True) (RxHistory.schedule stack) := by
  rw [RxHistory.SchedulerSource.schedule_factor]
  exact RxHistory.SchedulerSource.schedule_preserves (I:=Inv) (fun _ _ _=>True.intro)
    (fun _ _ _ same hi=>store same hi) _ atoms _ _ _ dispatch run LiveNapi.softirq_observed stack

theorem nested (worker : Worker) : PrefixPreserves Inv (fun _=>True) (RxHistory.nestedResched worker) := by
  rw [RxHistory.SchedulerSource.nested_factor]
  exact RxHistory.SchedulerSource.nested_preserves (I:=Inv) (fun _ _ _=>True.intro)
    (fun _ _ _ same hi=>store same hi) _ schedule worker

/-- The same observer run supplies the normal native endpoint. -/
private theorem native {action : RxHistory.Obs α} {original : Leanux.M α}
    (keep : PrefixPreserves Inv (fun _=>True) action) (erase : ErasesPrefix action original) :
    Preserves (fun w : World=>Ready w.wg) original :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.TxLiveStack.«0».Leanux.Proofs.WG.Queues.TxDisposition.LiveFrontier.native_of_source)
    action original erase keep

theorem ahead_native (pid : PeerId) : Preserves (fun w : World=>Ready w.wg) (Env.cryptAhead pid) :=
  native (ahead pid) (RxHistory.cryptAhead_erases pid)

theorem iteration_native (a : Activation) : Preserves (fun w : World=>Ready w.wg) (Env.Activation.iter a) :=
  native (iteration a) (RxHistory.activationIteration_erases a)

theorem run_native (a : Activation) : Preserves (fun w : World=>Ready w.wg) (Env.Activation.run a) :=
  native (run a) (RxHistory.activationRun_erases a)

theorem dispatch_native (worker : Worker) : Preserves (fun w : World=>Ready w.wg) (Env.dispatch worker) :=
  native (dispatch worker) (RxHistory.dispatch_erases worker)

theorem schedule_native (stack : Option Worker) : Preserves (fun w : World=>Ready w.wg) (Env.schedule stack) :=
  native (schedule stack) (RxHistory.schedule_erases stack)

theorem nested_native (worker : Worker) : Preserves (fun w : World=>Ready w.wg) (Env.nestedResched worker) :=
  native (nested worker) (RxHistory.nestedResched_erases worker)

end Leanux.Proofs.WG.Queues.TxDisposition.LiveScheduler
