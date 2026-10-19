import Leanux.Proofs.WG.Roaming.RemoteChronologyFocusSource
import Leanux.Proofs.WG.Roaming.RemoteDriverSchedulerSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteChronology.Driver.Scheduler
open Leanux Leanux.WG Noise Lifetimes Queues Std.Do
open Leanux.Proofs.Framing Leanux.Proofs.Logged

open RxHistory.SchedulerSource

theorem atoms (entry : RemoteMap) :
    AtomContracts (Driver.Inv entry) RemoteDriver.Safe (fun {_} a => RemoteDriver.focus a) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro α a
    exact Driver.mixed_store entry _ _ (erasesPrefix_lift _)
      (fun _ => productAmbient_spec a _ (fun _ _ prior => prior))
  · intro α stop
    exact Driver.mixed_store entry _ _ (erasesPrefix_throw stop) (fun _ => hoare_throw stop)
  · intro pid
    exact Driver.mixed_native entry _ _ (getPeerMixed_erases pid)
      (fun before => RemoteSilent.of_frame before _ (RemoteSilent.getPeer_frame pid))
  · intro id
    exact Driver.mixed_native entry _ _ (getTxSkbPrefix_erases id)
      (fun before => RemoteSilent.of_frame before _ (RemoteWorkers.packet_frame (SkbStore.getTx id)))
  · intro f
    exact Driver.mixed_native entry _ _ (erasesStatePrefix_lift _)
      (fun before => RemoteSilent.of_frame before _ (modifyDev_remotes
        (fun d => {d with txWorkQueue:=f d.txWorkQueue}) (fun _ => rfl)))
  · intro a
    exact Driver.mixed_store entry _ _ (activationOccupancyPrefix_erases a)
      (activationOccupancy_sameKernel a)
  · intro next
    exact Driver.mixed_store entry _ _ (pendingNapiPrefix_erases next)
      (SourceScheduler.pendingNapi_kernel next)
  · intro a
    exact Driver.mixed_store entry _ _ (activationHasWorkPrefix_erases a)
      (activationHasWork_sameKernel a)
  · apply Driver.audit_store entry _ _ consistentFilterAudit_erases
    exact (show SameProductStore getAmbient from fun initial =>
      productAmbient_spec (get : AmbientM Ambient) _ (fun _ _ prior => prior)).bind
        (fun w => filterM_sameKernel productStoreView _ activationConsistent_sameKernel w.suspended)

theorem tx_preserves (entry : RemoteMap) (pid : PeerId) :
    PrefixPreserves (Driver.Inv entry) RemoteDriver.Safe (RemoteDriver.Scheduler.tx pid) :=
  Driver.focus_mixed entry _ _ (txIterPrefix_erases _ (erasesPrefix_lift _))
    (fun before => RemoteWorkers.txIter before pid)

theorem encrypt_preserves (entry : RemoteMap) :
    PrefixPreserves (Driver.Inv entry) RemoteDriver.Safe RemoteDriver.Scheduler.encrypt :=
  Driver.focus_relative entry _ Poll.encryptIteration_relative

theorem decrypt_preserves (entry : RemoteMap) :
    PrefixPreserves (Driver.Inv entry) RemoteDriver.Safe RemoteDriver.Scheduler.decrypt :=
  Driver.focus_relative entry _ Poll.decryptIteration_relative

theorem napi_preserves (entry : RemoteMap) :
    PrefixPreserves (Driver.Inv entry) RemoteDriver.Safe RemoteDriver.Scheduler.napi :=
  Driver.focus_relative entry _ Poll.softirq_relative

theorem ahead_preserves (entry : RemoteMap) (pid : PeerId) :
    PrefixPreserves (Driver.Inv entry) RemoteDriver.Safe (RemoteDriver.Scheduler.ahead pid) :=
  cryptAhead_preserves (Driver.safe entry) _ (atoms entry) _ (encrypt_preserves entry) pid

theorem iteration_preserves (entry : RemoteMap) (a : Activation) :
    PrefixPreserves (Driver.Inv entry) RemoteDriver.Safe (RemoteDriver.Scheduler.iteration a) :=
  RxHistory.SchedulerSource.iteration_preserves _ (atoms entry) _ _ _ _ _
    (encrypt_preserves entry) (ahead_preserves entry) (tx_preserves entry)
    (decrypt_preserves entry) (Driver.receiveIteration_preserves entry) a

theorem run_preserves (entry : RemoteMap) (a : Activation) :
    PrefixPreserves (Driver.Inv entry) RemoteDriver.Safe (RemoteDriver.Scheduler.run a) :=
  RxHistory.SchedulerSource.run_preserves (Driver.safe entry) (Driver.store_inv entry) _ (atoms entry) _
    (iteration_preserves entry) a

theorem dispatch_preserves (entry : RemoteMap) (worker : Worker) :
    PrefixPreserves (Driver.Inv entry) RemoteDriver.Safe (RemoteDriver.Scheduler.dispatch worker) :=
  RxHistory.SchedulerSource.dispatch_preserves (Driver.safe entry) (Driver.store_inv entry) _ (atoms entry) _
    (run_preserves entry) worker

theorem schedule_preserves (entry : RemoteMap) (stack : Option Worker) :
    PrefixPreserves (Driver.Inv entry) RemoteDriver.Safe (RemoteDriver.Scheduler.schedule stack) :=
  RxHistory.SchedulerSource.schedule_preserves (Driver.safe entry) (Driver.store_inv entry) _ (atoms entry) _ _ _
    (dispatch_preserves entry) (run_preserves entry) (napi_preserves entry) stack

theorem nested_preserves (entry : RemoteMap) (worker : Worker) :
    PrefixPreserves (Driver.Inv entry) RemoteDriver.Safe (RemoteDriver.Scheduler.nested worker) :=
  RxHistory.SchedulerSource.nested_preserves (Driver.safe entry) (Driver.store_inv entry) _
    (schedule_preserves entry) worker

end Leanux.Proofs.WG.Roaming.RemoteChronology.Driver.Scheduler
