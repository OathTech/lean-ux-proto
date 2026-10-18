import Leanux.Proofs.WG.Noise.DriverTagFlushSource
import Leanux.Proofs.WG.Noise.DriverTagCallerSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Noise.DriverTags.Flush
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do Lifetimes
universe u

/-! Actual callbacks and fully instantiated observers. Native coverage is a
normal-result contract; all-outcome safety asserts validity of emitted receipts.
The sender adapter emits only after the entire sender callback returns normally. -/

def clearWorkerObserved (pid : PeerId) : Obs Unit := do
  recordHelper (.handshakeClear pid) (fun _ => .cleared) (handshakeClear pid)
  liftWGPrefix (keypairsClear pid)
  liftWGPrefix (WG.peerPut (some pid))

theorem clearWorkerObserved_erases (pid : PeerId) :
    ErasesStatePrefix (clearWorkerObserved pid) (queuedExpiredZeroKeyMaterial pid) := by
  unfold clearWorkerObserved queuedExpiredZeroKeyMaterial
  exact erasesStatePrefix_bind (recordHelper_erases _ _ _) (fun _ =>
    erasesStatePrefix_bind (erasesStatePrefix_lift _) (fun _ => erasesStatePrefix_lift _))

theorem clearWorkerObserved_preserves (entry : TagMap) (pid : PeerId) :
    StatePrefixPreserves (fun h g _ => NativeInv entry h g) ValidHistory (clearWorkerObserved pid) := by
  unfold clearWorkerObserved
  exact StatePrefixEnsures.bind (recordHelper_preserves entry _ _ _ rfl) (fun _ =>
    StatePrefixEnsures.bind (lift_frame entry _ (keys_tags pid)) (fun _ =>
    lift_retained entry _ (Index.staging_tags _ (fun initial =>
      Index.staging_peerPut initial (some pid)))))

theorem dev_preserves (entry : TagMap) :
    StatePrefixPreserves (fun h g _ => NativeInv entry h g) ValidHistory (liftWGPrefix getDev) :=
  lift_frame entry _ (store_frame getDev_sameWGStore)

theorem deleted_preserves (entry : TagMap) (pid : PeerId) (timer : PeerTimer) :
    StatePrefixPreserves (fun h g _ => NativeInv entry h g) ValidHistory
      (liftWGPrefix (delTimer pid timer)) :=
  lift_exact entry _ (fun g ambient result final after run =>
    ResponseSuffix.delTimer_tag_frame pid timer g.dev g ambient result final after rfl run)


/-- Dequeue and named section boundaries remain in the original order.
The worker callback records its actual normal creator receipt. -/
def runFlushedSendObserved (pid : PeerId) : Obs Unit :=
  sendWith (fun {_} a => liftWGPrefix a) initiationWorker pid

/-- The clear receipt is emitted at its own primitive cut, before key and
reference releases or the original section-stop check. -/
def runFlushedClearObserved (pid : PeerId) : Obs Unit :=
  clearWith (fun {_} a => liftWGPrefix a) clearWorkerObserved pid

/-- Actual bounded drain, including both recorded and placeholder selection,
the original upper bound and early return after the selected clear worker. -/
def drainObserved (upTo : Option PeerId) : Obs Unit :=
  drainWith (fun {_} a => liftWGPrefix a) runFlushedSendObserved runFlushedClearObserved upTo

/-- Timer deletion followed by the original conditional drain. A drain may
run queued work for peers other than the supplied peer. -/
def timersStopObserved (pid : PeerId) : Obs Unit :=
  timersWith (fun {_} a => liftWGPrefix a)
    (fun peer timer => liftWGPrefix (delTimer peer timer)) drainObserved pid

theorem runFlushedSendObserved_erases (pid : PeerId) :
    ErasesStatePrefix (runFlushedSendObserved pid) (runFlushedSendWork pid) := by
  rw [send_factor]
  exact sendWith_erases initiationWorker handshakeSendWorker initiationWorker_erases pid

theorem runFlushedClearObserved_erases (pid : PeerId) :
    ErasesStatePrefix (runFlushedClearObserved pid) (runFlushedClearWork pid) := by
  rw [clear_factor]
  exact clearWith_erases clearWorkerObserved queuedExpiredZeroKeyMaterial clearWorkerObserved_erases pid

theorem drainObserved_erases (upTo : Option PeerId) :
    ErasesStatePrefix (drainObserved upTo) (drainHandshakeSendWq upTo) := by
  rw [drain_factor]
  exact drainWith_erases runFlushedSendObserved runFlushedClearObserved
    runFlushedSendWork runFlushedClearWork runFlushedSendObserved_erases
    runFlushedClearObserved_erases upTo

theorem timersStopObserved_erases (pid : PeerId) :
    ErasesStatePrefix (timersStopObserved pid) (timersStop pid) := by
  rw [timers_factor]
  exact timersWith_erases (fun peer timer => liftWGPrefix (delTimer peer timer)) drainObserved
    delTimer drainHandshakeSendWq (fun _ _ => erasesStatePrefix_lift _) drainObserved_erases pid

theorem runFlushedSendObserved_preserves (entry : TagMap) (pid : PeerId) :
    StatePrefixPreserves (fun h g _ => NativeInv entry h g) ValidHistory
      (runFlushedSendObserved pid) :=
  sendWith_preserves _ _ (fun _ _ _ hi => hi.2) initiationWorker
    (fun p => lift_frame entry _ (prepare_tags p)) (ambient_preserves entry)
    (initiationWorker_preserves entry) pid

theorem runFlushedClearObserved_preserves (entry : TagMap) (pid : PeerId) :
    StatePrefixPreserves (fun h g _ => NativeInv entry h g) ValidHistory
      (runFlushedClearObserved pid) :=
  clearWith_preserves _ _ (fun _ _ _ hi => hi.2) clearWorkerObserved
    (fun p => lift_frame entry _ (clearErase_tags p)) (ambient_preserves entry)
    (clearWorkerObserved_preserves entry) pid

theorem drainObserved_preserves (entry : TagMap) (upTo : Option PeerId) :
    StatePrefixPreserves (fun h g _ => NativeInv entry h g) ValidHistory (drainObserved upTo) :=
  drainWith_preserves _ _ (fun _ _ _ hi => hi.2) runFlushedSendObserved runFlushedClearObserved
    (ambient_preserves entry) (dev_preserves entry)
    (runFlushedSendObserved_preserves entry) (runFlushedClearObserved_preserves entry) upTo

theorem timersStopObserved_preserves (entry : TagMap) (pid : PeerId) :
    StatePrefixPreserves (fun h g _ => NativeInv entry h g) ValidHistory (timersStopObserved pid) :=
  timersWith_preserves _ _ (fun _ _ _ hi => hi.2)
    (fun peer timer => liftWGPrefix (delTimer peer timer)) drainObserved (dev_preserves entry)
    (deleted_preserves entry) (drainObserved_preserves entry) pid

end Leanux.Proofs.WG.Noise.DriverTags.Flush
