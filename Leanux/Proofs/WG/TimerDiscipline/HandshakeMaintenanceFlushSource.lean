import Leanux.Proofs.WG.TimerDiscipline.HandshakeFocusSource
import Leanux.Proofs.WG.TimerDiscipline.HandshakeJournalAppendSource
import Leanux.Proofs.WG.Noise.DriverTagFlushSource
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.HandshakeMaintenance
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes
open HandshakeJournal
abbrev Obs := WGPrefix Event

theorem quiet_preserves {α : Type} (S : List Event → Prop) (a : WG.M α) :
    StatePrefixPreserves (fun h _ _ => S h) S (liftWGPrefix a) :=
  StatePrefixEnsures.lift a (fun _ _ _ h => h) (fun _ _ _ _ _ _ h _ => h)

def sendWorker (pid : PeerId) : Obs Unit :=
  focusStatePrefix Event.hook decodeHook (HookJournal.Initiation.workerObserved pid)
theorem sendWorker_erases (pid : PeerId) :
    ErasesStatePrefix (sendWorker pid) (handshakeSendWorker pid) :=
  focusStatePrefix_erases _ _ (HookJournal.Initiation.worker_erases pid)
theorem sendWorker_valid (pid : PeerId) :
    StatePrefixPreserves (fun h _ _ => ValidHistory h) ValidHistory (sendWorker pid) :=
  focus_native_valid (HookJournal.Initiation.worker_preserves pid)
theorem sendWorker_paired (pid : PeerId) :
    StatePrefixPreserves (fun h _ _ => Paired h) Paired (sendWorker pid) :=
  focus_native_paired (HookJournal.Initiation.worker_appends pid)
    (HookJournal.initiation_worker_derived_frame pid)
theorem sendWorker_appends (pid : PeerId) : StateAppends (sendWorker pid) :=
  StateAppends.focus _ _ _

def send (pid : PeerId) : Obs Unit :=
  Noise.DriverTags.Flush.sendWith (fun {_} a => liftWGPrefix a) sendWorker pid
def clear (pid : PeerId) : Obs Unit :=
  Noise.DriverTags.Flush.clearWith (fun {_} a => liftWGPrefix a)
    (fun p => liftWGPrefix (queuedExpiredZeroKeyMaterial p)) pid
def drain (upTo : Option PeerId) : Obs Unit :=
  Noise.DriverTags.Flush.drainWith (fun {_} a => liftWGPrefix a) send clear upTo
def timersStop (pid : PeerId) : Obs Unit :=
  Noise.DriverTags.Flush.timersWith (fun {_} a => liftWGPrefix a)
    (fun p t => liftWGPrefix (delTimer p t)) drain pid

theorem send_erases (pid : PeerId) : ErasesStatePrefix (send pid) (runFlushedSendWork pid) := by
  rw [Noise.DriverTags.Flush.send_factor]
  exact Noise.DriverTags.Flush.sendWith_erases _ _ sendWorker_erases pid
theorem clear_erases (pid : PeerId) : ErasesStatePrefix (clear pid) (runFlushedClearWork pid) := by
  rw [Noise.DriverTags.Flush.clear_factor]
  exact Noise.DriverTags.Flush.clearWith_erases _ _ (fun _ => erasesStatePrefix_lift _) pid
theorem drain_erases (upTo : Option PeerId) :
    ErasesStatePrefix (drain upTo) (drainHandshakeSendWq upTo) := by
  rw [Noise.DriverTags.Flush.drain_factor]
  exact Noise.DriverTags.Flush.drainWith_erases _ _ _ _ send_erases clear_erases upTo
theorem timersStop_erases (pid : PeerId) : ErasesStatePrefix (timersStop pid) (WG.timersStop pid) := by
  rw [Noise.DriverTags.Flush.timers_factor]
  exact Noise.DriverTags.Flush.timersWith_erases _ _ _ _
    (fun _ _ => erasesStatePrefix_lift _) drain_erases pid

theorem send_preserves (S : List Event → Prop)
    (hs : ∀ pid, StatePrefixPreserves (fun h _ _ => S h) S (sendWorker pid)) (pid : PeerId) :
    StatePrefixPreserves (fun h _ _ => S h) S (send pid) :=
  Noise.DriverTags.Flush.sendWith_preserves (fun h _ _ => S h) S (fun _ _ _ h => h) sendWorker
    (fun _ => quiet_preserves S _) (fun _ => quiet_preserves S _) hs pid
theorem clear_preserves (S : List Event → Prop) (pid : PeerId) :
    StatePrefixPreserves (fun h _ _ => S h) S (clear pid) :=
  Noise.DriverTags.Flush.clearWith_preserves (fun h _ _ => S h) S (fun _ _ _ h => h)
    (fun p => liftWGPrefix (queuedExpiredZeroKeyMaterial p))
    (fun _ => quiet_preserves S _) (fun _ => quiet_preserves S _)
    (fun _ => quiet_preserves S _) pid
theorem drain_preserves (S : List Event → Prop)
    (hs : ∀ pid, StatePrefixPreserves (fun h _ _ => S h) S (sendWorker pid)) (upTo : Option PeerId) :
    StatePrefixPreserves (fun h _ _ => S h) S (drain upTo) :=
  Noise.DriverTags.Flush.drainWith_preserves (fun h _ _ => S h) S (fun _ _ _ h => h) send clear
    (fun _ => quiet_preserves S _) (quiet_preserves S _) (send_preserves S hs)
    (clear_preserves S) upTo
theorem timersStop_preserves (S : List Event → Prop)
    (hs : ∀ pid, StatePrefixPreserves (fun h _ _ => S h) S (sendWorker pid)) (pid : PeerId) :
    StatePrefixPreserves (fun h _ _ => S h) S (timersStop pid) :=
  Noise.DriverTags.Flush.timersWith_preserves (fun h _ _ => S h) S (fun _ _ _ h => h)
    (fun p t => liftWGPrefix (delTimer p t)) drain
    (quiet_preserves S _) (fun _ _ => quiet_preserves S _) (drain_preserves S hs) pid

theorem send_valid (pid : PeerId) :
    StatePrefixPreserves (fun h _ _ => ValidHistory h) ValidHistory (send pid) :=
  send_preserves ValidHistory sendWorker_valid pid

theorem send_paired (pid : PeerId) :
    StatePrefixPreserves (fun h _ _ => Paired h) Paired (send pid) :=
  send_preserves Paired sendWorker_paired pid

theorem send_appends (pid : PeerId) : StateAppends (send pid) :=
  true_appends _ (send_preserves (fun _ => True) (fun p => appends_true _ (sendWorker_appends p)) pid)

theorem clear_valid (pid : PeerId) :
    StatePrefixPreserves (fun h _ _ => ValidHistory h) ValidHistory (clear pid) :=
  clear_preserves ValidHistory pid

theorem clear_paired (pid : PeerId) :
    StatePrefixPreserves (fun h _ _ => Paired h) Paired (clear pid) :=
  clear_preserves Paired pid

theorem clear_appends (pid : PeerId) : StateAppends (clear pid) :=
  true_appends _ (clear_preserves (fun _ => True) pid)

theorem drain_valid (upTo : Option PeerId) :
    StatePrefixPreserves (fun h _ _ => ValidHistory h) ValidHistory (drain upTo) :=
  drain_preserves ValidHistory sendWorker_valid upTo

theorem drain_paired (upTo : Option PeerId) :
    StatePrefixPreserves (fun h _ _ => Paired h) Paired (drain upTo) :=
  drain_preserves Paired sendWorker_paired upTo

theorem drain_appends (upTo : Option PeerId) : StateAppends (drain upTo) :=
  true_appends _ (drain_preserves (fun _ => True) (fun p => appends_true _ (sendWorker_appends p)) upTo)

theorem timersStop_valid (pid : PeerId) :
    StatePrefixPreserves (fun h _ _ => ValidHistory h) ValidHistory (timersStop pid) :=
  timersStop_preserves ValidHistory sendWorker_valid pid

theorem timersStop_paired (pid : PeerId) :
    StatePrefixPreserves (fun h _ _ => Paired h) Paired (timersStop pid) :=
  timersStop_preserves Paired sendWorker_paired pid

theorem timersStop_appends (pid : PeerId) : StateAppends (timersStop pid) :=
  true_appends _ (timersStop_preserves (fun _ => True) (fun p => appends_true _ (sendWorker_appends p)) pid)
end Leanux.Proofs.WG.TimerDiscipline.HandshakeMaintenance
