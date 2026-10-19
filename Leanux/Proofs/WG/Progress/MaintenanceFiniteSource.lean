import Leanux.Proofs.WG.Progress.InitiationCallerFiniteSource
import Leanux.Proofs.WG.Noise.DriverTagFlushFactors
import Leanux.Proofs.WG.Noise.DriverTagRemovalFactors
import Leanux.Proofs.WG.Noise.DriverTagControlFactors

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.MaintenanceFinite
open Leanux Leanux.WG
open Leanux.Proofs.WG.Noise.DriverTags

/-- The actual flushed sender with its finite whole handshake worker. -/
def send (pid : PeerId) : WG.M Unit :=
  Flush.sendWith (fun {_} a => a) HandshakeFinite.sendWorker pid

theorem send_source (pid : PeerId) : WG.runFlushedSendWork pid = send pid := by
  rw [Flush.send_factor]
  have worker : WG.handshakeSendWorker = HandshakeFinite.sendWorker :=
    funext HandshakeFinite.sendWorker_source
  rw [worker]
  rfl

/-- The original finite 4096-turn workqueue factor, replacing only the sender.
The clear callback is already structural and performs no allocation or curve. -/
def drain (upTo : Option PeerId := none) : WG.M Unit :=
  Flush.drainWith (fun {_} a => a) send WG.runFlushedClearWork upTo

theorem drain_source (upTo : Option PeerId) :
    WG.drainHandshakeSendWq upTo = drain upTo := by
  rw [Flush.drain_factor]
  have sends : WG.runFlushedSendWork = send := funext send_source
  rw [sends]
  rfl

/-- Timer deletion uses its original bounded source; a selected clear-work
flush uses the finite drain at the same cut. -/
def timersStop (pid : PeerId) : WG.M Unit :=
  Flush.timersWith (fun {_} a => a) WG.delTimer (@drain) pid

theorem timersStop_source (pid : PeerId) : WG.timersStop pid = timersStop pid := by
  rw [Flush.timers_factor]
  have drains : WG.drainHandshakeSendWq = @drain := funext drain_source
  rw [drains]
  rfl

/-- The existing after-dead removal factor with both inline drain sites
replaced. Its queued-crypt refusal and final release remain original. -/
def afterDead (pid : PeerId) : WG.M Unit :=
  Removal.afterDeadWith (fun {_} a => a) WG.keypairsClear timersStop (@drain)
    (fun p => WG.peerPut (some p)) pid

theorem afterDead_source (pid : PeerId) :
    WG.peerRemoveAfterDead pid = afterDead pid := by
  rw [Removal.afterDead_factor]
  have timers : WG.timersStop = timersStop := funext timersStop_source
  have drains : WG.drainHandshakeSendWq = @drain := funext drain_source
  rw [timers, drains]
  rfl

def remove (peer : Option PeerId) : WG.M Unit :=
  Configuration.peerRemoveWith (fun {_} a => a) WG.peerMakeDead afterDead peer

theorem remove_source (peer : Option PeerId) : WG.peerRemove peer = remove peer := by
  rw [Configuration.peerRemove_factor]
  have afters : WG.peerRemoveAfterDead = afterDead := funext afterDead_source
  rw [afters]
  rfl

/-- Bulk removal uses the original structural/range-bounded allowed-IP free,
make-dead pass, and list traversal with finite after-dead callbacks. -/
def removeAll : WG.M Unit :=
  Configuration.peerRemoveAllWith (fun {_} a => a) WG.free WG.peerMakeDead afterDead

theorem removeAll_source : WG.peerRemoveAll = removeAll := by
  rw [Configuration.peerRemoveAll_factor]
  have afters : WG.peerRemoveAfterDead = afterDead := funext afterDead_source
  rw [afters]
  rfl

def destruct : WG.M Unit :=
  Configuration.destructWith (fun {_} a => a) removeAll Removal.destructFinishSource

theorem destruct_source : WG.wgDestruct = destruct := by
  rw [Configuration.wgDestruct_factor, removeAll_source]
  rfl

/-- Stop keeps the original per-peer operation order and queued-receive Stop;
only inline timer-stop drains need the finite sender substitution. -/
def stop : WG.M Unit :=
  Control.stopWith (fun {_} a => a)
    (Control.stopPeerWith (fun pid => requireNotPending pid "wg_stop while a handshake is queued")
      WG.purgeStagedPackets timersStop WG.handshakeClear WG.keypairsClear WG.resetLastSentHandshake)

theorem stop_source : WG.wgStop = stop := by
  rw [Control.stop_factor]
  have timers : WG.timersStop = timersStop := funext timersStop_source
  rw [timers]
  rfl

def down : WG.M Unit := Control.downWith (fun {_} a => a) stop

theorem down_source : WG.wgDown = down := by
  rw [Control.down_factor, stop_source]
  rfl

end Leanux.Proofs.WG.Progress.MaintenanceFinite
