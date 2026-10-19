import Leanux.Proofs.WG.TimerDiscipline.HandshakeMaintenanceRemovalSource
import Leanux.Proofs.WG.Noise.DriverTagControlSource
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.HandshakeMaintenance
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes
open HandshakeJournal

def stopPeer (pid : PeerId) : Obs Unit :=
  Noise.DriverTags.Control.stopPeerWith
    (fun p => liftWGPrefix (requireNotPending p "wg_stop while a handshake is queued"))
    (fun p => liftWGPrefix (purgeStagedPackets p)) timersStop
    (fun p => liftWGPrefix (handshakeClear p))
    (fun p => liftWGPrefix (keypairsClear p))
    (fun p => liftWGPrefix (resetLastSentHandshake p)) pid
def stop : Obs Unit :=
  Noise.DriverTags.Control.stopWith (fun {_} a => liftWGPrefix a) stopPeer
def down : Obs Unit :=
  Noise.DriverTags.Control.downWith (fun {_} a => liftWGPrefix a) stop

theorem stopPeer_erases (pid : PeerId) :
    ErasesStatePrefix (stopPeer pid)
      (Noise.DriverTags.Control.stopPeerWith
        (fun p => requireNotPending p "wg_stop while a handshake is queued")
        purgeStagedPackets WG.timersStop handshakeClear keypairsClear resetLastSentHandshake pid) :=
  Noise.DriverTags.Control.stopPeerWith_erases _ _ _ _ _ _ _ _ _ _ _ _
    (fun _ => erasesStatePrefix_lift _) (fun _ => erasesStatePrefix_lift _)
    timersStop_erases (fun _ => erasesStatePrefix_lift _)
    (fun _ => erasesStatePrefix_lift _) (fun _ => erasesStatePrefix_lift _) pid
theorem stop_erases : ErasesStatePrefix stop WG.wgStop := by
  rw [Noise.DriverTags.Control.stop_factor]
  exact Noise.DriverTags.Control.stopWith_erases _ _ stopPeer_erases
theorem down_erases : ErasesStatePrefix down WG.wgDown := by
  rw [Noise.DriverTags.Control.down_factor]
  exact Noise.DriverTags.Control.downWith_erases _ _ stop_erases

theorem stopPeer_preserves (S : List Event → Prop)
    (hs : ∀ pid, StatePrefixPreserves (fun h _ _ => S h) S (sendWorker pid)) (pid : PeerId) :
    StatePrefixPreserves (fun h _ _ => S h) S (stopPeer pid) :=
  Noise.DriverTags.Control.stopPeerWith_preserves (fun h _ _ => S h) S
    _ _ _ _ _ _ (fun _ => quiet_preserves S _) (fun _ => quiet_preserves S _)
    (timersStop_preserves S hs) (fun _ => quiet_preserves S _)
    (fun _ => quiet_preserves S _) (fun _ => quiet_preserves S _) pid
theorem stop_preserves (S : List Event → Prop)
    (hs : ∀ pid, StatePrefixPreserves (fun h _ _ => S h) S (sendWorker pid)) :
    StatePrefixPreserves (fun h _ _ => S h) S stop :=
  Noise.DriverTags.Control.stopWith_preserves (fun h _ _ => S h) S (fun _ _ _ h => h)
    stopPeer (stopPeer_preserves S hs) (quiet_preserves S _)
    (fun _ => quiet_preserves S _) (quiet_preserves S _) (quiet_preserves S _)
    (quiet_preserves S _) (quiet_preserves S _)
theorem down_preserves (S : List Event → Prop)
    (hs : ∀ pid, StatePrefixPreserves (fun h _ _ => S h) S (sendWorker pid)) :
    StatePrefixPreserves (fun h _ _ => S h) S down :=
  Noise.DriverTags.Control.downWith_preserves (fun h _ _ => S h) S
    stop (stop_preserves S hs) (quiet_preserves S _)

theorem stopPeer_valid (pid : PeerId) :
    StatePrefixPreserves (fun h _ _ => ValidHistory h) ValidHistory (stopPeer pid) :=
  stopPeer_preserves ValidHistory sendWorker_valid pid

theorem stopPeer_paired (pid : PeerId) :
    StatePrefixPreserves (fun h _ _ => Paired h) Paired (stopPeer pid) :=
  stopPeer_preserves Paired sendWorker_paired pid

theorem stopPeer_appends (pid : PeerId) : StateAppends (stopPeer pid) :=
  true_appends _ (stopPeer_preserves (fun _ => True)
    (fun p => appends_true _ (sendWorker_appends p)) pid)

theorem stop_valid :
    StatePrefixPreserves (fun h _ _ => ValidHistory h) ValidHistory stop :=
  stop_preserves ValidHistory sendWorker_valid 

theorem stop_paired :
    StatePrefixPreserves (fun h _ _ => Paired h) Paired stop :=
  stop_preserves Paired sendWorker_paired 

theorem stop_appends : StateAppends stop :=
  true_appends _ (stop_preserves (fun _ => True)
    (fun p => appends_true _ (sendWorker_appends p)) )

theorem down_valid :
    StatePrefixPreserves (fun h _ _ => ValidHistory h) ValidHistory down :=
  down_preserves ValidHistory sendWorker_valid 

theorem down_paired :
    StatePrefixPreserves (fun h _ _ => Paired h) Paired down :=
  down_preserves Paired sendWorker_paired 

theorem down_appends : StateAppends down :=
  true_appends _ (down_preserves (fun _ => True)
    (fun p => appends_true _ (sendWorker_appends p)) )
end Leanux.Proofs.WG.TimerDiscipline.HandshakeMaintenance
