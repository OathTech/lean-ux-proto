import Leanux.Proofs.WG.TransmitSecurity.DriverEffectsNeutral
import Leanux.Proofs.WG.HandshakeSecurity.TimestampArchiveTimerActors

/-! Timer callbacks retain the same committed timestamp history, including
keepalive staging and the peer read used by its subsequent flag write. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues TransmitSecurity

theorem expired_keepalive (pid : PeerId) :
    Preserves (Driver.expiredKeepaliveObserved TimestampDriver.hooks pid) := by
  rw [Driver.expiredKeepalive_lift TimestampDriver.hooks rfl]
  apply StatePrefixEnsures.bind (keepalive pid)
  intro _
  apply StatePrefixEnsures.bind (lift _ (read_peer pid))
  intro p
  apply StatePrefixEnsures.bind (ambient _)
  intro another
  split
  · apply StatePrefixEnsures.bind (Saved.read_saved pid)
    intro saved
    apply StatePrefixEnsures.bind (Saved.write_saved pid saved
      (fun p => {p with timerNeedAnotherKeepalive := false}) (fun _ => ⟨rfl,rfl⟩))
    intro _
    apply lift
    intro confirmed
    exact discard_view_spec id (StateInv confirmed) _ (mod_timer _ _ _ _ confirmed)
  · exact pure ()

theorem persistent (pid : PeerId) : Preserves (Driver.persistentObserved TimestampDriver.hooks pid) := by
  rw [Driver.persistent_lift TimestampDriver.hooks]
  apply StatePrefixEnsures.bind (lift _ (read_peer pid))
  intro p
  apply StatePrefixEnsures.bind (ambient _)
  intro active
  split
  · exact keepalive pid
  · exact pure ()

theorem timer (pid : PeerId) (t : PeerTimer) :
    Preserves (Driver.timerObserved TimestampDriver.hooks pid t) := by
  cases t with
  | retransmitHandshake =>
    rw [Driver.timer_retransmit_lift TimestampDriver.hooks rfl]
    exact lift _ (retransmit pid)
  | sendKeepalive => exact expired_keepalive pid
  | newHandshake =>
    rw [Driver.timer_new_lift TimestampDriver.hooks rfl]
    exact lift _ (new_handshake pid)
  | zeroKeyMaterial => exact lift _ (zero_material pid)
  | persistentKeepalive => exact persistent pid

end Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
