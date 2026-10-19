import Leanux.Proofs.WG.TransmitSecurity.DriverEffectsNeutral
import Leanux.Proofs.WG.HandshakeSecurity.ResponderDriverTimerFrames

/-! Timer callbacks retain the same committed responder history, including
keepalive staging and the peer read used by its subsequent flag write. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.Responder.DriverCuts
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues TransmitSecurity

theorem expired_keepalive (pid : PeerId) :
    Preserves (Driver.expiredKeepaliveObserved hooks pid) := by
  rw [Driver.expiredKeepalive_lift hooks rfl]
  apply StatePrefixEnsures.bind (keepalive pid)
  intro _
  apply StatePrefixEnsures.bind (lift _ (carrier_read_peer pid))
  intro p
  apply StatePrefixEnsures.bind (ambient _)
  intro another
  split
  · apply StatePrefixEnsures.bind (read_saved pid)
    intro saved
    apply StatePrefixEnsures.bind (write_saved pid saved
      (fun p => {p with timerNeedAnotherKeepalive := false}) (fun _ => rfl) (fun _ => rfl))
    intro _
    apply lift
    intro confirmed
    exact discard_view_spec id (Carrier confirmed) _ (carrier_modify_timer _ _ _ _ confirmed)
  · exact pure ()

theorem persistent (pid : PeerId) : Preserves (Driver.persistentObserved hooks pid) := by
  rw [Driver.persistent_lift hooks]
  apply StatePrefixEnsures.bind (lift _ (carrier_read_peer pid))
  intro p
  apply StatePrefixEnsures.bind (ambient _)
  intro active
  split
  · exact keepalive pid
  · exact pure ()

theorem timer (pid : PeerId) (t : PeerTimer) :
    Preserves (Driver.timerObserved hooks pid t) := by
  cases t with
  | retransmitHandshake =>
    rw [Driver.timer_retransmit_lift hooks rfl]
    exact lift _ (carrier_retransmit pid)
  | sendKeepalive => exact expired_keepalive pid
  | newHandshake =>
    rw [Driver.timer_new_lift hooks rfl]
    exact lift _ (carrier_new_handshake pid)
  | zeroKeyMaterial => exact lift _ (carrier_zero_material pid)
  | persistentKeepalive => exact persistent pid

end Leanux.Proofs.WG.HandshakeSecurity.Responder.DriverCuts
