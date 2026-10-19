import Leanux.Proofs.WG.HandshakeSecurity.PeerReferenceTimerActors
import Leanux.Proofs.WG.HandshakeSecurity.PeerReferenceSaved

/-! Actual timer callbacks preserve the positive-reference exchange carrier. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.PeerReference
variable {E : Type} [EntryFormat E]
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues TransmitSecurity

theorem expired_keepalive (pid : PeerId) :
    Observed (E := E) (Driver.expiredKeepaliveObserved EntrySource.hooks (E := E) pid) := by
  rw [Driver.expiredKeepalive_lift EntrySource.hooks (E := E) rfl]
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
      (fun p => {p with timerNeedAnotherKeepalive := false}) (fun _ => rfl))
    intro _
    apply lift
    exact discard_view_spec id Inv _ (mod_timer _ _ _ _)
  · exact pure ()

theorem persistent (pid : PeerId) : Observed (E := E) (Driver.persistentObserved EntrySource.hooks (E := E) pid) := by
  rw [Driver.persistent_lift EntrySource.hooks]
  apply StatePrefixEnsures.bind (lift _ (read_peer pid))
  intro p
  apply StatePrefixEnsures.bind (ambient _)
  intro active
  split
  · exact keepalive pid
  · exact pure ()

theorem timer (pid : PeerId) (t : PeerTimer) :
    Observed (E := E) (Driver.timerObserved EntrySource.hooks (E := E) pid t) := by
  cases t with
  | retransmitHandshake =>
    rw [Driver.timer_retransmit_lift EntrySource.hooks (E := E) rfl rfl rfl]
    exact lift _ (retransmit pid)
  | sendKeepalive => exact expired_keepalive pid
  | newHandshake =>
    rw [Driver.timer_new_lift EntrySource.hooks (E := E) rfl rfl]
    exact lift _ (new_handshake pid)
  | zeroKeyMaterial => exact lift _ (zero_material pid)
  | persistentKeepalive => exact persistent pid

end Leanux.Proofs.WG.HandshakeSecurity.PeerReference
