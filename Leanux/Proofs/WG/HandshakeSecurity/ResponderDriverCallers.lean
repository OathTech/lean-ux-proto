import Leanux.Proofs.WG.HandshakeSecurity.ResponderDriverSaved

namespace Leanux.Proofs.WG.HandshakeSecurity.Responder.DriverCuts
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues TransmitSecurity

/-- Keepalive staging is reached with the same native carrier even when its
saved peer is written only after allocation and MTU reads. -/
theorem keepalive (pid : PeerId) : Preserves (Driver.keepaliveObserved hooks pid) := by
  rw [Driver.keepalive_native _ rfl]
  unfold Driver.keepaliveInline
  apply StatePrefixEnsures.bind (read_saved pid)
  intro p
  apply StatePrefixEnsures.bind (saved_ambient pid p _)
  intro empty
  split
  · apply StatePrefixEnsures.bind (saved_ambient pid p _)
    intro allocated
    apply StatePrefixEnsures.bind (saved_ambient pid p _)
    intro failed
    split
    · exact forget_saved pid p (pure ())
    · apply StatePrefixEnsures.bind (saved_store pid p getDev getDev_sameWGStore)
      intro d
      apply StatePrefixEnsures.bind (write_saved pid p
        (fun p => {p with staged := p.staged ++ [{mtu := d.mtu}]}) (fun _ => rfl) (fun _ => rfl))
      intro _
      exact staging pid
  · exact forget_saved pid p (staging pid)

end Leanux.Proofs.WG.HandshakeSecurity.Responder.DriverCuts
