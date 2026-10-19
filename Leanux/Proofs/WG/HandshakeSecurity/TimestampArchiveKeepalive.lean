import Leanux.Proofs.WG.HandshakeSecurity.TimestampArchiveSaved

namespace Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues TransmitSecurity

/-- Keepalive staging is reached with the same native carrier even when its
saved peer is written only after allocation and MTU reads. -/
theorem keepalive (pid : PeerId) : Preserves (Driver.keepaliveObserved TimestampDriver.hooks pid) := by
  unfold Driver.keepaliveObserved
  apply StatePrefixEnsures.bind (Saved.read_saved pid)
  intro p
  apply StatePrefixEnsures.bind (Saved.saved_ambient pid p _)
  intro empty
  split
  · apply StatePrefixEnsures.bind (Saved.saved_ambient pid p _)
    intro allocated
    apply StatePrefixEnsures.bind (Saved.saved_ambient pid p _)
    intro failed
    split
    · exact Saved.forget_saved pid p (pure ())
    · apply StatePrefixEnsures.bind (Saved.saved_store pid p getDev getDev_sameWGStore)
      intro d
      apply StatePrefixEnsures.bind (Saved.write_saved pid p
        (fun p => {p with staged := p.staged ++ [{mtu := d.mtu}]}) (fun _ => ⟨rfl,rfl⟩))
      intro _
      exact staging pid
  · exact Saved.forget_saved pid p (staging pid)

end Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
