import Leanux.WG.PeerRemove

/-! Native factors separated from observer and frame dependencies. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG

/-- The actual dequeue, pending guard and flag update are one source cut.
Keeping the peer read with its write permits projections of its other fields. -/
def flushedSendPrepare (pid : PeerId) : WG.M Unit := do
  modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue.erase pid}
  let p ← getPeer pid
  if !p.handshakePending then invariant "queued work without a pending flag"
  setPeer pid {p with handshakePending := (← getDev).sendWorkQueue.contains pid}

theorem runFlushedSendWork_factor (pid : PeerId) : runFlushedSendWork pid = (do
    flushedSendPrepare pid
    let _ ← hidden (.sectionStart .sendWorker)
    handshakeSendWorker pid
    let _ ← hidden (.sectionStop .sendWorker)
    pure ()) := by
  simp only [runFlushedSendWork,flushedSendPrepare,bind_assoc]
  congr 1
  funext u
  congr 1
  funext p
  split <;> simp only [bind_assoc]

end Leanux.Proofs.WG.Index
