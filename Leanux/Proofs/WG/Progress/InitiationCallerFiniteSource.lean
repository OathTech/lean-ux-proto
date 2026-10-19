import Leanux.Proofs.WG.Progress.InitiationFiniteSource
import Leanux.Proofs.WG.Progress.SendBufferFiniteSource
import Leanux.Proofs.WG.TimerDiscipline.InitiationTraversalSource

set_option autoImplicit false

namespace Leanux.Proofs.WG.Progress.HandshakeFinite
open Leanux Leanux.WG
open Leanux.Proofs.WG.TimerDiscipline

/-- Original sender stages with the finite creator and allocation-aware buffer
sender. The timer, MAC, routing and repayment effects remain concrete. -/
def sendInitiation (pid : PeerId) : WG.M Unit :=
  initiationTraversalPreludeWith createInitiation pid >>=
    initiationTraversalSuffixWith (initiationTraversalFinishWith sendBuffer) pid

theorem sendInitiation_source (pid : PeerId) :
    WG.sendHandshakeInitiation pid = sendInitiation pid := by
  rw [← initiationTraversal_source]
  unfold sendInitiation initiationTraversalPrelude initiationTraversalSuffix
    initiationTraversalFinish
  have creatorSame : WG.createInitiation = createInitiation := funext createInitiation_source
  have bufferSame : WG.sendBufferToPeer = sendBuffer :=
    funext fun target => funext fun bytes => sendBuffer_source target bytes
  rw [creatorSame, bufferSame]

/-- The actual queued worker's sender followed by its original final peer put. -/
def sendWorker (pid : PeerId) : WG.M Unit := do
  sendInitiation pid
  peerPut (some pid)

theorem sendWorker_source (pid : PeerId) :
    WG.handshakeSendWorker pid = sendWorker pid := by
  unfold WG.handshakeSendWorker sendWorker
  rw [sendInitiation_source]

end Leanux.Proofs.WG.Progress.HandshakeFinite
