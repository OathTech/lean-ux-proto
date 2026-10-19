import Leanux.Proofs.WG.Progress.ResponseFiniteSource
import Leanux.Proofs.WG.Progress.SendBufferFiniteSource
import Leanux.Proofs.WG.Noise.SessionEvaluationSource
import Leanux.Proofs.WG.Origins.HandshakeSources

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.HandshakeFinite
open Leanux Leanux.WG
open Leanux.Proofs.WG.Origins

/-- Only callbacks reached by the response sender are replaced. The shared
source factor retains every original branch and continuation. -/
def responseOps : HandshakeSources.Ops WG.M :=
  { HandshakeSources.original with
    session := Noise.SessionEvaluation.evaluate
    create := createResponse
    send := sendBuffer }

theorem responseOps_source : HandshakeSources.original = responseOps := by
  have createEq : WG.createResponse = createResponse := funext createResponse_source
  have sessionEq : WG.beginSession = Noise.SessionEvaluation.evaluate :=
    funext Noise.SessionEvaluation.evaluate_source
  have sendEq : WG.sendBufferToPeer = sendBuffer :=
    funext fun pid => funext (sendBuffer_source pid)
  unfold responseOps
  rw [← createEq, ← sessionEq, ← sendEq]
  rfl

/-- The complete response sender with finite creation, session allocation and
buffer allocation. Its actual MAC and timer calls remain finite native calls. -/
def sendResponse (pid : PeerId) : WG.M Unit :=
  HandshakeSources.responseWith responseOps pid

theorem sendResponse_source (pid : PeerId) :
    WG.sendHandshakeResponse pid = sendResponse pid := by
  rw [← HandshakeSources.response_original]
  unfold sendResponse
  rw [← responseOps_source]

end Leanux.Proofs.WG.Progress.HandshakeFinite
