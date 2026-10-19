import Leanux.Proofs.WG.Progress.ResponseSenderFiniteSource
import Leanux.Proofs.WG.Progress.ConsumerFiniteSource
import Leanux.Proofs.WG.Progress.KeepaliveFiniteSource
import Leanux.Proofs.WG.Progress.CookieFiniteClaims

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.HandshakeFinite
open Leanux Leanux.WG Leanux.Proofs.WG.Origins

/-- The shared reception factor with its validation call exposed. This short
factor retains the original early cookie branch, load read and dispatch. -/
def receptionWithValidation (o : HandshakeSources.Ops WG.M)
    (validate : List UInt8 → SkbSource → Bool → WG.M MacState)
    (msg : List UInt8) (src : SkbSource) : WG.M Unit := do
  if ← o.step (branch .hsCookie (messageType msg == MESSAGE_HANDSHAKE_COOKIE)) then
    o.cookieConsume msg
    return
  let loaded ← o.step Cookies.loadPhase
  let mac ← o.step (validate msg src loaded)
  HandshakeSources.afterMacWith o msg src loaded mac

theorem receptionWithValidation_source (o : HandshakeSources.Ops WG.M)
    (msg : List UInt8) (src : SkbSource) :
    receptionWithValidation o WG.cookieValidatePacket msg src =
      HandshakeSources.receptionWith o msg src := rfl

/-- All callbacks reached by the shared handshake dispatch use their finite
counterparts where a nonstructural curve/allocation primitive was present. -/
def receptionOps : HandshakeSources.Ops WG.M :=
  { responseOps with
    cookie := sendCookie
    initiation := ConsumerFinite.initiation
    response := ConsumerFinite.response
    keepalive := keepalive }

theorem receptionOps_source : HandshakeSources.original = receptionOps := by
  have cookieEq : WG.sendHandshakeCookie = sendCookie :=
    funext fun msg => funext (sendCookie_source msg)
  have initiationEq : WG.consumeInitiation = ConsumerFinite.initiation :=
    funext ConsumerFinite.initiation_source
  have responseEq : WG.consumeResponse = ConsumerFinite.response :=
    funext ConsumerFinite.response_source
  have keepaliveEq : WG.sendKeepalive = keepalive := funext keepalive_source
  unfold receptionOps
  rw [← responseOps_source, ← cookieEq, ← initiationEq, ← responseEq, ← keepaliveEq]
  rfl

/-- The complete original handshake reception with finite validation and
dispatch callbacks, including early cookie consumption and all Stops. -/
def reception (msg : List UInt8) (src : SkbSource) : WG.M Unit :=
  receptionWithValidation receptionOps validateCookie msg src

theorem reception_source (msg : List UInt8) (src : SkbSource) :
    WG.receiveHandshakePacket msg src = reception msg src := by
  have validateEq : WG.cookieValidatePacket = validateCookie :=
    funext fun message => funext fun source => funext (validateCookie_source message source)
  unfold reception
  rw [← receptionOps_source, ← validateEq, receptionWithValidation_source]
  exact (HandshakeSources.reception_original msg src).symm

/-- The exact native queue-consume step, exposing only its reception call. -/
def stepWithReception (receive : List UInt8 → SkbSource → WG.M Unit) : WG.M Bool := do
  match (← getDev).handshakeQueue.consume with
  | (none, _) =>
    _ ← branch .workerConsumed false
    return false
  | (some (msg, src), ring) =>
    _ ← branch .workerConsumed true
    modifyDev fun d => {d with handshakeQueue := ring}
    receive msg src
    modifyDev fun d => {d with handshakeQueueLen := d.handshakeQueueLen - 1}
    return true

theorem stepWithReception_source :
    stepWithReception WG.receiveHandshakePacket = WG.receiveStep := rfl

/-- Complete queue step using the finite reception, with the same ring update
and final queue-length payment. It does not assert that the queue drains. -/
def receiveStep : WG.M Bool := stepWithReception reception

theorem receiveStep_source : WG.receiveStep = receiveStep := by
  have receiveEq : WG.receiveHandshakePacket = reception :=
    funext fun msg => funext (reception_source msg)
  unfold receiveStep
  rw [← receiveEq, stepWithReception_source]

end Leanux.Proofs.WG.Progress.HandshakeFinite
