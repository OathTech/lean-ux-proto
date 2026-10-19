import Leanux.Proofs.WG.AuthenticatedEffects.RawAppendCookie
import Leanux.Proofs.WG.AuthenticatedEffects.ProtocolSenderOther

/-! The native handshake receive and queued-send callbacks share the direct
append source. Session and keepalive callbacks remain supplied by the same
Driver execution; no independently erased execution is substituted for them. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.RawAppend
open Leanux Leanux.WG Leanux.Proofs.Logged Origins.HandshakeSources

def receiveOps (session : PeerId → WGPrefix Event Bool) (keepalive : PeerId → WGPrefix Event Unit) :
    Ops (WGPrefix Event) :=
  {HandshakeWorker.ops session keepalive with send := buffer, cookie := cookie}

private theorem callback_projects (record : HandshakeCausal.Event → E) (decode : E → Option Event)
    (quiet : ∀ event, decode (record event) = none) (kind : HandshakeCausal.Kind) (pid : PeerId)
    (body : WGPrefix E α) (target : WGPrefix Event α) (project : StateProjectsPrefix decode id body target) :
    StateProjectsPrefix decode id (HandshakeWorker.callback record kind pid body) target :=
  (pinned_const _private.Leanux.Proofs.WG.AuthenticatedEffects.HandshakeWorkerObserved.«0».Leanux.Proofs.WG.AuthenticatedEffects.HandshakeWorker.callback_projects)
    record decode quiet kind pid body target project

theorem receive_projects (decode : E → Option Event)
    (record : HandshakeCausal.Event → E) (old : E → Option HandshakeCausal.Event)
    (quiet : ∀ event, decode (record event) = none)
    (sg : PeerId → WGPrefix E Bool) (st : PeerId → WGPrefix Event Bool)
    (kg : PeerId → WGPrefix E Unit) (kt : PeerId → WGPrefix Event Unit)
    (hs : ∀ pid, StateProjectsPrefix decode id (sg pid) (st pid))
    (hk : ∀ pid, StateProjectsPrefix decode id (kg pid) (kt pid)) (mac : HandshakeMac)
    (socketRecord : ProtocolSocket.Receipt (CausalEffects.Context Cause) → E)
    (scope : E → Option (CausalScope.Event Cause)) (cookieRecord : CookieSocket.Receipt → E)
    (socketSelected : ∀ receipt, decode (socketRecord receipt) =
      ofSent receipt.run.before.sent receipt.run.after.sent)
    (cookieSelected : ∀ receipt, decode (cookieRecord receipt) = some (datagramEvent receipt.datagram)) :
    HandshakeWorker.OpsProjects decode
      (ProtocolSender.receiveOps record old sg kg mac socketRecord scope cookieRecord) (receiveOps st kt) :=
  {HandshakeEffects.observedOps_other record old decode quiet sg st kg kt hs hk mac with
    send := fun pid msg => callback_projects record decode quiet .send pid _ _
      (buffer_projects decode socketRecord socketSelected scope pid msg)
    cookie := fun msg src => cookie_projects decode cookieRecord cookieSelected mac msg src}

theorem receive_effects_projects (decode : E → Option Event)
    (record : HandshakeCausal.Event → E) (old : E → Option HandshakeCausal.Event)
    (quiet : ∀ event, decode (record event) = none)
    (effects : TimerEffects.Ops (WGPrefix E))
    (effectProject : TimerEffects.Ops.Projects decode effects TimerEffects.lifted)
    (sg : PeerId → WGPrefix E Bool) (st : PeerId → WGPrefix Event Bool)
    (kg : PeerId → WGPrefix E Unit) (kt : PeerId → WGPrefix Event Unit)
    (hs : ∀ pid, StateProjectsPrefix decode id (sg pid) (st pid))
    (hk : ∀ pid, StateProjectsPrefix decode id (kg pid) (kt pid)) (mac : HandshakeMac)
    (socketRecord : ProtocolSocket.Receipt (CausalEffects.Context Cause) → E)
    (scope : E → Option (CausalScope.Event Cause)) (cookieRecord : CookieSocket.Receipt → E)
    (socketSelected : ∀ receipt, decode (socketRecord receipt) =
      ofSent receipt.run.before.sent receipt.run.after.sent)
    (cookieSelected : ∀ receipt, decode (cookieRecord receipt) = some (datagramEvent receipt.datagram)) :
    HandshakeWorker.OpsProjects decode
      (HandshakeEffects.withEffects
        (ProtocolSender.receiveOps record old sg kg mac socketRecord scope cookieRecord) record effects)
      (receiveOps st kt) :=
  {HandshakeEffects.effects_other record old decode quiet effects effectProject sg st kg kt hs hk mac with
    send := fun pid msg => callback_projects record decode quiet .send pid _ _
      (buffer_projects decode socketRecord socketSelected scope pid msg)
    cookie := fun msg src => cookie_projects decode cookieRecord cookieSelected mac msg src}

def sendOps : HandshakeSecurity.SendExchange.Ops (WGPrefix Event) :=
  {SendEffects.native with send := buffer}

theorem send_projects (decode : E → Option Event)
    (record : ProtocolSocket.Receipt (CausalEffects.Context Cause) → E)
    (scope : E → Option (CausalScope.Event Cause))
    (selected : ∀ receipt, decode (record receipt) = ofSent receipt.run.before.sent receipt.run.after.sent) :
    HandshakeSecurity.SendExchange.Ops.Projects decode (ProtocolSender.sendOps record scope) sendOps :=
  {SendEffects.native_projects decode with send := buffer_projects decode record selected scope}

end Leanux.Proofs.WG.AuthenticatedEffects.RawAppend
