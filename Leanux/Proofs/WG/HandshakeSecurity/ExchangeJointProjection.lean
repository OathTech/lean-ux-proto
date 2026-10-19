import Leanux.Proofs.WG.HandshakeSecurity.ExchangeJointSource
import Leanux.Proofs.WG.HandshakeSecurity.ExchangeDecoration
import Leanux.Proofs.WG.HandshakeSecurity.SendExchangeProjection

/-! Exact projections for decorated callbacks. These compare the same source
execution and preserve both result and ordered journal through Stops. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ExchangeJoint
open Leanux Leanux.WG Leanux.Proofs.Logged Origins.HandshakeSources
open AuthenticatedEffects

theorem receive_projects (rho : E → Option F)
    (record : Exchange.Event → E) (targetRecord : Exchange.Event → F)
    (matching : ∀ event, rho (record event) = some (targetRecord event))
    (g : Ops (WGPrefix E)) (t : Ops (WGPrefix F))
    (base : HandshakeWorker.OpsProjects rho g t) :
    HandshakeWorker.OpsProjects rho (receiveOps record g) (receiveOps targetRecord t) :=
  {base with
    create := fun pid => Exchange.receipt_projects rho _ _ _ _ (base.create pid) (fun _ => matching _)
    initiation := fun msg => Exchange.receipt_projects rho _ _ _ _ (base.initiation msg) (fun _ => matching _)
    response := fun msg => Exchange.receipt_projects rho _ _ _ _ (base.response msg) (fun _ => matching _)}

theorem receive_ignored (rho : E → Option F) (record : Exchange.Event → E)
    (quiet : ∀ event, rho (record event) = none)
    (g : Ops (WGPrefix E)) (t : Ops (WGPrefix F))
    (base : HandshakeWorker.OpsProjects rho g t) :
    HandshakeWorker.OpsProjects rho (receiveOps record g) t :=
  {base with
    create := fun pid => Exchange.receipt_ignored rho _ _ _ (base.create pid) (fun _ => quiet _)
    initiation := fun msg => Exchange.receipt_ignored rho _ _ _ (base.initiation msg) (fun _ => quiet _)
    response := fun msg => Exchange.receipt_ignored rho _ _ _ (base.response msg) (fun _ => quiet _)}

theorem receive_native (rho : E → Option Exchange.Event) (record : Exchange.Event → E)
    (matching : ∀ event, rho (record event) = some event)
    (g : Ops (WGPrefix E)) (session : PeerId → WGPrefix Exchange.Event Bool)
    (keepalive : PeerId → WGPrefix Exchange.Event Unit)
    (base : HandshakeWorker.OpsProjects rho g (HandshakeWorker.ops session keepalive)) :
    HandshakeWorker.OpsProjects rho (receiveOps record g) (ExchangeDriver.receiveOps session keepalive) :=
  receive_projects rho record id matching g _ base

theorem send_projects (rho : E → Option F)
    (record : Exchange.Event → E) (targetRecord : Exchange.Event → F)
    (matching : ∀ event, rho (record event) = some (targetRecord event))
    (g : SendExchange.Ops (WGPrefix E)) (t : SendExchange.Ops (WGPrefix F))
    (base : SendExchange.Ops.Projects rho g t) :
    SendExchange.Ops.Projects rho (sendOps record g) (sendOps targetRecord t) :=
  {base with create := fun pid =>
    Exchange.receipt_projects rho _ _ _ _ (base.create pid) (fun _ => matching _)}

theorem send_ignored (rho : E → Option F) (record : Exchange.Event → E)
    (quiet : ∀ event, rho (record event) = none)
    (g : SendExchange.Ops (WGPrefix E)) (t : SendExchange.Ops (WGPrefix F))
    (base : SendExchange.Ops.Projects rho g t) :
    SendExchange.Ops.Projects rho (sendOps record g) t :=
  {base with create := fun pid =>
    Exchange.receipt_ignored rho _ _ _ (base.create pid) (fun _ => quiet _)}

theorem flushed_exchange (rho : E → Option Exchange.Event) (record : Exchange.Event → E)
    (matching : ∀ event, rho (record event) = some event)
    (base : SendExchange.Ops (WGPrefix E))
    (native : SendExchange.Ops.Projects rho base nativeSendOps) (pid : PeerId) :
    StateProjectsPrefix rho id (flushed record base pid) (ExchangeDriver.flushed pid) := by
  apply SendExchange.flushed_projects rho liftWGPrefix liftWGPrefix
  · intro α action
    handshake_worker_project_step rho
  · intro target
    exact SendExchange.worker_projects rho (send_projects rho record id matching base _ native) target

theorem flushed_ignored (rho : E → Option F) (record : Exchange.Event → E)
    (quiet : ∀ event, rho (record event) = none)
    (g : SendExchange.Ops (WGPrefix E)) (t : SendExchange.Ops (WGPrefix F))
    (base : SendExchange.Ops.Projects rho g t) (pid : PeerId) :
    StateProjectsPrefix rho id (flushed record g pid)
      (SendExchange.flushedWith liftWGPrefix (SendExchange.workerWith t) pid) := by
  apply SendExchange.flushed_projects rho liftWGPrefix liftWGPrefix
  · intro α action
    handshake_worker_project_step rho
  · intro target
    exact SendExchange.worker_projects rho (send_ignored rho record quiet g t base) target

theorem session_projects (rho : E → Option F)
    (record : Exchange.Event → E) (targetRecord : Exchange.Event → F)
    (matching : ∀ event, rho (record event) = some (targetRecord event))
    (pid : PeerId) (g : WGPrefix E Bool) (t : WGPrefix F Bool)
    (base : StateProjectsPrefix rho id g t) :
    StateProjectsPrefix rho id (session record pid g) (session targetRecord pid t) :=
  Exchange.receipt_projects rho g t _ _ base (fun _ => matching _)

theorem session_ignored (rho : E → Option F) (record : Exchange.Event → E)
    (quiet : ∀ event, rho (record event) = none)
    (pid : PeerId) (g : WGPrefix E Bool) (t : WGPrefix F Bool)
    (base : StateProjectsPrefix rho id g t) :
    StateProjectsPrefix rho id (session record pid g) t :=
  Exchange.receipt_ignored rho g t _ base (fun _ => quiet _)

end Leanux.Proofs.WG.HandshakeSecurity.ExchangeJoint
