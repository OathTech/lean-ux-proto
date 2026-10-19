import Leanux.Proofs.WG.HandshakeSecurity.ExchangeJointProjection
import Leanux.Proofs.WG.TransmitSecurity.DriverProjectionBase

/-! Projection of existing authenticated handshake observations to their
native callback bodies. Dropping those event constructors is an exact history
frame, independent of the callback's native-result erasure. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ExchangeJoint
open Leanux Leanux.WG Leanux.Proofs.Logged Origins.HandshakeSources
open AuthenticatedEffects

theorem old_native (record : HandshakeCausal.Event → E)
    (decode : E → Option HandshakeCausal.Event) (rho : E → Option F)
    (quiet : ∀ event, rho (record event) = none) (body : WGPrefix HandshakeCausal.Event α)
    (native : WG.M α) (erases : ErasesStatePrefix body native) :
    StateProjectsPrefix rho id (HandshakeWorker.old record decode body) (liftWGPrefix native) :=
  Exchange.quiet_native_projection rho _ native (focusStatePrefix_erases record decode erases)
    (fun w a h => focusPrefix_other record decode rho quiet (body.run w) a h)

theorem callback_native (record : HandshakeCausal.Event → E) (rho : E → Option F)
    (quiet : ∀ event, rho (record event) = none) (kind : HandshakeCausal.Kind) (pid : PeerId)
    (body : WGPrefix E α) (target : WGPrefix F α) (projects : StateProjectsPrefix rho id body target) :
    StateProjectsPrefix rho id (HandshakeWorker.callback record kind pid body) target := by
  intro w a h
  have projected := projects w a (h ++ [record (.callback kind pid)])
  change runStatePrefix target w a (h.filterMap rho) =
    ((runStatePrefix (HandshakeWorker.callback record kind pid body) w a h).1.map (fun ((x,v),b) => ((x,v),b)),
      (runStatePrefix (HandshakeWorker.callback record kind pid body) w a h).2.filterMap rho)
  unfold HandshakeWorker.callback
  rw [runStatePrefix_bind,runStatePrefix_emit]
  simpa only [Prod.map,id,Prod.eta,runStatePrefix,List.filterMap_append,
    List.filterMap_cons,List.filterMap_nil,quiet,Option.toList_none,List.nil_append,List.append_nil] using projected

theorem observed_ops_native (record : HandshakeCausal.Event → E)
    (decode : E → Option HandshakeCausal.Event) (rho : E → Option F)
    (quiet : ∀ event, rho (record event) = none)
    (sg : PeerId → WGPrefix E Bool) (sa : PeerId → WGPrefix F Bool)
    (kg : PeerId → WGPrefix E Unit) (ka : PeerId → WGPrefix F Unit)
    (hs : ∀ pid, StateProjectsPrefix rho id (sg pid) (sa pid))
    (hk : ∀ pid, StateProjectsPrefix rho id (kg pid) (ka pid)) (mac : HandshakeMac) :
    HandshakeWorker.OpsProjects rho (HandshakeWorker.observedOps record decode sg kg mac)
      (HandshakeWorker.ops sa ka) where
  step := fun _ => TransmitSecurity.Driver.Projection.state_lift rho _
  session := fun pid => callback_native record rho quiet _ pid _ _ (hs pid)
  modifyPeer := fun _ _ => old_native record decode rho quiet _ _ (HandshakeCausal.call_erases _ _ _)
  create := fun _ => old_native record decode rho quiet _ _ (HandshakeCausal.call_erases _ _ _)
  mac := fun _ _ => old_native record decode rho quiet _ _ (HandshakeCausal.call_erases _ _ _)
  send := fun _ _ => old_native record decode rho quiet _ _ (HandshakeCausal.call_erases _ _ _)
  derived := fun _ => old_native record decode rho quiet _ _ (HandshakeCausal.call_erases _ _ _)
  traversal := fun _ => old_native record decode rho quiet _ _ (HandshakeCausal.call_erases _ _ _)
  sent := fun _ => old_native record decode rho quiet _ _ (HandshakeCausal.call_erases _ _ _)
  cookie := fun _ _ => TransmitSecurity.Driver.Projection.state_lift rho _
  initiation := fun _ => old_native record decode rho quiet _ _ (HandshakeCausal.initiation_erases _)
  response := fun _ => old_native record decode rho quiet _ _ (HandshakeCausal.response_erases _)
  endpoint := fun _ _ => old_native record decode rho quiet _ _ (HandshakeCausal.call_erases _ _ _)
  complete := fun _ => old_native record decode rho quiet _ _ (HandshakeCausal.call_erases _ _ _)
  keepalive := fun pid => callback_native record rho quiet _ pid _ _ (hk pid)
  received := fun _ => old_native record decode rho quiet _ _ (HandshakeCausal.call_erases _ _ _)
  put := fun _ => TransmitSecurity.Driver.Projection.state_lift rho _
  cookieConsume := fun _ => TransmitSecurity.Driver.Projection.state_lift rho _

end Leanux.Proofs.WG.HandshakeSecurity.ExchangeJoint
