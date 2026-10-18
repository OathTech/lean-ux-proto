import Leanux.Proofs.WG.Roaming.RemoteDriverOuterSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteDriver.Outer
open Leanux Leanux.WG Noise Queues Lifetimes Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Leanux.Proofs.WG.Configuration

def set (attrs : DeviceAttrs) : PrefixM Event Int :=
  netlinkRequestWith (fun {_} a=>liftPrefix a)
    (liftWGObserver (RemoteConfiguration.setDevice Event.rx rxEvent Event.birth Event.endpoint attrs))

theorem set_preserves (entry : RemoteMap) (attrs : DeviceAttrs) :
    PrefixPreserves (Inv entry) Safe (set attrs) :=
  netlink entry _ ((RemoteConfiguration.setDevice_covered entry attrs).liftWGObserver)

theorem set_projects (attrs : DeviceAttrs) :
    ProjectsPrefix rxEvent id (set attrs) (RxHistory.syscallDispatch (.wgSet attrs)) := by
  change ProjectsPrefix rxEvent id (set attrs)
    (RxHistory.audit (netlinkRequestAudit (auditFocus (liftWGObserver (wgSetDevicePrefix attrs)))))
  rw [netlinkRequestAudit_factor]
  unfold RxHistory.audit
  rw [← netlinkRequestWith_focus RxHistory.Event.audit RxHistory.auditEvent (fun _=>rfl)
    (auditFocus (liftWGObserver (wgSetDevicePrefix attrs))) (Appends.focus _ _ _)]
  apply netlinkRequestWith_projects rxEvent
  change ProjectsPrefix rxEvent id _ (RxHistory.mixed (liftWGObserver (wgSetDevicePrefix attrs)))
  rw [← RoutingJoint.nativeRx_product]
  exact (RemoteConfiguration.setDevice_projects Event.rx rxEvent Event.birth Event.endpoint
    (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) attrs).liftWGObserver _ _

theorem set_appends (attrs : DeviceAttrs) : Appends (set attrs) :=
  netlinkRequestWith_appends ((RemoteConfiguration.setDevice_appends Event.rx rxEvent
    Event.birth Event.endpoint attrs).liftWGObserver)

theorem set_erases (attrs : DeviceAttrs) : ErasesPrefix (set attrs) (Leanux.dispatch (.wgSet attrs)) :=
  projection_erases (set_projects attrs) (RxHistory.syscallDispatch_erases _)

def create : PrefixM Event Int := focus (RxHistory.syscallDispatch .wgCreate)
def delete : PrefixM Event Int := focus (RxHistory.syscallDispatch .wgDelete)

theorem create_preserves (entry : RemoteMap) : PrefixPreserves (Inv entry) Safe create := by
  apply focus_retained entry _ _ (RxHistory.syscallDispatch_appends _) (RxHistory.syscallDispatch_erases _)
  intro before
  change Preserves (fun w : World=>RemoteSilent.Retained before w.wg)
    (Leanux.rtnetlinkRequest (liftWG WG.wgCreate))
  exact RemoteDispatch.rtnetlink_retained before _
    (RemoteLifecycle.lift_native before _ (RemoteLifecycle.create_native before))

theorem delete_preserves (entry : RemoteMap) : PrefixPreserves (Inv entry) Safe delete := by
  apply focus_retained entry _ _ (RxHistory.syscallDispatch_appends _) (RxHistory.syscallDispatch_erases _)
  intro before
  change Preserves (fun w : World=>RemoteSilent.Retained before w.wg)
    (Leanux.rtnetlinkRequest Env.wgDelete)
  exact RemoteDispatch.rtnetlink_retained before _ (RemoteLifecycle.envDelete_native before)

theorem create_projects : ProjectsPrefix rxEvent id create (RxHistory.syscallDispatch .wgCreate) :=
  Scheduler.focus_projects _ (RxHistory.syscallDispatch_appends _)
theorem delete_projects : ProjectsPrefix rxEvent id delete (RxHistory.syscallDispatch .wgDelete) :=
  Scheduler.focus_projects _ (RxHistory.syscallDispatch_appends _)
theorem create_appends : Appends create := Appends.focus _ _ _
theorem delete_appends : Appends delete := Appends.focus _ _ _

end Leanux.Proofs.WG.Roaming.RemoteDriver.Outer
