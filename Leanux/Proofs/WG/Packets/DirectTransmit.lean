import Leanux.Proofs.WG.Lifetimes.TxCallFocus
import Leanux.Proofs.WG.Packets.NativeTransmitPreservation
import Leanux.Proofs.WG.Packets.TransmitStack
import Leanux.Proofs.WG.Packets.OldProduct

/-! The actual direct transmit syscall uses its original socket/route source,
with only the native completed-handoff observation added. -/
namespace Leanux.Proofs.WG.TransmitJoint
open Leanux Leanux.WG Leanux.Proofs.Logged
open Lifetimes Queues AllowedIps

def multicast (family addr : Nat) : PrefixM Event Unit :=
  oldProduct (RoutingJoint.rxAction (RxHistory.audit (xmitMulticastLoopAudit family addr)))

def direct (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts) : PrefixM Event Int :=
  syscallXmitWith multicast (fun family addr packets mtu => liftWGObserver (transmit family addr packets mtu))
    family addr payload opts

private theorem direct_old_factor (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts) :
    syscallXmitWith
      (fun family addr => RoutingJoint.rxAction (RxHistory.audit (xmitMulticastLoopAudit family addr)))
      (fun family addr packets mtu => liftWGObserver (RoutingJoint.access (wgXmitPrefix family addr packets mtu)))
      family addr payload opts = RoutingJoint.dispatch (.wgXmit family addr payload opts) := by
  change syscallXmitWith
    (fun family addr => focusPrefix RoutingJoint.Event.rx RoutingJoint.rxEvent (RxHistory.audit (xmitMulticastLoopAudit family addr)))
    (fun family addr packets mtu => focusPrefix RoutingJoint.Event.rx RoutingJoint.rxEvent
      (RxHistory.audit (auditFocus (liftWGObserver (wgXmitPrefix family addr packets mtu)))))
    family addr payload opts = _
  rw [syscallXmitWith_focus RoutingJoint.Event.rx RoutingJoint.rxEvent (fun _ => rfl)
    (fun family addr => RxHistory.audit (xmitMulticastLoopAudit family addr))
    (fun family addr packets mtu => RxHistory.audit (auditFocus (liftWGObserver (wgXmitPrefix family addr packets mtu))))
    (fun _ _ => Appends.focus _ _ _) (fun _ _ _ _ => Appends.focus _ _ _)
    family addr payload opts]
  congr 1
  change syscallXmitWith
    (fun family addr => focusPrefix RxHistory.Event.audit RxHistory.auditEvent (xmitMulticastLoopAudit family addr))
    (fun family addr packets mtu => focusPrefix RxHistory.Event.audit RxHistory.auditEvent
      (auditFocus (liftWGObserver (wgXmitPrefix family addr packets mtu))))
    family addr payload opts = _
  exact syscallXmitWith_focus RxHistory.Event.audit RxHistory.auditEvent (fun _ => rfl)
    _ _ xmitMulticastLoopAudit_appends (fun _ _ _ _ => Appends.focus _ _ _) family addr payload opts

/-- Exact old journal, product state, result and Stop at the direct call. -/
theorem direct_projects (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts) :
    ProjectsPrefix oldEvent id (direct family addr payload opts)
      (RoutingJoint.dispatch (.wgXmit family addr payload opts)) := by
  rw [← direct_old_factor]
  exact syscallXmitWith_projects oldEvent _ _ _ _
    (fun family addr => oldProduct_projects _ (Appends.focus _ _ _))
    (fun family addr packets mtu => (transmit_projects family addr packets mtu).liftWGObserver _ _)
    family addr payload opts

theorem direct_appends (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts) :
    Appends (direct family addr payload opts) :=
  syscallXmitWith_appends multicast _ (fun _ _ => oldProduct_appends _)
    (fun family addr packets mtu => (transmit_appends family addr packets mtu).liftWGObserver)
    family addr payload opts

/-- The multicast path retains the old audit, including loopback accesses. -/
theorem multicast_preserves (initial : FlatTable × FlatTable) (family addr : Nat) :
    PrefixPreserves (Inv initial) (Safe initial) (multicast family addr) :=
  oldProduct_projected initial _ _ (Appends.focus _ _ _)
    (RoutingJoint.rxAction_routing (RxHistory.audit_erases (xmitMulticastLoopAudit_erases family addr)))
    (global_completion_same World.wg initial _ (xmitMulticastLoop_routing family addr))

/-- The actual direct syscall transports each strict-prefix handoff check.
All source route/descriptor/multicast behavior remains inside this contract. -/
theorem direct_preserves (initial : FlatTable × FlatTable)
    (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts) :
    PrefixPreserves (Inv initial) (Safe initial) (direct family addr payload opts) :=
  syscallXmitWith_preserves (fun _ _ hi => hi.safe) Inv.store multicast _
    (multicast_preserves initial) (transmit_product initial) family addr payload opts

theorem direct_erases (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts) :
    ErasesPrefix (direct family addr payload opts) (Leanux.dispatch (.wgXmit family addr payload opts)) := by
  intro w h
  have projected := congrArg Prod.fst (direct_projects family addr payload opts w h)
  have original := RoutingJoint.dispatch_erases (.wgXmit family addr payload opts) w (h.filterMap oldEvent)
  have same := projected.symm.trans original
  change (runPrefix (direct family addr payload opts) w h).1.map (fun (x,v) => (x,v)) = _ at same
  cases hr : (runPrefix (direct family addr payload opts) w h).1 <;> simpa only [hr,Except.map] using same

end Leanux.Proofs.WG.TransmitJoint
