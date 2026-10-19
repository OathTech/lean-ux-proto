import Leanux.Proofs.WG.Roaming.RemoteChronologyTrafficSource
import Leanux.Proofs.WG.Roaming.RemoteChronologyNativeSource
import Leanux.Proofs.WG.Roaming.RemoteDriverControlsSource
import Leanux.Proofs.WG.Roaming.RemoteDriverDispatchTrafficSource
import Leanux.Proofs.WG.Roaming.RemoteOuterRulesSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteChronology.Driver
open Leanux Leanux.WG Noise Lifetimes Queues Std.Do
open Leanux.Proofs.Framing Leanux.Proofs.Logged
open Leanux.Proofs.WG.Configuration

namespace Outer
theorem lift_store (entry : RemoteMap) {α : Type} (action : Leanux.M α)
    (frame : SameProductStore action) :
    PrefixPreserves (Inv entry) RemoteDriver.Safe (liftPrefix action) :=
  viewLiftPrefix_preserves productStoreView (safe entry) (store_inv entry) frame

theorem lift_fs (entry : RemoteMap) {α : Type} (action : FS.M α) :
    PrefixPreserves (Inv entry) RemoteDriver.Safe (liftPrefix (liftFS action)) :=
  viewLiftPrefix_preserves (fun w : World => wgStoreView w.wg) (safe entry) (wg_store_inv entry)
    (fun _ => productFS_spec action _ (fun _ _ _ _ prior => prior))

theorem lift_ambient (entry : RemoteMap) {α : Type} (action : AmbientM α) :
    PrefixPreserves (Inv entry) RemoteDriver.Safe (liftPrefix (liftAmbient action)) :=
  lift_store entry _ (fun _ => productAmbient_spec action _ (fun _ _ prior => prior))

theorem socket (entry : RemoteMap) (fd : Nat) (body : PrefixM RemoteDriver.Event Int)
    (hb : PrefixPreserves (Inv entry) RemoteDriver.Safe body) :
    PrefixPreserves (Inv entry) RemoteDriver.Safe
      (socketCallOnWith (fun {_} a => liftPrefix a) fd body) :=
  RemoteOuterRules.socket _ _ (safe entry) (fun {_} => lift_fs entry) fd body hb

theorem netlink (entry : RemoteMap) (body : PrefixM RemoteDriver.Event Int)
    (hb : PrefixPreserves (Inv entry) RemoteDriver.Safe body) :
    PrefixPreserves (Inv entry) RemoteDriver.Safe
      (netlinkRequestWith (fun {_} a => liftPrefix a) body) :=
  RemoteOuterRules.netlink _ _ (safe entry) (fun {_} => lift_fs entry)
    (fun {_} => lift_ambient entry) body hb

theorem set_preserves (entry : RemoteMap) (attrs : DeviceAttrs) :
    PrefixPreserves (Inv entry) RemoteDriver.Safe (RemoteDriver.Outer.set attrs) :=
  netlink entry _ ((configuration_preserves entry attrs).liftWGObserver)

theorem create_preserves (entry : RemoteMap) :
    PrefixPreserves (Inv entry) RemoteDriver.Safe RemoteDriver.Outer.create := by
  apply focus_audit entry _ _ (dispatchAudit_erases .wgCreate)
  intro before
  change Preserves (fun w : World => RemoteSilent.Retained before w.wg)
    (Leanux.rtnetlinkRequest (liftWG WG.wgCreate))
  exact RemoteDispatch.rtnetlink_retained before _
    (RemoteLifecycle.lift_native before _ (RemoteLifecycle.create_native before))

theorem delete_preserves (entry : RemoteMap) :
    PrefixPreserves (Inv entry) RemoteDriver.Safe RemoteDriver.Outer.delete := by
  apply focus_audit entry _ _ (dispatchAudit_erases .wgDelete)
  intro before
  change Preserves (fun w : World => RemoteSilent.Retained before w.wg)
    (Leanux.rtnetlinkRequest Env.wgDelete)
  exact RemoteDispatch.rtnetlink_retained before _ (RemoteLifecycle.envDelete_native before)

theorem xmit_preserves (entry : RemoteMap) (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts) :
    PrefixPreserves (Inv entry) RemoteDriver.Safe (RemoteDriver.Outer.xmit family addr payload opts) :=
  syscallXmitWith_preserves (safe entry) (wg_store_inv entry) _ _
    (Traffic.multicast_preserves entry) (Traffic.transmit_preserves entry) family addr payload opts

theorem inject_preserves (entry : RemoteMap) (family port : Nat) (msg : List UInt8)
    (tos : Nat) (ll : Bool) (dest : Nat) :
    PrefixPreserves (Inv entry) RemoteDriver.Safe (RemoteDriver.Outer.inject family port msg tos ll dest) :=
  socket entry _ _ (Traffic.inject_preserves entry family port msg tos ll dest)

theorem observe_preserves (entry : RemoteMap) :
    PrefixPreserves (Inv entry) RemoteDriver.Safe RemoteDriver.Outer.observe := by
  unfold RemoteDriver.Outer.observe
  apply (Deferred.idle_preserves entry).bind
  intro _
  apply (lift_store entry Environment.observeTail observeTail_sameKernel).bind
  rintro ⟨ret,observed⟩
  have same : SameProductStore (modifyAmbient fun w => {w with
      extraOut:=["datagrams","replies","stats"].map fun k => (k,observed.getObjValD k)}) := by
    apply (ProjectedAction.iff_run _ _ _).mpr
    intro w value v run
    cases run
    rfl
  exact (lift_store entry _ same).bind
    (fun _ => socket entry _ _ (PrefixPreserves.pure (safe entry) ret))
end Outer

end Leanux.Proofs.WG.Roaming.RemoteChronology.Driver
