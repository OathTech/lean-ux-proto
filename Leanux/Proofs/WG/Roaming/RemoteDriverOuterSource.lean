import Leanux.Proofs.WG.Roaming.RemoteOuterRulesSource
import Leanux.Proofs.WG.Roaming.RemoteDriverTrafficSource
import Leanux.Proofs.WG.Roaming.RemoteConfigurationDevicePreservationSource
import Leanux.Proofs.WG.Roaming.RemoteLifecycleSource
import Leanux.Proofs.WG.Lifetimes.TxCallFocus
import Leanux.Proofs.WG.Roaming.RemoteDispatchSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteDriver.Outer
open Leanux Leanux.WG Noise Queues Lifetimes Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Leanux.Proofs.WG.Configuration

theorem lift_store (entry : RemoteMap) {α : Type} (action : Leanux.M α)
    (frame : SameProductStore action) : PrefixPreserves (Inv entry) Safe (liftPrefix action) :=
  viewLiftPrefix_preserves productStoreView (safe entry) (store_inv entry) frame

theorem lift_fs (entry : RemoteMap) {α : Type} (action : FS.M α) :
    PrefixPreserves (Inv entry) Safe (liftPrefix (liftFS action)) :=
  viewLiftPrefix_preserves (fun w : World=>wgStoreView w.wg) (safe entry) (wg_store_inv entry)
    (fun _=>productFS_spec action _ (fun _ _ _ _ pre=>pre))

theorem lift_ambient (entry : RemoteMap) {α : Type} (action : AmbientM α) :
    PrefixPreserves (Inv entry) Safe (liftPrefix (liftAmbient action)) :=
  lift_store entry _ (fun _=>productAmbient_spec action _ (fun _ _ pre=>pre))

theorem socket (entry : RemoteMap) (fd : Nat) (body : PrefixM Event Int)
    (hb : PrefixPreserves (Inv entry) Safe body) :
    PrefixPreserves (Inv entry) Safe (socketCallOnWith (fun {_} a=>liftPrefix a) fd body) :=
  RemoteOuterRules.socket _ _ (safe entry) (fun {_} => lift_fs entry) fd body hb

theorem netlink (entry : RemoteMap) (body : PrefixM Event Int)
    (hb : PrefixPreserves (Inv entry) Safe body) :
    PrefixPreserves (Inv entry) Safe (netlinkRequestWith (fun {_} a=>liftPrefix a) body) :=
  RemoteOuterRules.netlink _ _ (safe entry) (fun {_} => lift_fs entry)
    (fun {_} => lift_ambient entry) body hb

end Leanux.Proofs.WG.Roaming.RemoteDriver.Outer
