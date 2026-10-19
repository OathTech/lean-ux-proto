import Leanux.Proofs.WG.TimerDiscipline.HookConfigurationSource
import Leanux.Proofs.WG.TimerDiscipline.HandshakeMaintenanceEnvironmentSource
import Leanux.Proofs.WG.TimerDiscipline.HookTrafficSource
import Leanux.Proofs.WG.Roaming.RemoteOuterRulesSource
/-! Concrete configuration callbacks and original socket/netlink wrappers.
The only receipt-producing configuration subpaths are actual inline drains. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.HookCommon
open Leanux Leanux.WG Leanux.Proofs.Logged HandshakeJournal Lifetimes Configuration
def peerCommand (attrs : PeerAttrs) : WGPrefix Event Int :=
  HookConfiguration.command HandshakeMaintenance.remove attrs
def deviceCommand (attrs : DeviceAttrs) : WGPrefix Event Int :=
  HookConfiguration.device HandshakeMaintenance.remove HandshakeMaintenance.removeAll attrs

theorem peerCommand_erases (attrs : PeerAttrs) :
    ErasesStatePrefix (peerCommand attrs) (setPeerCmd attrs) :=
  HookConfiguration.command_erases _ HandshakeMaintenance.remove_erases attrs
theorem deviceCommand_erases (attrs : DeviceAttrs) :
    ErasesStatePrefix (deviceCommand attrs) (wgSetDevice attrs) :=
  HookConfiguration.device_erases _ _ HandshakeMaintenance.remove_erases HandshakeMaintenance.removeAll_erases attrs
theorem peerCommand_valid (attrs : PeerAttrs) :
    StatePrefixPreserves (fun h _ _=>ValidHistory h) ValidHistory (peerCommand attrs) :=
  HookConfiguration.command_preserves ValidHistory _ HandshakeMaintenance.remove_valid attrs
theorem peerCommand_paired (attrs : PeerAttrs) :
    StatePrefixPreserves (fun h _ _=>Paired h) Paired (peerCommand attrs) :=
  HookConfiguration.command_preserves Paired _ HandshakeMaintenance.remove_paired attrs
theorem deviceCommand_valid (attrs : DeviceAttrs) :
    StatePrefixPreserves (fun h _ _=>ValidHistory h) ValidHistory (deviceCommand attrs) :=
  HookConfiguration.device_preserves ValidHistory _ _ HandshakeMaintenance.remove_valid HandshakeMaintenance.removeAll_valid attrs
theorem deviceCommand_paired (attrs : DeviceAttrs) :
    StatePrefixPreserves (fun h _ _=>Paired h) Paired (deviceCommand attrs) :=
  HookConfiguration.device_preserves Paired _ _ HandshakeMaintenance.remove_paired HandshakeMaintenance.removeAll_paired attrs
theorem peerCommand_appends (attrs : PeerAttrs) : StateAppends (peerCommand attrs) :=
  HookConfiguration.command_appends _ HandshakeMaintenance.remove_appends attrs
theorem deviceCommand_appends (attrs : DeviceAttrs) : StateAppends (deviceCommand attrs) :=
  HookConfiguration.device_appends _ _ HandshakeMaintenance.remove_appends HandshakeMaintenance.removeAll_appends attrs

theorem quiet_preserves {E α : Type} (S : List E → Prop) (a : Leanux.M α) :
    PrefixPreserves (fun h _=>S h) S (liftPrefix a) :=
  PrefixEnsures.preserves (PrefixEnsures.lift _ (fun _ _ h=>h) (fun _ _ _ _ h _=>h))

theorem rtnetlink_erases {E : Type} (body : PrefixM E Int) (a : Leanux.M Int)
    (hb : ErasesPrefix body a) :
    ErasesPrefix (rtnetlinkRequestWith (fun {_} a=>liftPrefix a) body) (Leanux.rtnetlinkRequest a) := by
  rw [rtnetlinkRequest_factor]
  unfold rtnetlinkRequestWith socketCallOnWith
  repeat' first
    | with_reducible exact hb
    | exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | (maintenance_intro; try dsimp only)
    | split

theorem rtnetlink_preserves {E : Type} (S : List E → Prop) (body : PrefixM E Int)
    (hb : PrefixPreserves (fun h _=>S h) S body) :
    PrefixPreserves (fun h _=>S h) S
      (rtnetlinkRequestWith (fun {_} a=>liftPrefix a) body) := by
  unfold rtnetlinkRequestWith socketCallOnWith
  repeat' first
    | with_reducible exact hb
    | with_reducible exact quiet_preserves S _
    | with_reducible exact PrefixPreserves.pure (I:=fun h _=>S h) (S:=S) (fun _ _ h=>h) _
    | (poll_preserve_head Bind.bind; apply PrefixPreserves.bind)
    | maintenance_intro
    | rx_phase_reduce
    | split

end Leanux.Proofs.WG.TimerDiscipline.HookCommon
