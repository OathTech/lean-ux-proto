import Leanux.Proofs.WG.Config.RequestKeyHeaderModel

/-! Projected normal final-header fields and actual port-selection semantics. Identity effects are handled separately from the unchanged scalar header. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.RequestOrder.FinalHeader
open Leanux Leanux.WG

abbrev Header := String × Nat × Nat × Nat × Nat

def header (d : Device) : Header :=
  (d.ifname,d.ifindex,d.incomingPort,d.fwmark,d.deviceUpdateGen)

def Fields (attrs : DeviceAttrs) (before after : Device) : Prop :=
  after.ifname=before.ifname ∧ after.ifindex=before.ifindex ∧
  after.fwmark=attrs.fwmark.getD before.fwmark ∧
  after.deviceUpdateGen=before.deviceUpdateGen+1

def PortSelected (attrs : DeviceAttrs) (before : Device) (actual : Nat) : Prop :=
  match attrs.listenPort with
  | none => actual=before.incomingPort
  | some port => if port=0 then ZeroPortRequestChoice before actual else actual=port

end Leanux.Proofs.WG.Config.RequestOrder.FinalHeader
