import Leanux.Proofs.WG.Config.RequestOrderModel
import Leanux.Proofs.WG.Config.ClaimView

/-! Projected initial-to-port field continuity for arbitrary device attributes. -/
set_option autoImplicit false

namespace Leanux.Proofs.WG.Config.RequestOrder
open Leanux Leanux.WG

def markDevice (attrs : DeviceAttrs) (d : Device) : Device :=
  {d with fwmark := attrs.fwmark.getD d.fwmark}

def MarkInput (attrs : DeviceAttrs) (initial final : Campaign2.State) : Prop :=
  final.device.map withoutPeers = initial.device.map (fun d => withoutPeers (markDevice attrs d)) ∧
    (∀ d, initial.device = some d →
      ClaimView.clearedPeers d final.toCore (if attrs.fwmark.isSome then d.peerList else [])) ∧
    final.portBound = initial.portBound ∧ final.nlSock7 = initial.nlSock7 ∧
    final.fixtureNetDevices = initial.fixtureNetDevices

def PortInput (attrs : DeviceAttrs) (initial : Campaign2.State) (r : Receipt) : Prop :=
  MarkInput attrs (incrementState initial) r.before.wg

def InputHistory (attrs : DeviceAttrs) (initial : Campaign2.State) (h : List Receipt) : Prop :=
  ∀ r ∈ h, ∀ port, r.kind = .port port → PortInput attrs initial r

def Portless (h : List Receipt) : Prop :=
  ∀ r ∈ h, ∀ port, r.kind ≠ .port port

def PortSilent {α : Type} (L : Language α) : Prop :=
  ∀ h, L.prefixes h → Portless h

def prefixDevice (attrs : DeviceAttrs) (d : Device) : Device :=
  {d with fwmark := attrs.fwmark.getD d.fwmark,deviceUpdateGen := d.deviceUpdateGen + 1}

end Leanux.Proofs.WG.Config.RequestOrder
