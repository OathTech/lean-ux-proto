import Leanux.Proofs.WG.Config.RequestInputModel
import Leanux.Proofs.WG.TimerDiscipline.SendView
import Leanux.Proofs.WG.Config.ZeroPortOutcomeModel

/-! Projected header continuity at completed key-stage receipts. Selected port values refer to actual successful port receipts from the same request; absent port attributes retain the entry value. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.RequestOrder.KeyHeader
open Leanux Leanux.WG TimerDiscipline

def fixed (d : Device) : SendConfiguration := sendConfiguration {d with incomingPort:=0}

def CoreInput (attrs : DeviceAttrs) (initial current : Campaign2.State) : Prop :=
  current.device.map fixed=initial.device.map (fun d=>fixed (prefixDevice attrs d))

def PortOrigin (attrs : DeviceAttrs) (initial : Campaign2.State) (h : List Receipt)
    (actual : Option Nat) : Prop :=
  match attrs.listenPort with
  | none => actual=initial.device.map Device.incomingPort
  | some port => ∃ r∈h,r.kind=.port port ∧ r.result=0 ∧
      actual=r.after.wg.device.map Device.incomingPort

def At (attrs : DeviceAttrs) (initial : Campaign2.State) (h : List Receipt)
    (current : Campaign2.State) : Prop :=
  CoreInput attrs initial current ∧ PortOrigin attrs initial h (current.device.map Device.incomingPort)

def History (attrs : DeviceAttrs) (initial : Campaign2.State) (h : List Receipt) : Prop :=
  ∀ r∈h,r.kind=.keyStage → At attrs initial h r.before.wg

def Fields (attrs : DeviceAttrs) (before after : Device) : Prop :=
  after.ifname=before.ifname ∧ after.ifindex=before.ifindex ∧
  after.fwmark=attrs.fwmark.getD before.fwmark ∧
  after.staticIdentity=before.staticIdentity ∧ after.deviceUpdateGen=before.deviceUpdateGen+1

end Leanux.Proofs.WG.Config.RequestOrder.KeyHeader
