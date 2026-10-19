import Leanux.Proofs.WG.Config.RequestOrderModel
import Leanux.Proofs.WG.Queues.JointDevice
import Leanux.Proofs.Logged.NativeCapture
import Leanux.Proofs.WG.Campaign2.Bridge

/-! Native source actions and receipt validity; execution state stays behind these bridge predicates. -/
set_option autoImplicit false

namespace Leanux.Proofs.WG.Config.RequestOrder
open Leanux Leanux.WG Leanux.Proofs.Logged
open Leanux.Proofs.WG.Configuration

def keyStage (attrs : DeviceAttrs) : WG.M Int :=
  deviceKeyWith (fun {_} a => a) pubkeyLookup peerPut peerRemove
    precomputeStaticStatic expireCurrentPeerKeypairs sendStagedPackets (pure 0) attrs

def action (attrs : DeviceAttrs) : Kind → WG.M Int
  | .updateEntry _ => do
    modifyDev fun d => {d with deviceUpdateGen := d.deviceUpdateGen + 1}
    pure 0
  | .clearSource pid => do clearPeerEndpointSrc pid; pure 0
  | .port p => setPort p
  | .replacement => do peerRemoveAll; pure 0
  | .keyStage => keyStage attrs
  | .peer p => setPeerCmd p

def receipt (kind : Kind) (r : WGRunWitness Int) : Receipt :=
  ⟨kind, r.value, Campaign2.snapshot r.before r.ambientBefore,
    Campaign2.snapshot r.after r.ambientAfter⟩

def Valid (attrs : DeviceAttrs) (r : Receipt) : Prop :=
  ∃ native : WGRunWitness Int, native.Valid (action attrs r.kind) ∧ receipt r.kind native = r

def ValidHistory (attrs : DeviceAttrs) (h : List Receipt) : Prop :=
  ∀ r ∈ h, Valid attrs r

abbrev HistorySpec {α : Type} (P S : List Receipt → Prop)
    (a : WGPrefix Receipt α) (Q : α → List Receipt → Prop) : Prop :=
  StatePrefixEnsures (fun h _ _ => P h) S a (fun x h _ _ => Q x h)

def Finished {α : Type} (L : Language α)
    (result : Except Stop ((α × WGWorld) × Ambient)) (added : List Receipt) : Prop :=
  match result with | .error _ => True | .ok (out,_) => L.normal out.1 added

def Conforms {α : Type} (a : WGPrefix Receipt α) (L : Language α) : Prop :=
  ∀ w ambient h, ∃ added, (runWGPrefix a w ambient h).2 = h ++ added ∧
    L.prefixes added ∧ Finished L (runWGPrefix a w ambient h).1 added

def PreludePost (attrs : DeviceAttrs) (initial : WGWorld) (a : Ambient)
    (h : List Receipt) (w : WGWorld) : Prop :=
  (h = [] ∧ w = initial) ∨ Begun attrs (Campaign2.snapshot initial a).wg h

end Leanux.Proofs.WG.Config.RequestOrder
